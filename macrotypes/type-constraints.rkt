#lang racket/base

(provide add-constraints
         add-constraints/var?
         add-constraints/variance/var?
         lookup
         lookup-Xs/keep-unsolved
         inst-type
         inst-type/orig
         inst-type/cs
         inst-types/cs
         inst-type/cs/orig
         inst-types/cs/orig
         )

(require syntax/parse
         syntax/stx
         syntax/id-table
         syntax/id-set
         (for-meta -1 "typecheck.rkt")
         "stx-utils.rkt"
         anaphoric
         )

;; add-constraints :
;; (Listof Id) (Listof (List Id Type)) (Stx-Listof (Stx-List Stx Stx)) -> (Listof (List Id Type))
;; Adds a new set of constaints to a substituion, using the type
;; unification algorithm for local type inference.
(define (add-constraints Xs substs new-cs [orig-cs new-cs])
  (define Xs* (stx->list Xs))
  (define (X? X)
    (member X Xs* free-identifier=?))
  (add-constraints/var? Xs* X? substs new-cs orig-cs))

(define (add-constraints/var? Xs* var? substs new-cs [orig-cs new-cs])
  (define Xs (stx->list Xs*))
  (define Ys (stx-map stx-car substs))
  (define-syntax-class var
    [pattern x:id #:when (var? #'x)])
  (syntax-parse new-cs
    [() substs]
    [([a:var b] . rst)
     (cond
       [(member #'a Ys free-identifier=?)
        ;; There are two cases.
        ;; Either #'a already maps to #'b or an equivalent type,
        ;; or #'a already maps to a type that conflicts with #'b.
        ;; In either case, whatever #'a maps to must be equivalent
        ;; to #'b, so add that to the constraints.
        (add-constraints/var?
         Xs
         var?
         substs
         (cons (list (lookup #'a substs) #'b)
               #'rst)
         orig-cs)]
       [(and (identifier? #'b) (var? #'b) (free-identifier=? #'a #'b))
        ;; #'a and #'b are equal, drop this constraint
        (add-constraints/var? Xs var? substs #'rst orig-cs)]
       [else
        (define entry (occurs-check (list #'a #'b) orig-cs))
        (add-constraints/var?
         Xs
         var?
         ;; Add the mapping #'a -> #'b to the substitution,
         (add-substitution-entry entry substs)
         ;; and substitute that in each of the constraints.
         (cs-substitute-entry entry #'rst)
         orig-cs)])]
    [([a b:var] . rst)
     (add-constraints/var? Xs
                           var?
                           substs
                           #'([b a] . rst)
                           orig-cs)]
    [([a b] . rst)
     ;; If #'a and #'b are base types, check that they're equal.
     ;; Identifers not within Xs count as base types.
     ;; If #'a and #'b are constructed types, check that the
     ;; constructors are the same, add the sub-constraints, and
     ;; recur.
     ;; Otherwise, raise an error.
     (cond
       [(identifier? #'a)
        ;; #'a is an identifier, but not a var, so it is considered
        ;; a base type. We also know #'b is not a var, so #'b has
        ;; to be the same "identifier base type" as #'a.
        (unless (and (identifier? #'b) (free-identifier=? #'a #'b))
          (type-error #:src (get-orig #'b)
                      #:msg (format "couldn't unify ~~a and ~~a\n  expected: ~a\n  given: ~a"
                                    (string-join (map type->str (stx-map stx-car orig-cs)) ", ")
                                    (string-join (map type->str (stx-map stx-cadr orig-cs)) ", "))
                      #'a #'b))
        (add-constraints/var? Xs
                              var?
                              substs
                              #'rst
                              orig-cs)]
       [else
        (syntax-parse #'[a b]
          [_
           #:when (typecheck? #'a #'b)
           (add-constraints/var? Xs
                                 var?
                                 substs
                                 #'rst
                                 orig-cs)]
          [((~Any tycons1 τ1 ...) (~Any tycons2 τ2 ...))
           #:when (typecheck? #'tycons1 #'tycons2)
           #:when (stx-length=? #'[τ1 ...] #'[τ2 ...])
           (add-constraints/var? Xs
                                 var?
                                 substs
                                 #'((τ1 τ2) ... . rst)
                                 orig-cs)]
          [else
           (type-error #:src (get-orig #'b)
                       #:msg (format "couldn't unify ~~a and ~~a\n  expected: ~a\n  given: ~a"
                                     (string-join (map type->str (stx-map stx-car orig-cs)) ", ")
                                     (string-join (map type->str (stx-map stx-cadr orig-cs)) ", "))
                       #'a #'b)])])]))

;; Variance Type Type -> Boolean
(define (typecheck?/variance variance a b)
  (cond
    [(variance-covariant? variance) (typecheck? b a)]
    [(variance-contravariant? variance) (typecheck? b a)]
    ;; invariant and irrelevant
    ;; TODO: use a parameter to indicate whether we're making a co/contravariant typecheck?, or whether it's an invariant typecheck? (to avoid an exponential cost by branching at each step)
    [else (and (typecheck? a b)
               (typecheck? b a))]))

(define ((stx->list->c l-c) v) (and (stx-list? v) (l-c (stx->list v))))
(define (to-datum v) (syntax->datum (datum->syntax #f v)))
(define ((stx->datum->c d-c) v) (d-c (to-datum v)))
(provide/contract
 [add-constraints/variance
  (->* {(flat-named-contract
         "(stx-listof identifier?)"
         (stx->list->c (listof identifier?)))
        (free-id-table/c identifier? variance? #:immutable #t)
        (flat-named-contract
         "(stx-listof (stx-list/c type? type? variance?))"
         (stx->list->c (listof (stx->list->c (list/c type? type? (stx->datum->c variance?))))))}
       {(free-id-table/c identifier? type? #:immutable #t)}
       (free-id-table/c identifier? type? #:immutable #t))])
(define (add-constraints/variance Xs X→variance ab+variance*
                                  [old-solution (make-immutable-free-id-table)])
  (define Xset (immutable-free-id-set (stx->list Xs)))
  (define X? (curry free-id-set-member? Xset))
  (add-constraints/variance/var? X? X→variance ab+variance* old-solution))

;; (-> Any Boolean : (∩ X Id))
;; (ImmutableFreeIdTable (∩ X Id) Variance)
;; (Stx-Listof (Stx-List Type Type Variance)) ;; caller-τ callee-τ variance
;; (ImmutableFreeIdTable (∩ X Id) Type)
;; ->
;; (ImmutableFreeIdTable (∩ X Id) Type)
(define (add-constraints/variance/var? X? X→variance ab+variance* old-solution)
  (define-syntax-class X
    (pattern v:id
             #:when (X? #'v)
             #:attr variance (or (free-id-table-ref X→variance #'a #f)
                                 invariant)))
  (define (do-error)
    (define/with-syntax [(a b _) . _] ab+variance*)
    (type-error #:src (get-orig #'b)
                #:msg "couldn't unify ~~a and ~~a"
                #'a #'b))
  (define (continue new-ab* new-solution)
    (add-constraints/variance/var? X? X→variance new-ab* new-solution))
  (syntax-parse ab+variance*
    [() old-solution]
    [((caller-τ callee-τ:X a/b-variance) . rest)
     ;; If a substitution was already inferred for X, check if #'a is compatible
     (awhen (free-id-table-ref old-solution #'callee-τ #f)
       (define v (variance-join (attribute callee-τ.variance)
                                (syntax->datum #'a/b-variance)))
       (unless (typecheck?/variance v it #'caller-τ)
         (do-error)))
     (continue #'rest
               (free-id-table-set old-solution #'callee-τ #'caller-τ))]
    [(((~Any caller-tycons caller-τᵢ ...)
       (~Any callee-tycons callee-τᵢ ...)
       a/b-variance)
      . rest)
     ;; varianceᵢ is composed with the a/b-variance. The main case of
     ;; composition is to flip the former if the latter is contravariant,
     ;; similarly to the xor logic operator.
     #:with (varianceᵢ ...)
     (for/list ([v (in-list (or (get-arg-variances #'caller-tycons)
                                (get-arg-variances #'callee-tycons)))])
       (variance-compose (syntax->datum #'a/b-variance) v))
     #:when (= (stx-length #'(caller-τᵢ ...)) (stx-length #'(callee-τᵢ ...)))
     #:when (= (stx-length #'(caller-τᵢ ...)) (stx-length #'(varianceᵢ ...)))
     (continue #'((caller-τᵢ callee-τᵢ varianceᵢ) ... . rest)
               old-solution)]
    [((caller-τ callee-τ a/b-variance) . rest)
     #:when (typecheck?/variance (syntax->datum #'a/b-variance)
                                 #'caller-τ
                                 #'callee-τ)
     (continue #'rest old-solution)]
    [(_ . rest)
     (do-error)]))

(define (datum=? x y)
  (equal? (syntax->datum x) (syntax->datum y)))

;; add-substitution-entry : (List Id Type) (Listof (List Id Type)) -> (Listof (List Id Type))
;; Adds the mapping a -> b to the substitution and substitutes for it in the other entries
(define (add-substitution-entry entry substs)
  (match-define (list a b) entry)
  (cons entry
        (for/list ([subst (in-list substs)])
          (list (first subst)
                (inst-type/orig (list b) (list a) (second subst) datum=?)))))

;; cs-substitute-entry : (List Id Type) (Stx-Listof (Stx-List Stx Stx)) -> (Listof (List Stx Stx))
;; substitute a -> b in each of the constraints
(define (cs-substitute-entry entry cs)
  (match-define (list a b) entry)
  (for/list ([c (in-list (stx->list cs))])
    (list (inst-type/orig (list b) (list a) (stx-car c) datum=?)
          (inst-type/orig (list b) (list a) (stx-cadr c) datum=?))))

;; occurs-check : (List Id Type) (Stx-Listof (Stx-List Stx Stx)) -> (List Id Type)
(define (occurs-check entry orig-cs)
  (match-define (list a b) entry)
  (cond [(stx-contains-id? b a)
         (type-error #:src (get-orig b)
                     #:msg (format (string-append
                                    "couldn't unify ~~a and ~~a because one contains the other\n"
                                    "  expected: ~a\n"
                                    "  given: ~a")
                                   (string-join (map type->str (stx-map stx-car orig-cs)) ", ")
                                   (string-join (map type->str (stx-map stx-cadr orig-cs)) ", "))
                     a b)]
        [else entry]))

(define (lookup x substs)
  (syntax-parse substs
    [((y:id τ) . rst)
     #:when (free-identifier=? #'y x)
     #'τ]
    [(_ . rst) (lookup x #'rst)]
    [() #f]))

;; lookup-Xs/keep-unsolved : (Stx-Listof Id) Constraints -> (Listof Type-Stx)
;; looks up each X in the constraints, returning the X if it's unconstrained
(define (lookup-Xs/keep-unsolved Xs cs)
  (for/list ([X (in-stx-list Xs)])
    (or (lookup X cs) X)))

;; instantiate polymorphic types
;; inst-type : (Listof Type) (Listof Id) Type -> Type
;; Instantiates ty with the tys-solved substituted for the Xs, where the ith
;; identifier in Xs is associated with the ith type in tys-solved
(define (inst-type tys-solved Xs ty)
  (substs tys-solved Xs ty))
;; inst-type/orig : (Listof Type) (Listof Id) Type (Id Id -> Bool) -> Type
;; like inst-type, but also substitutes within the orig property
(define (inst-type/orig tys-solved Xs ty [var=? free-identifier=?])
  (add-orig (inst-type tys-solved Xs ty)
            (substs (stx-map get-orig tys-solved) Xs (get-orig ty) var=?)))

;; inst-type/cs : (Stx-Listof Id) Constraints Type-Stx -> Type-Stx
;; Instantiates ty, substituting each identifier in Xs with its mapping in cs.
(define (inst-type/cs Xs cs ty)
  (define tys-solved (lookup-Xs/keep-unsolved Xs cs))
  (inst-type tys-solved Xs ty))
;; inst-types/cs : (Stx-Listof Id) Constraints (Stx-Listof Type-Stx) -> (Listof Type-Stx)
;; the plural version of inst-type/cs
(define (inst-types/cs Xs cs tys)
  (stx-map (lambda (t) (inst-type/cs Xs cs t)) tys))

;; inst-type/cs/orig :
;; (Stx-Listof Id) Constraints Type-Stx (Id Id -> Bool) -> Type-Stx
;; like inst-type/cs, but also substitutes within the orig property
(define (inst-type/cs/orig Xs cs ty [var=? free-identifier=?])
  (define tys-solved (lookup-Xs/keep-unsolved Xs cs))
  (inst-type/orig tys-solved Xs ty var=?))
;; inst-type/cs/orig/variance
;; (ImmutableFreeIdTable X Type) Type -> Type
(define (inst-type/cs/orig/variance solution ty [var=? free-identifier=?])
  (define solution-as-list (free-id-table-map solution cons))
  (inst-type/orig (map cdr solution-as-list)
                  (map car solution-as-list)
                  ty
                  var=?))
;; inst-types/cs/orig :
;; (Stx-Listof Id) Constraints (Stx-Listof Type-Stx) (Id Id -> Bool) -> (Listof Type-Stx)
;; the plural version of inst-type/cs/orig
(define (inst-types/cs/orig Xs cs tys [var=? free-identifier=?])
  (stx-map (lambda (t) (inst-type/cs/orig Xs cs t var=?)) tys))

