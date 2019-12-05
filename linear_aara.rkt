#|
My whirlwind "tour" of making an executable semantic(s) model in Redex took a
lot longer than expected, and I didn't get to follow-up on `share`, or other
type-judgment forms for sum-types, etc..., but this definitely gets us headed
somewhere interesting.


Caveats that I only learned after the fact:

- Sadly, we can't use (quickcheck-inspired) redex-check to generate
  #:satisfying typed-inference terms when side-conditions come into play.
  Something I may rewrite to include more metafunctions then, instead.

- William Bowman's blog post/tutorial on Redex is extremely helpful, especially
  in dealing with how to debug the inferencer.
|#

#lang racket

(require redex
         racket/match
         racket/list
         racket/contract
         racket/bool)

(provide (all-defined-out))

;; Define the language's expressions, operators, type environments, and
;; a call-by-value evaluation context as non-terminals.
(define-language LinearAARAL
  (e ::= x c n l one nat
     (+ e e)
     (cons e e)
     ()
     (e e)
     (tick t)
     (tick t in e)
     (let ([y e]) e)
     (case e [nil = e] [(cons x x) = e])
     (o e)
     (nil τ))
  (o ::= hd tl)
  (pot ::= (p → q))
  (one ::= triv ⟨⟩)
  (t ::= (side-condition n_1 (rational? (term n_1))))
  (p q r ::= (side-condition
              n_1 (and (rational? (term n_1)) (>= (term n_1) 0))))

  (n ::= number)
  (nat ::= natural)
  (l ::= (λ (x : τ) e))
  (A B ::= [τ p])
  (T τ ::= Unit Nat (A → A) (τ * τ) (List A) A)
  (x y z ::= variable-not-otherwise-mentioned)
  (Γ ::= • (Γ (x : τ) ... (e : τ) ...))
  (Venv ::= V (V x))
  (v ::= n l (cons v v) ⟨⟩ [])
  (E ::= hole
     (E e ...) (v ... E e ...) (E e) (v E)
     (λ (x : τ) E)
     (cons v ... E e ...)
     (hd E)
     (tl E)
     (let ([x E]) e) (let ([x v]) E)
     (case E [nil = e] [(cons x x) = e]))
  ;; binding-forms around shadowing/capture-avoiding subst
  #:binding-forms
  (λ (x : τ) e #:refers-to x)
  (let ([y e]) e) #:refers-to y)

(default-language LinearAARAL)

;; A basic reduction relation for small-step reductions, e.g. function subst,
;; etc...
(define ->
  (reduction-relation
   LinearAARAL
   #:domain e
   #:codomain e
   (--> ((λ (x : τ) e_1) e_2) (substitute e_1 x e_2)
        "β→")
   (--> (hd (cons e_1 e_2)) e_1
        "hd")
   (--> (tl (cons e_1 e_2)) e_2
        "tl")
   (--> (let ([x e_1]) e_2) (substitute e_2 x e_1)
        "let")
   (--> (+ q_1 q_2) ,(+ (term q_1) (term q_2))
        "plus")
   ))

;; Redex exposes the function compatible-closure-context for computing common
;; contexts;
;; The `->ocaml` reduction is call-by-value. With `compatible-clousre`, you can
;; define full-reductions for call-by-push-value, etc...
(define ->* (compatible-closure -> LinearAARAL e))
(define ->ocaml (compatible-closure -> LinearAARAL E))

;; Metafunctions allow us to compute with terms, i.e returns only certain
;; components of a term for binding or computing a value in Racket for a
;; type-check.
(define-metafunction LinearAARAL
  normalize : e -> e
  [(normalize e)
   ,(car (apply-reduction-relation* ->* (term e)))])

(define-metafunction LinearAARAL
  abs-env : A -> A
  [(abs-env [τ q])
   [τ 0]])

(define-metafunction LinearAARAL
  env-set : Γ -> Γ
  [(env-set ((• (x : τ) ... (x_n : τ_n)) (x_r : τ_r)))
   (• (x : τ) ... (x_n : τ_n) (x_r : τ_r))]
  [(env-set ((• (x : τ) ... (x_n : τ_n)) (x_r : τ_r) ... (x_k : τ_k)))
   (• (x : τ) ... (x_n : τ_n) (x_r : τ_r) ... (x_k : t_k))]
  [(env-set (• (x : τ) ... (x_n : τ_n)))
   (• (x : τ) ... (x_n : τ_n))])

(define-metafunction LinearAARAL
  unique-env : Γ -> Γ
  [(unique-env (•)) •]
  [(unique-env (• (x : τ)))
   (• (x : τ))]
  [(unique-env (• (x : τ) (x_1 : τ_1) ... (x : τ) (x_2 : τ_2) ...))
   (• (x : τ) (x_1 : τ_1) ... (x_2 : τ_2) ...)]
  [(unique-env (• (x : τ) (x_1 : τ_1) ...))
   (unique-env (• (x_1 : τ_1) ...))])

(define-metafunction LinearAARAL
  lookup : Γ x -> τ or #f
  [(lookup • x)
   #f]
  [(lookup (• (x : τ)) x)
   τ]
  [(lookup (• (x : τ) (x_1 : τ_1) ...) x_2)
   (lookup (• (x_1 : τ_1) ...) x_2)])

(define-metafunction LinearAARAL
  lists-fn : T -> [τ q]
  [(lists-fn (List [τ q]))
   [τ q]]
  [(lists-fn [(List [τ q]) p])
   [τ q]]
  [(lists-fn [τ q])
   [τ q]
   ]
  [(lists-fn τ)
   [τ 0]])

;; An equivalence judgment-form
(define-judgment-form LinearAARAL
  #:contract (≡ e e)
  #:mode (≡ I I)
  [(where (e e) ((normalize e_1) (normalize e_2)))
   ----------- "β"
   (≡ e_1 e_2)]

  [(≡ e_1 (e_2 x))
   --------------- "η₁"
   (≡ (λ (x : τ) e_1) e_2)]

  [(≡ (e_2 x) e_1)
   ------------------------ "η₂"
   (≡ e_2 (λ (x : τ) e_1))])

(define-judgment-form LinearAARAL
  #:contract (⇓ Venv ⊢ e v q)
  #:mode (⇓ I I I I I)

  [--------------------"E:Unit"
   (⇓ V ⊢ triv ⟨⟩ 0)]

  [--------------------"E:Cons"
   (⇓ V ⊢ (cons x_1 x_2) (cons v v) 0)]

  ;;; ... To Be Continued
  )


;; Main Static Semantics and Type-Inferencing
(define-judgment-form LinearAARAL
  #:contract (type-infer Γ pot ⊢ e : τ)
  #:mode (type-infer I I I I I O)

  [-----------------------------------------"L:Var"
   (type-infer (Γ (x : τ)) (q → p) ⊢ x : τ)]



  ;; helpers for now; TODO: figure out right ... pattern and lookup meta-fn
  [-----------------------------------------"L:Var2a"
   (type-infer (Γ (x : τ_1) (y : τ_2)) (q → p) ⊢ y : τ_2)]

  [-----------------------------------------"L:Var2b"
   (type-infer (Γ (x : τ_1) (y : τ_2)) (q → p) ⊢ x : τ_1)]
  ;;

  [
   -----------------------------------------"L:Nat"
   (type-infer Γ (q → p) ⊢ n : Nat)]


  [----------------------------------------- "L:Unit"
   (type-infer • (q → q) ⊢ triv : Unit)]


  [(where [τ q] A)
   -----------------------------------------"L:App"
   (type-infer (Γ (e_1 : (A → B)) (e_2 : τ))
               (q → q_1)
               ⊢ (e_1 e_2) : B)]


  [(where [τ p] A)
   (type-infer (Γ (x : (abs-env A))) (p → q) ⊢ e : [τ q])
   ------------------------------------------------------- "L:Fun"
   (type-infer Γ (r → q) ⊢ (λ (x : A) e) : [τ q])]


  [
   ---------------------------------------------------- "L:Nil"
   (type-infer • (p → q) ⊢ (nil τ) : τ)]


  [(side-condition ,(= (term q) (+ (term q_1) (term t))))
   (side-condition ,(= (- (term q) (term t)) (term q_1)))
   (type-infer (• (e : τ)) (q → q_1) ⊢ e : τ)
   -------------------------------------------------------"L:Tick"
   (type-infer (• (e : τ)) (q → q_1) ⊢ (tick t in e) : τ)]


  [(side-condition ,(>= (term q) 0))
   (side-condition ,(= (term t) (term q)))
   --------------------------------------------- "L:Tick≥0"
   (type-infer • (q → 0) ⊢ (tick t) : Unit)]


  [(side-condition ,(< (term t) 0))
   (side-condition ,(= (abs (term t)) (term q)))
   --------------------------------------------- "L:Tick<0"
   (type-infer • (0 → q) ⊢ (tick t) : Unit)]

  [(where [τ p] (lists-fn T))
   (type-infer Γ (q → p) ⊢ e_1 : τ)
   (type-infer (Γ (e_2 : T) (x : τ))
               (p → q_1) ⊢ e_2 : T)
   ---------------------------------------------------"L:Let"
   (type-infer (Γ (e_2 : T)) (q → q_1)
               ⊢ (let ([x e_1]) e_2) : T)]


  [(where [τ p] (lists-fn T))
   (where r, (- (term q) (term p)))
   (type-infer (Γ (e_1 : τ)) (q → r) ⊢ e_1 : τ)
   (type-infer (Γ (e_2 : T)) (r → q_1)
               ⊢ e_2 : T)
   ----------------------------------------------"L:Cons"
   (type-infer (Γ (e_2 : T)) (q → q_1)
               ⊢ (cons e_1 e_2) : T)]


  [(where [τ p] (lists-fn T))
   (where r ,(+ (term q) (term p)))
   (type-infer Γ (q → q_1) ⊢ e_0 : τ_1)
   (type-infer (unique-env (env-set (Γ (x_1 : τ) (x_2 : T))))
               (r → q_1) ⊢ e_1 : τ_1)
   --------------------------------------------------------------------- "L:MatL"
   (type-infer (Γ (x : T)) (q → q_1)
               ⊢ (case x [nil = e_0] [(cons x_1 x_2) = e_1]) : τ_1)]


  [(type-infer Γ (q → q_1) ⊢ e : τ_1)
   --------------------------------------------- "L:Weak"
   (type-infer (Γ (x : τ)) (q → q_1) ⊢ e : τ_1)]


  ;; TODO: Think on how to handle "L: Relax"
  )

(printf "tick -> ")
(judgment-holds (type-infer (• (x : Nat)) (8 → 4) ⊢ (tick 4 in x) : τ) τ)

(printf "tick -> ")
(judgment-holds (type-infer • (4 → 0) ⊢ (tick 4) : τ) τ)

(printf "tick -> ")
(judgment-holds (type-infer • (0 → 4) ⊢ (tick -4) : τ) τ)

(printf "unit -> ")
(judgment-holds (type-infer • (0 → 0) ⊢ triv : τ) τ)

(printf "nil -> ")
(judgment-holds (type-infer • (0 → 0) ⊢ (nil (List [Nat 2])) : τ) τ)

(printf "var -> ")
(judgment-holds
 (type-infer (• (x : (List [Nat 3]))) (0 → 0) ⊢ x : τ) τ)

(printf "cons -> ")
(judgment-holds (type-infer (• (y : (List [Nat 4]))) (8 → 0) ⊢ (cons x y) : τ) τ)


(printf "fun -> ")
(judgment-holds (type-infer • (0 → 0) ⊢ (λ (x : [(List [Nat 4]) 5]) x) : τ)
                τ)

(printf "let -> ")
(judgment-holds (type-infer (• (e : Unit)) (0 → 0) ⊢ (let ([y triv]) e) : τ) τ)

(printf "case -> ")
(judgment-holds (type-infer (• (x : (List [Nat 4]))) (0 → 0)
                            ⊢ (case x
                                [nil = (nil (List [Nat 4]))]
                                [(cons x_1 x_2) = x_2]) : τ) τ)
(build-derivations (type-infer (• (x : (List [Nat 4]))) (0 → 0)
                               ⊢ (case x
                                   [nil = (nil (List [Nat 4]))]
                                   [(cons x_1 x_2) = x_2]) : τ))


;; TESTING

(test-equal (judgment-holds
             (≡ (λ (x : Nat) ((λ (x : Nat) x) 5))
                (λ (x : Nat) 5))) #t)

(test-equal (judgment-holds
             (≡ (f 5)
                (λ (x : Nat) ((f 5) x)))) #t)


(define eg1 (term (λ (n : Nat) n)))
(test-equal (redex-match? LinearAARAL e eg1) #t)
(define eg2 (term (tick 9)))
(test-equal (redex-match? LinearAARAL e eg2) #t)
(test-equal (redex-match? LinearAARAL e (term [(tick 9)])) #f)


(test-equal (redex-match? LinearAARAL e (term (hd (cons (cons 2 3) 4)))) #t)

(test-equal (alpha-equivalent? (term (λ (x : Nat) e))  (term (λ (x : Nat) e))) #t)
(test-equal (alpha-equivalent? (term (λ (x : Nat) x))  (term (λ (y : Nat) y))) #t)
(test-equal (alpha-equivalent? (term (λ (x : Nat) y))  (term (λ (y : Nat) y))) #f)

(redex-check
 LinearAARAL
 v
 (redex-match? LinearAARAL e (term v))
 #:attempts 1000)

(define-term id
  (λ (x : [(List [Nat 2]) 0]) x))

(generate-term LinearAARAL e 10)

(define-term dumb-id
  (λ (l : [(List [Nat 2]) 0])
    (case l
      [nil = (nil [(List [Nat 2]) 0])]
      [(cons x xs) = (tick 2 in (let ([ys (id xs)])
                                  (cons x ys)))])))

(test-equal (redex-match? LinearAARAL e (term dumb-id)) #t)

(println "type id->")
(judgment-holds (type-infer
                 • (0 → 0) ⊢
                 (λ (l : [(List [Nat 2]) 0])
                   (case l
                     [nil = (nil [(List [Nat 2]) 0])]
                     [(cons x xs) = xs])) : τ) τ)

;; (build-derivations (type-infer
;;                     • (0 → 0) ⊢
;;                     (λ (l : [(List [Nat 2]) 0])
;;                       (case l
;;                         [nil = (nil [(List [Nat 2]) 0])]
;;                         [(cons x xs) = xs])) : τ))


;; REDUCTIONS
(apply-reduction-relation* ->* (term (λ (x : Nat) (hd (cons (cons 9 2) 100)))))
(apply-reduction-relation* ->ocaml (term (λ (x : Nat) (let ([y 10]) y))))
(apply-reduction-relation* ->* (term (λ (x : Nat) (let ([y 10]) y))))
(apply-reduction-relation* ->* (term (λ (x : Nat) (let ([y 10]) (cons x y)))))
(apply-reduction-relation ->ocaml (term (let ([y 10]) y)))

(apply-reduction-relation ->ocaml (term (hd (cons 1 2))))
(apply-reduction-relation* ->ocaml (term (hd (cons (hd (cons 1 2)) 9))))
(apply-reduction-relation* ->ocaml (term (let ([y (hd (cons 44 2))]) y)))

;; (traces ->ocaml (term ((λ (x : Nat) (let ([y 10]) (+ x y))) 12)))

(test-results)

;; (render-language LinearAARAL)
;;(render-judgment-form type-infer)

