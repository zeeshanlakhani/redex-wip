#lang racket

(require redex/reduction-semantics
         racket/match
         racket/list
         racket/contract
         racket/bool)

;; TODO: Define share
(define-language LinearAARA
  (e ::= x c n l
     (+ q p)
     (cons e e)
     (e e)
     (tick q)
     (let ([y e]) e)
     (case e [nil = e] [(cons x x) = e])
     (share ([y (e e)] e))
     ⟨⟩)
  (c ::= nil)
  (p q ::= natural)
  (n ::= natural)
  (μ (x : τ) l)
  (l ::= (λ (x : τ) e))
  (τ ::= Unit Nat (τ → τ) (τ * τ) (List A))
  (A B ::= [τ q])
  (x y ::= variable-not-otherwise-mentioned)
  (Γ ::= • (Γ (x : τ ... (x : A))))
  (v ::= n l (cons v v) ⟨⟩ [])
  (E ::= hole
     (E e ...) (v ... E e ...) (E e) (v E)
     (λ (x : τ) E)
     (cons v ... E e ...)
     (hd E)
     (tl E)
     (let ([x E]) e) (let ([x v]) E)
     (case E [nil = e] [(cons x x) = e])
     (share ([x (E E)] e)))
  #:binding-forms
  (λ (x : τ) e #:refers-to x)
  (let ([y e]) e) #:refers-to y
  (share ([y (y_1 y_2)] e) #:refers-to y))

(default-language LinearAARA)

(define eg1 (term (λ (n : Nat) n)))
(test-equal (redex-match? LinearAARA e eg1) #t)
(define eg2 (term (tick 9)))
(test-equal (redex-match? LinearAARA e eg2) #t)
(test-equal (redex-match? LinearAARA e (term [(tick 9)])) #f)


(redex-match LinearAARA (in-hole E v) (term (hd (cons (cons (1 2)) 4))))
(redex-match LinearAARA (in-hole E e) (term (hd (cons (cons (1 2)) 4))))
(test-equal (redex-match? LinearAARA e (term (hd (cons (cons 2 3) 4)))) #t)

(test-equal (alpha-equivalent? (term (λ (x : Nat) e))  (term (λ (x : Nat) e))) #t)
(test-equal (alpha-equivalent? (term (λ (x : Nat) x))  (term (λ (y : Nat) y))) #t)
(test-equal (alpha-equivalent? (term (λ (x : Nat) y))  (term (λ (y : Nat) y))) #f)

(term (substitute (λ (y : Nat) (x e2)) x 5))

(define an-e1 (generate-term LinearAARA e 10))

;; (test-predicate (redex-match? LinearAARA e) (term (hd (cons (cons 1 2) 3))))
;; (test-predicate (redex-match? LinearAARA f) (term (hd (cons (cons 1 2) 3)))) ;; -> fails


;; random testing of syntactic properties.
(redex-check
 LinearAARA
 v
 (redex-match? LinearAARA e (term v))
 #:attempts 1000)

(define ->
  (reduction-relation
   LinearAARA
   #:domain e
   #:codomain e
   (--> (μ (x : τ) e) (substitute (μ (x : τ) e) x e)
        "μ")
   (--> ((λ (x : τ) e_1) e_2) (substitute e_1 x e_2)
        "β→")
   (--> (hd (cons e_1 e_2)) e_1
        "hd")
   (--> (tl (cons e_1 e_2)) e_2
        "tl")
   (--> (let ([x e_1]) e_2) (substitute e_2 x e_1)
        "let")
   (--> (+ q p) ,(+ (term q) (term p))
        "plus potential")
   ))


(define ->* (compatible-closure -> LinearAARA e))
(define ->ocaml (compatible-closure -> LinearAARA E))

(apply-reduction-relation* ->* (term (λ (x : Nat) (hd (cons (cons 9 2) 100)))))
(apply-reduction-relation* ->ocaml (term (λ (x : Nat) (let ([y 10]) y))))
(apply-reduction-relation* ->* (term (λ (x : Nat) (let ([y 10]) y))))
(apply-reduction-relation* ->* (term (λ (x : Nat) (let ([y 10]) (cons x y)))))
(apply-reduction-relation ->ocaml (term (let ([y 10]) y)))
(apply-reduction-relation ->ocaml (term (hd (cons 1 2))))
(apply-reduction-relation* ->ocaml (term (hd (cons (hd (cons 1 2)) 9))))
(apply-reduction-relation* ->ocaml (term (let ([y (hd (cons 44 2))]) y)))

(define-metafunction LinearAARA
  normalize : e -> e
  [(normalize e)
   ,(car (apply-reduction-relation* ->* (term e)))])

(define-judgment-form LinearAARA
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

(judgment-holds
 (≡ (λ (x : Nat) ((λ (x : Nat) x) 5))
    (λ (x : Nat) 5)))

(judgment-holds
 (≡ (f 5)
    (λ (x : Nat) ((f 5) x))))

(define-metafunction LinearAARA
  const-type : c -> A
  [(const-type nil) [(List A) 0]])

(define-judgment-form LinearAARA
  #:contract (type-infer Γ q ⊢ e : A)
  #:mode (type-infer I I I I I O)

  [--------------------------------------- "L:Var"
   (type-infer (Γ (x : τ)) 0 ⊢ x : [τ 0])]


  [--------------------------------- "L:Unit"
   (type-infer • 0 ⊢ ⟨⟩ : [Unit 0])]

  [
   ----------------------------------------------------------- "L:App"
   (type-infer (Γ (e_1 : A → B) (e_2 : A)) q ⊢ (e_1 e_2) : B)]


  [(where [τ 0] A)
   (where q ,(if (natural? (term q)) (term q) 0))
   (type-infer (Γ (x : [τ 0])) q ⊢ e : B)
   ------------------------------------------------ "L:Fun"
   (type-infer Γ 0 ⊢ (λ (x : A) e) : [(A → B), 0])]


  [
   ------------------------------------------ "L:Nil"
   (type-infer • 0 ⊢ nil : (const-type nil))]


  [(side-condition ,(>= (term q) 0))
   --------------------------------------- "L:Tick1"
   (type-infer • q ⊢ (tick q) : [Unit 0])]

  [(side-condition ,(< (term q) 0))
   --------------------------------------- "L:Tick2"
   (type-infer • 0 ⊢ (tick q) : [unit q])]

  [(type-infer Γ_1 q ⊢ e_1 : [τ p])
   (type-infer (Γ_2 (x : τ)) p ⊢ e_2 : B)
   ----------------------------------------- "L:Let"
   (type-infer (Γ_1 Γ_2) q ⊢ (let [x e_1] e_2) : B)]

  [
   --------------------------------------------- "L:Cons"
   (type-infer (Γ (x_1 : τ) (x_2 : (List A))) p
               ⊢ (cons x_1 x_2) : [(List A) 0])]


  [(type-infer Γ q ⊢ e_0 : B)
   (type-infer (Γ (x_1 : τ) (x_2 : (List [τ p]))) (+ q p) ⊢ e_1 : B)
   ----------------------------------------------------------------- "L:MatL"
   (type-infer (Γ (x : (List [τ p] ))) q
               ⊢ (case e [nil = e_0] [(cons x_1 x_2) = e_1]) : B)]

  [(type-infer Γ q ⊢ e : B)
   ----------------------------------------------------------------- "L:Weak"
   (type-infer (Γ (x : τ)) q ⊢ e : B)]

  [(where p ,(if (natural? (term p)) (term p) 0))
   (where q ,(if (natural? (term q)) (term q) 0))
   (where q_1 ,(if (natural? (term q_1)) (term q_1) 0))
   (side-condition ,(>= (term q) (term p)))
   (side-condition ,(>= (- (term q) (term q_1))
                        (- (term p) (term p_1))))
   (type-infer Γ p ⊢ e : [τ p_1])
   ----------------------------------------------------------------- "L:Relax"
   (type-infer Γ q ⊢ e : [τ q_1])]

  ;; ----------------------------------------------------------------- "T:Share"

  )

