#lang slideshow/widescreen

(require "linear_aara.rkt"
         "helpers.rkt"
         redex
         slideshow/pict
         slideshow/code
         slideshow/text)

(define footnote-color "red")

(define (supert s)
  (colorize
   (text s `(superscript . ,(current-main-font)) (current-font-size))
   footnote-color))


(slide
 #:title "A Wip, Executable Semantic Model for Linear AARA"
 'next!
 (scale (colorize (para #:align 'center (bold "And a Showcase of Redex")) "red") 0.9)
 'next!
 'alts
 (list (list (bitmap "prac.jpg"))
       (list (scale (bitmap "runyour.png") 0.5))))

(slide
 #:title "Redex: Design Programming Languages as Executable Semantics"
 'alts
 (list (list
        (colorize (scale (t "Our language expressions, operations, type envs, and more") 0.8) "red")
        (scale (pict->pre-render-pict (render-language LinearAARAL)) 1.1))

       (list (scale (bitmap "relation.png") 0.5)))
)

(slide
 #:title "Let's build a derivation tree for type-checking our `id` fn"
 'alts
 (list (list (scale
              (code (define-term dumb-id
                      (λ (l : [(List [Nat 2]) 0])
                        (case l
                          [nil = (nil [(List [Nat 2]) 0])]
                          [(cons x xs) = (tick 2 in (let ([ys (id xs)])
                                                      (cons x ys)))])))) 0.8))
       (list (scale (code ((list
                            (derivation
                             '(type-infer
                               •
                               (0 → 0)
                               ⊢
                               (λ (l : ((List (Nat 2)) 0))
                                 (case l (nil = (nil ((List (Nat 2)) 0))) ((cons x xs) = xs)))
                               :
                               ((List (Nat 2)) 0))
                             "L:Fun"
                             (list
                              (derivation
                               '(type-infer
                                 (• (l«77» : ((List (Nat 2)) 0)))
                                 (0 → 0)
                                 ⊢
                                 (case l«77» (nil = (nil ((List (Nat 2)) 0))) ((cons x xs) = xs))
                                 :
                                 ((List (Nat 2)) 0))
                               "L:MatL"
                               (list
                                (derivation
                                 '(type-infer • (0 → 0) ⊢ (nil ((List (Nat 2)) 0)) : ((List (Nat 2)) 0))
                                 "L:Nil"
                                 '())
                                (derivation
                                 '(type-infer
                                   (• (xs : ((List (Nat 2)) 0)))
                                   (2 → 0)
                                   ⊢
                                   xs
                                   :
                                   ((List (Nat 2)) 0))
                                 "L:Var"
                                 '())))))))) 0.4))

       (list (scale (bitmap "derive.png") 0.59))))

(slide
 #:title "Our Static Semantics for Linear AARA (Lists)"
 'alts
 (list (list (scale (bitmap "statics.png") 0.7))
       (list (scale (code
                     [(where [τ p] (lists-fn T))
                      (where r, (- (term q) (term p)))
                      (type-infer (Γ (e_1 : τ)) (q → r) ⊢ e_1 : τ)
                      (type-infer (Γ (e_2 : T)) (r → q_1)
                                  ⊢ e_2 : T)
                      ----------------------------------------------"L:Cons"
                      (type-infer (Γ (e_2 : T)) (q → q_1)
                                  ⊢ (cons e_1 e_2) : T)]
) 0.9))))

(slide
 #:title "Do (Typing) Judgments Hold?"
 'alts
 (list (list (scale (code
                     (printf "tick -> ")
                     (judgment-holds (type-infer (• (x : Nat)) (8 → 4) ⊢ (tick 4 in x) : τ) τ)


                     (printf "tick -> ")
                     (judgment-holds (type-infer • (4 → 0) ⊢ (tick 4) : τ) τ)


                     (printf "tick -> ")
                     (judgment-holds (type-infer • (0 → 4) ⊢ (tick -4) : τ) τ)


                     (printf "unit -> ")
                     (judgment-holds (type-infer • (0 → 0) ⊢ triv : τ) τ)


                     (printf "cons -> ")
                     (judgment-holds (type-infer (• (y : (List [Nat 4]))) (8 → 0) ⊢ (cons x y) : τ) τ)


                     (printf "fun -> ")
                     (judgment-holds (type-infer • (0 → 0) ⊢ (λ (x : [(List [Nat 4]) 5]) x) : τ) τ)


                     (printf "let -> ")
                     (judgment-holds (type-infer (• (e : Unit)) (0 → 0) ⊢ (let ([y triv]) e) : τ) τ)


                     (printf "case -> ")
                     (judgment-holds (type-infer (• (x : (List [Nat 4]))) (0 → 0)
                                                 ⊢ (case x
                                                     [nil = (nil (List [Nat 4]))]
                                                     [(cons x_1 x_2) = x_2]) : τ) τ)
                     ) 0.6))
       (list (scale (code
                     (printf "tick -> ")
                     (judgment-holds (type-infer (• (x : Nat)) (8 → 4) ⊢ (tick 4 in x) : τ) '(Nat))


                     (printf "tick -> ")
                     (judgment-holds (type-infer • (4 → 0) ⊢ (tick 4) : τ) '(Unit))


                     (printf "tick -> ")
                     (judgment-holds (type-infer • (0 → 4) ⊢ (tick -4) : τ) '(Unit))


                     (printf "unit -> ")
                     (judgment-holds (type-infer • (0 → 0) ⊢ triv : τ) '(Unit))


                     (printf "cons -> ")
                     (judgment-holds (type-infer (• (y : (List [Nat 4]))) (8 → 0) ⊢ (cons x y) : τ) '((List (Nat 4))))


                     (printf "fun -> ")
                     (judgment-holds (type-infer • (0 → 0) ⊢ (λ (x : [(List [Nat 4]) 5]) x) : τ) '(((List (Nat 4)) 0)))


                     (printf "let -> ")
                     (judgment-holds (type-infer (• (e : Unit)) (0 → 0) ⊢ (let ([y triv]) e) : τ) '(Unit))


                     (printf "case -> ")
                     (judgment-holds (type-infer (• (x : (List [Nat 4]))) (0 → 0)
                                                 ⊢ (case x
                                                     [nil = (nil (List [Nat 4]))]
                                                     [(cons x_1 x_2) = x_2]) : τ)  '((List (Nat 4))))
) 0.6))))

(slide
 #:title "Redex Has So Much More"
 (item "Testing is Crucial")
 'next
 (scale (code (redex-check
               LinearAARAL
               v
               (redex-match? LinearAARAL e (term v))
               #:attempts 1000)) 0.6)
 (scale (code (test-equal (redex-match? LinearAARAL e (term dumb-id)) #t)) 0.7)
 'next
 (item "Can easily model natural, small-step semantics, and programming paradigms like call-by-push-value")
 (item "Next up for our model: Share!, Sum, Products, and Recursive Types")
 )
