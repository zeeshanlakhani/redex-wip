#lang slideshow

(require slideshow/code
         redex)

(provide (all-defined-out))

(define (foreign-code str)
  (apply
   vl-append
   (current-code-line-sep)
   (map (lambda (str)
          (para #:fill? #t (tt str)))
        (string-split str "\n"))))

(define algol60-code foreign-code)

(define-syntax-rule (lang l)
  (vl-append
   (hbl-append (tt "#lang ") (code l))
   (blank (+ ((get-current-code-font-size))
             (current-code-line-sep)))))

(define (highlight-last . strs)
  (apply
   hbl-append
   (append
    (map (lambda (str) (t (string-append str " "))) (drop-right strs 1))
    (list (colorize (t (car (take-right strs 1))) "red")))))

(define (cite who what where when)
  (apply
   para
   (flatten
    (list who "." (map it (string-split what " ")) "." where "." when "."))))

(define (anonymous what where when)
  (apply
   para
   (flatten
    (list (map it (string-split what " ")) "." where "." when "."))))

(define (item-cite who what where when)
  (apply
   item
   (flatten
    (list who "." (map it (string-split what " ")) "." where "." when "."))))

(define (colorize-words str color)
  (map (lambda (str) (colorize (t str) color))
       (string-split str " ")))

(define (blue x) (colorize x "blue"))

(define (red x) (colorize x "red"))

(define (yellow x) (colorize x "yellow"))

(define (when-who-what when who what)
  (blue
   (apply
    para
    when
    ": "
    who
    ", "
    (map it (string-split what " ")))))

(define (with-rewriters t)
  (define rewrite-lookup
    (match-lambda
      [(list op id r v a cp)
       (list "" r "(" v ") = " a)]))
  (define set-rewrite
    (match-lambda
      [(list op id r1 v a r2 cp)
       (list "" r1 "[" v ":=" a "] = " r2)]))
  (define subset-rewrite
    (match-lambda
      [(list op id left right cp)
       (list "" left " ⊂ " right "")]))
  (define (turn which subscr)
    (hbl-append (text which (default-style) (default-font-size))
                (text subscr (cons 'subscript (default-style)) (default-font-size))
                (text " " (default-style) (default-font-size))))
  (with-compound-rewriters
   (['var-lookup rewrite-lookup]
    ['var-set set-rewrite]
    ['program-lookup rewrite-lookup]
    [':lookup rewrite-lookup]
    [':set set-rewrite]
    ['check-program
     (match-lambda
       [(list op id p Π cp)
        (list (turn "⊨" "prog") p " : " Π)])]
    ['check-blocks
     (match-lambda
       [(list op ip  Π p cp)
        (list "" Π (turn "⊢" "blocks") p)])]
    ['check-block
     (match-lambda
       [(list op id Π Γ ι cp)
        (list "" Π ";" Γ (turn "⊢" "blocks") ι)])]
    ['check-instr
     (match-lambda
       [(list op id Π Γ1 ι Γ2 cp)
        (list "" Π (turn "⊢" "instr") Γ1 "{" ι "}" Γ2)])]
    ['l-⊂ subset-rewrite]
    ['Γ-⊂ subset-rewrite]
    ['⊔
     (match-lambda
       [(list op id τ1 τ2 τ3 cp)
        (list "" τ1 "⊔" τ2 " = " τ3)])]
    ['dom
     (λ (lws)
       (define arg (list-ref lws 2))
       (list "dom(" arg ")"))])
   (t)))

(define (scale-to-fit/m p)
  (scale p (min (/ (- 1024 margin margin) (pict-width p))
                (/ (- 768 margin margin) (pict-height p)))))
