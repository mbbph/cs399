;Testing Ground
;Run the program to see results
;'obs' still not working
#lang s-exp "racets-2.rkt"
(require racket/match)
(require syntax/parse/define)

(define my-pol
 (let-label l (lambda (x) (equal? x "Alice")) l))

(define my-facet1 (ref (fac my-pol #f #t)))
(define my-facet2 (ref (fac my-pol 0 1)))

(define my-facet3 (ref (fac my-pol (list 1 2 3) (list 1 2 3))))

(println (if (deref my-facet1) 3 4))

(println (+ 1 (deref my-facet2)))

(println (and (deref my-facet1) #t))

(println (or (deref my-facet1) #t))

(define x (match (deref my-facet3)
  [(list a b c)
   #:when (= 6 (+ a b c))
   'sum-is-six]
  [(list a b c) 'sum-is-not-six]))
(println x)

(define y (add1 (deref my-facet2)))
(println y)





;Errors
;Cannot compile most user-defined macros (such this one) due to syntax taint issues 
;(define-syntax (our-if-using-syntax-case stx)
;    (syntax-case stx ()
;      [(_ condition true-expr false-expr)
;       #'(cond [condition true-expr]
;               [else false-expr])]))

