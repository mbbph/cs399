;2020 Lisa Hou
;Bryn Mawr College CS 399 Senior Thesis Codebase
;Based on code from Micinski et al (2018) and Felleisen (2011)

#lang racket
(require "facets.rkt" (for-syntax "facets.rkt"))
(require (for-syntax racket/syntax))
(require (for-syntax racket/struct-info))
(require (for-syntax racket/keyword-transform))
(require (for-syntax racket/stxparam))
(require (for-syntax racket/set))
(require (for-syntax syntax/transformer))
(require (for-syntax racket/base syntax/parse))
(require racket/stxparam)

(provide (except-out (all-from-out racket) #%module-begin with-continuation-mark)
         (rename-out
          [fac-continuation-mark with-continuation-mark]
          [module-begin #%module-begin])

 let-label
 fac
 obs ;not working yet
 ref
 deref
 ref-set!
 ext-lambda
 ★
 )

;Racet macros from 'RACETS' code base
;cont-mark
(define-syntax (fac-continuation-mark stx)
  (wrong-syntax stx "continuation marks are currently unsupported in racets"))

;ext-lambda
(define-syntax (ext-lambda stx)
  (syntax-parse stx
    [(_ xs expr)
     #`(lambda xs expr)]))

;let-label
(define-syntax (let-label stx)
  (syntax-parse stx
    [(_ l (lambda xs e) body)
     #`(let ([l (labelpair (gensym 'lab)
                           (lambda xs e))])
         body)]))

;lazy fail
(define-syntax (★)
  (syntax-parse
      #`(lfail)))

;fac
(define-syntax (fac stx)
  (syntax-parse stx
    [(_ l v1 v2)
     #`(construct-facet-optimized (set->list (set-union (current-pc) (set (pos (labelpair-name l))))) v1 v2) ]))

; ref
(define-syntax (ref stx)
  (syntax-parse stx
    [(_ vr)
     #`(let ([var vr]) 
         (if (facet? var)
             (box (construct-facet-optimized (set->list (current-pc)) var (lfail)))
             (box var)))]))

; ref-set! x expr
(define-syntax (ref-set! stx)
  (syntax-parse stx
    [(_ var e)
     #`(let ([value e])
         (let setf ([var var] 
                    [pc (current-pc)])
           (if (box? var) 
               (set-box! var (construct-facet-optimized (set->list (current-pc)) value (unbox var))) 
               (mkfacet   
                (facet-labelname (unbox var))
                (setf 
                 (facet-left (unbox var)) 
                 (set-add pc (pos (facet-labelname var)))) 
                (setf 
                 (facet-right (unbox var)) 
                 (set-add pc (neg (facet-labelname var))))))))])) 

;deref
(define-syntax (deref stx)
  (syntax-parse stx
    [(_ vr)
     #`(let dereff ([var (unbox vr)])
         (if (facet? var)
             (cond
               [(set-member? (current-pc) (pos (facet-labelname var)))
                (dereff (facet-left var))]
               [(set-member? (current-pc) (neg (facet-labelname var)))
                (dereff (facet-right var))]
               [else
                (mkfacet (facet-labelname var) (dereff (facet-left var)) (dereff (facet-right var)))])
             var))]))

;obs
(define-syntax (obs stx)
  (syntax-parse stx
    [(_ l e1 e2)
     #`(let obsf ([lp l]
                  [v1 e1]
                  [v2 e2])
         (if (facet? v2)
             (let ([v2-name (facet-labelname v2)])
               (if (equal? v2-name (labelpair-name lp))
                   (if (let applyf ([func (labelpair-pol lp)])
         (cond
           [(facet? func)
            (let* ([left
                    (parameterize ([current-pc
                                    (set-add (current-pc)
                                             (pos (facet-labelname func)))])
                      (applyf (facet-left func)))]
                   [right
                    (parameterize ([current-pc
                                    (set-add (current-pc)
                                             (neg (facet-labelname func)))])
                      (applyf (facet-right func)))])
              (construct-facet-optimized
               (list (pos (facet-labelname func)))
               left
               right))]
           [(fclo? func) ((fclo-clo func) v1)]
           [else ((facet-fmap* func) v1)]))
                       (facet-left v2)
                       (facet-right v2))
                   (let* ([v2-l (facet-left v2)]
                          [v2-r (facet-right v2)])
                     (mkfacet v2-name
                              (obsf lp v1 v2-l)
                              (obsf lp v1 v2-r)))))
             v2))]))





;New forms
;module-begin
;Expands all macros before transforming
(define-syntax (module-begin stx)
  (syntax-parse stx
    [(_ forms ...)
     (with-syntax ([expanded
                    (local-expand #'(#%plain-module-begin forms ...) 'module-begin '())])
       (transform #'expanded))]))


;
(begin-for-syntax
  (define (transform stx)
    (syntax-case stx (t-quote-syntax)
      ([head id expr] ;set
       (check-ident #'head #'set!)
       #`(head id #,(transform #'expr)))

      ([a b ...] ;provide
       (check-ident #'a #'#%provide)
       stx)

      ([a b ...] ;require
       (check-ident #'a #'#%require)
       stx)

      ([head xs expr] ;plain-lambda
       (check-ident #'head #'#%plain-lambda)
        #`(fclo (lambda xs #,(transform #'expr))))

      ([head xs expr] ;lambda
       (check-ident #'head #'lambda)
       #`(fclo (lambda xs #,(transform #'expr))))

      ;various #%app conditions
      ([head (lrv (((obsf1) lamb)) obsf2) arg1 arg2 arg3] ;(#%app (letrec-values (((obsf) lamb)) obsf arg1 arg2 arg3)
       (and (eq? (syntax-e #'head) '#%app) (check-ident #'lrv #'letrec-values) (check-ident #'obsf1 #'obsf) (check-ident #'obsf12 #'obsf))
       stx)
      
      ([head f args1] ;(#%app [struct constructor id] args) or (#%app gensym args)
       (and (eq? (syntax-e #'head) '#%app) (or (syntax-procedure-alias-property #'f) (check-ident #'f #'gensym)))
       #`(head f #,(transform #'args1)))

      ([head f args1 args2] ;similar to above -- may be extraneous
       (or (and (eq? (syntax-e #'head) '#%app) (syntax-procedure-alias-property #'f)) (check-ident #'f #'gensym)) 
       #`(head f #,(transform #'args1) #,(transform #'args2)))

      ([head f . args] ;(#%app construct-facet-optimized . args) or (#%app facet? . args)
       (and (eq? (syntax-e #'head) '#%app) (or (check-ident #'f #'construct-facet-optimized) (check-ident #'f #'facet?)))
       stx)
      
      ([head f . args] ;general #%app
       (and (eq? (syntax-e #'head) '#%app) (not (check-ident #'f #'gensym)) (not (syntax-procedure-alias-property #'f)))
       #`(let applyf ([func f])
         (cond
           [(facet? func)
            (let* ([left
                    (parameterize ([current-pc
                                    (set-add (current-pc)
                                             (pos (facet-labelname func)))])
                      (applyf (facet-left func)))]
                   [right
                    (parameterize ([current-pc
                                    (set-add (current-pc)
                                             (neg (facet-labelname func)))])
                      (applyf (facet-right func)))])
              (construct-facet-optimized
               (list (pos (facet-labelname func)))
               left
               right))]
           [(fclo? func) ((fclo-clo func) . #,(map transform (syntax-e #'args)))]
           [else ((facet-fmap* func) . #,(map transform (syntax-e #'args)))])))

      ;various 'if' conditions
      ([head (f fac v) et ef] ;(if (#%app facet? v) et ef)
       (and (check-ident #'head #'if) (eq? (syntax-e #'f) '#%app) (check-ident #'fac #'facet?))
       #`(head (f fac v) et #,(transform #'ef)))

      ([head guard et ef] ;general if
       (check-ident #'head #'if)
       #`(let iff ([gv #,(transform #'guard)])
         (if (facet? gv)
             (cond
               [(set-member? (current-pc) (pos (facet-labelname gv))) 
                (iff (facet-left gv))]  
               [(set-member? (current-pc) (neg (facet-labelname gv)))
                (iff (facet-right gv))]
               [else 
                (let*
                    ([left
                      (parameterize ([current-pc (set-add (current-pc)
                                                          (pos
                                                           (facet-labelname gv)))]) 
                        (iff (facet-left gv)))]
                     [right
                      (parameterize ([current-pc (set-add (current-pc)
                                                          (neg
                                                           (facet-labelname gv)))]) 
                        (iff (facet-right gv)))]) 
                  (construct-facet-optimized (list (pos (facet-labelname gv))) left right))])
             (if gv #,(transform #'et) #,(transform #'ef)))))

      ;various 'let-values' conditions
      ([head (((id) val-expr)) body] ;one ((id) val-expr) clause
       (check-ident #'head #'let-values)
       #`(head ([(id) #,(transform #'val-expr)]) #,(transform #'body)))

      ([head (((id) val-expr) ((id2) val-expr2)) body] ;two ((id) val-expr) clauses
       (check-ident #'head #'let-values) 
       #`(head ([(id) #,(transform #'val-expr)] [(id2) #,(transform #'val-expr2)]) #,(transform #'body)))

      ([head ([(id) val-expr]) body]
       (check-ident #'head #'letrec-values) ;single letrec-values clause
        #`(head ([(id) #,(transform #'val-expr)]) #,(transform #'body)))

;      let-values and letrec-values with arbitrary number of clauses require the use of map
;      but I am unable to get it working 
;      #`(head #,(map (lambda (fst . snd)
;                       [list fst snd])
;                                   ;(fst . (transform snd)))
;                     (map syntax-e
;                                 (syntax-e #'([(id ...) val-expr] ...))))
;                             #,(map (lambda (bod)
;                                    (transform bod))
;                                  (syntax-e #'(body ...))))))
                                
                                     
      ([t-quote-syntax b] ;need this to get rid of one of the syntax taint problems 
       stx)

      ([a b ...] ;miscellaneous forms
       (datum->syntax stx (cons #'a (map transform (syntax-e #'(b ...))))))

      (a ;single val -- the base case
       stx))))

(begin-for-syntax (define (check-ident ident expected)
  (and (identifier? ident)
       (free-identifier=? ident expected))))
