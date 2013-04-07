#lang scheme/base

(require tests/typed-racket/unit-tests/test-utils
         (for-syntax scheme/base)        
         (for-template scheme/base)      
         (private type-contract)         
         (types abbrev numeric-tower union)    
         rackunit
         "types.rkt" "instantiate.rkt")             

(define-syntax-rule (t e)      
  (test-not-exn (format "~a" e) (lambda () (type->contract e (lambda _ (error "type could not be converted to contract"))))))

(define-namespace-anchor anchor)
(define ns (namespace-anchor->empty-namespace anchor))

(define-syntax-rule (t/sc e)      
  (test-not-exn (format "~a" e)
    (lambda ()
      (define sc
         (type->static-contract e (lambda _ (error "type could not be converted to contract"))))
      (eval-syntax (instantiate sc) ns))))

(define-syntax-rule (t/fail e) 
  (test-not-exn (format "~a" e) (lambda () 
                                  (let/ec exit                    
                                    (type->contract e (lambda _ (exit #t)))
                                    (error "type could be converted to contract")))))

(define contract-tests
  (test-suite "Contract Tests" 
              (t/sc (-Number . -> . -Number))    
              (t/sc (-Promise -Number))          
              (t/sc (-lst -Symbol))
              (t/sc (-set Univ))  
              (t/sc (-poly (a) (-lst a)))
              (t/sc (-mu a (-lst a)))
              (t/sc (-mu a (-box a)))
              ))               



(require rackunit/text-ui)
(void (run-tests contract-tests))

