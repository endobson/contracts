#lang scheme/base

(require tests/typed-racket/unit-tests/test-utils
         (for-syntax scheme/base)        
         (for-template scheme/base)      
         (private type-contract)         
         (types abbrev numeric-tower)    
         rackunit
         "types.rkt" "instantiate.rkt")             

(define-syntax-rule (t e)      
  (test-not-exn (format "~a" e) (lambda () (type->contract e (lambda _ (error "type could not be converted to contract"))))))

(define-syntax-rule (t/sc e)      
  (test-not-exn (format "~a" e) (lambda () (type->static-contract e (lambda _ (error "type could not be converted to contract"))))))

(define-syntax-rule (t/fail e) 
  (test-not-exn (format "~a" e) (lambda () 
                                  (let/ec exit                    
                                    (type->contract e (lambda _ (exit #t)))
                                    (error "type could be converted to contract")))))

(define contract-tests
  (test-suite "Contract Tests" 
              (t (-Number . -> . -Number))    
              (t/sc (-Number . -> . -Number))    
              (t (-Promise -Number))          
              (t (-set Univ))  
              ))               

(define types-to-test
  (list
    -Number
    (-lst -Number)
    (-Number . -> . -Number)))

(for ((type types-to-test))
  (displayln (syntax->datum
    (instantiate (type->static-contract type (lambda (_)
                                                  (error 'testing "type could not be converted to a contract")))))))

(require rackunit/text-ui)
;(run-tests contract-tests)
