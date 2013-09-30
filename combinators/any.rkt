#lang racket/base

(require "../structures.rkt"
         racket/match
         (except-in racket/contract recursive-contract)
         (for-syntax racket/base racket/syntax syntax/parse))

(provide
  (contract-out
    [any/sc static-contract?])
  any/sc:)


;;Printing
(define (any-write-proc v port mode)
  (if (equal? mode 0)
      (display "any/sc" port)
      (display "#<any/sc>" port)))

(struct any-combinator simple-contract ()
        #:methods gen:custom-write [(define write-proc any-write-proc)])

(define-match-expander any/sc:
  (syntax-parser
    [(_) #'(any-combinator _ _ _)]))

(define any/sc (any-combinator null #'any/c 'flat))

