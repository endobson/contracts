#lang racket/base

(require "../structures.rkt" "../constraints.rkt"
         racket/list racket/match
         unstable/contract
         (except-in racket/contract recursive-contract))

(provide
  (contract-out
    [case->/sc ((listof arr-combinator?) . -> . static-contract?)]
    [arr/sc (-> (listof static-contract?)
                (maybe/c static-contract?)
                (maybe/c (listof static-contract?))
                static-contract?)]))


(define (case->/sc arrs)
  (case-combinator arrs))

(define (arr/sc args rest range)
  (arr-combinator (arr-seq args rest range)))

(struct case-combinator combinator ())
(struct arr-combinator combinator ())
(struct arr-seq (args rest range)
        #:property prop:sequence
          (match-lambda 
            [(arr-seq args rest range)
             (append
               args
               (if rest (list rest) empty)
               (if range range empty))]))
