#lang racket/base

(require racket/match)

(provide
  contract-kind?
  contract-kind<
  kind->keyword
  combine-kinds)

(define (contract-kind? v)
  (case v
    ((flat chaperone impersonator) #t)
    (else #f)))

(define (contract-kind< v1 v2)
  (match* (v1 v2)
    [('flat _) #t]
    [('chaperone 'flat) #f]
    [('chaperone (or 'chaperone 'impersonator)) #t]
    [('impersonator (or 'flat 'chaperone)) #f]
    [('impersonator 'impersonator) #t]))

(define combine-kinds
  (case-lambda
    ((v) v)
    ((v1 v2 . vs)
     (define combined
       (cond
         ((impersonator? v1) v1)
         ((impersonator? v2) v2)
         ((chaperone? v1) v1)
         ((chaperone? v2) v2)
         (else 'flat)))
          
     (apply combine-kinds combined vs))))

(define (kind->keyword kind)
  (case kind
    ((flat) '#:flat)
    ((chaperone) '#:chaperone)
    ((impersonator) '#:impersonator)))
