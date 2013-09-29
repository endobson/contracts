#lang racket/base

(require "combinators.rkt"
         "structures.rkt"
         racket/set
         unstable/debug
         racket/trace
         racket/match)

(provide optimize)

(define list?/sc (flat/sc #'list?))
(define set?/sc (flat/sc #'set?))
(define box?/sc (flat/sc #'box?))
(define vector?/sc (flat/sc #'box?))
(define syntax?/sc (flat/sc #'syntax?))
(define promise?/sc (flat/sc #'promise?))
(define hash?/sc (flat/sc #'hash?))

(define (any/sc-reduce sc)
  (match sc
    [(restrict (any/sc:)) any/sc]
    [(listof/sc: (any/sc:)) list?/sc]
    [(vectorof/sc: (any/sc:)) vector?/sc]
    [(set/sc: (any/sc:)) set?/sc]
    [(box/sc: (any/sc:)) box?/sc]
    [(syntax/sc: (any/sc:)) syntax?/sc]
    [(promise/sc: (any/sc:)) promise?/sc]
    [(hash/sc: (any/sc:) (any/sc:)) hash?/sc]
    [(->/sc: mand-args opt-args mand-kw-args opt-kw-args rest-arg (list (any/sc:) ...))
     (function/sc mand-args opt-args mand-kw-args opt-kw-args rest-arg #f)]
    [(any/sc:) sc]
    [else sc]))

(define (flat-reduce sc)
  (match sc
    [(simple-contract stx 'flat)
     any/sc]
    [(flat-restrict (simple-contract stx 'flat))
     any/sc]
    [(chaperone-restrict (simple-contract stx 'flat))
     any/sc]
    [sc sc]))

(define (invert-variance v)
  (case v
    [(covariant) 'contravariant]
    [(contravariant) 'covariant]
    [(invariant) 'invariant]))

(define (combine-variance var1 var2)
  (case var1
    [(covariant) var2]
    [(contravariant) (invert-variance var2)]
    [(invariant) 'invariant]))

(define (optimize sc variance)
  (define (single-step sc variance)
    (define (maybe-flat-reduce sc)
      (case variance
        [(covariant) (flat-reduce sc)]
        [(contravariant invariant) sc]
        [else (error 'maybe-flat-reduce "Bad variance ~a" variance)]))
    (maybe-flat-reduce (any/sc-reduce sc)))

  (define ((recur current-variance) sc variance)
    (define new-variance (combine-variance current-variance variance))
    (single-step (sc-map sc (recur new-variance)) new-variance))
  ((recur variance) sc 'covariant))


(module+ test
  (require rackunit)
  (provide optimizer-tests)
  (define-simple-check (check-optimize variance argument expected)
    (equal? (optimize argument variance) expected))
  (define optimizer-tests
    (test-suite "Optimizer Tests"
      (check-optimize 'covariant
        (listof/sc any/sc)
        any/sc)
      (check-optimize 'contravariant
        (listof/sc any/sc)
        list?/sc)
      (check-optimize 'covariant
        (set/sc any/sc)
        any/sc)
      (check-optimize 'contravariant
        (set/sc any/sc)
        set?/sc)
      (check-optimize 'covariant
        (function/sc (list (listof/sc any/sc))
                     (list)
                     (list)
                     (list)
                     #f
                     (list (listof/sc any/sc)))
        (function/sc (list list?/sc)
                     (list)
                     (list)
                     (list)
                     #f
                     #f))
      (check-optimize 'contravariant
        (function/sc (list (listof/sc any/sc))
                     (list)
                     (list)
                     (list)
                     #f
                     (list (listof/sc any/sc)))
        (function/sc (list any/sc)
                     (list)
                     (list)
                     (list)
                     #f
                     (list list?/sc))))))
