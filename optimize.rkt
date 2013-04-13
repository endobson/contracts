#lang racket/base

(require "combinators.rkt"
         "structures.rkt"
         racket/set
         unstable/debug
         racket/trace
         racket/match)

(define list?/sc (flat/sc #'list?))
(define set?/sc (flat/sc #'set?))
(define box?/sc (flat/sc #'box?))
(define vector?/sc (flat/sc #'box?))
(define syntax?/sc (flat/sc #'syntax?))
(define promise?/sc (flat/sc #'promise?))
(define hash?/sc (flat/sc #'hash?))

(define (any/sc-reduce sc)
  (match sc
    [(flat-restrict (any/sc:)) any/sc]
    [(chaperone-restrict (any/sc:)) any/sc]
    [(listof/sc: (any/sc:)) list?/sc]
    [(vectorof/sc: (any/sc:)) vector?/sc]
    [(set/sc: (any/sc:)) set?/sc]
    [(box/sc: (any/sc:)) box?/sc]
    [(syntax/sc: (any/sc:)) syntax?/sc]
    [(promise/sc: (any/sc:)) promise?/sc]
    [(hash/sc: (any/sc:) (any/sc:)) hash?/sc]
    [(any/sc:) sc]
    [else sc]))



(define (optimize sc)
  (define (single-step sc variance)
    (any/sc-reduce sc))

  (define (recur sc variance)
    (single-step (sc-map sc recur) variance))
  (recur sc 'pos))


(module+ test
  (require rackunit)
  (define-simple-check (check-optimize argument expected)
    (equal? (optimize argument) expected))
  (check-optimize 
    (listof/sc any/sc)
    list?/sc)
  (check-optimize 
    (set/sc any/sc)
    set?/sc))

