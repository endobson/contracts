#lang racket/base

(require
  "../kinds.rkt"
  "../structures.rkt"
  "../constraints.rkt"
  racket/list
  racket/match
  (except-in racket/contract recursive-contract))

(provide
  (contract-out
    (struct simple-contract ([args empty?] [syntax syntax?] [kind contract-kind?]))))

(define (simple-contract-write-proc v port mode)
  (match-define (simple-contract _ syntax kind) v)
  (define-values (open close)
    (if (equal? mode 0)
        (values "(" ")")
        (values "#<" ">")))
  (display open port)
  (fprintf port "~a/sc" kind)
  (display " " port)
  (write (syntax->datum syntax) port)
  (display close port))



(struct simple-contract combinator (syntax kind)
        #:methods gen:sc-mapable [(define (sc-map v f) v)]
        #:methods gen:sc-contract [(define (sc->contract v f) (simple-contract-syntax v))]
        #:methods gen:sc-constraints [(define (sc->constraints v f) (simple-contract-restrict (simple-contract-kind v)))]
        #:methods gen:custom-write [(define write-proc simple-contract-write-proc)])
