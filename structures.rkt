#lang racket/base

(require racket/match racket/list racket/generic 
         (except-in racket/contract recursive-contract)
         "kinds.rkt")

(provide
  (contract-out
    (struct simple-contract ([args empty?] [syntax syntax?] [kind contract-kind?]))
    (struct recursive-contract ([names (listof identifier?)]
                                [values (listof static-contract?)]
                                [body static-contract?]))
    (struct recursive-contract-use ([name identifier?]))
    (struct combinator ([args (listof static-contract?)]))
    (struct flat-combinator ([args (listof static-contract?)]))
    (struct chaperone-combinator ([args (listof static-contract?)]))
    (struct impersonator-combinator ([args (listof static-contract?)]))
    (struct restrict ([body static-contract?]))
    (struct flat-restrict ([body static-contract?]))
    (struct chaperone-restrict ([body static-contract?]))
    [sc-map (static-contract? (static-contract? variance/c . -> . static-contract?) . -> . static-contract?)]
    [sc->contract (static-contract? (static-contract? . -> . syntax?) . -> . syntax?)]
    [static-contract? predicate/c]
    [sc-contract? predicate/c]
    )


  prop:combinator-name
  gen:sc-contract
  gen:sc-mapable)

(define variance/c (or/c 'covariant 'contravariant 'invariant))

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

(define (recursive-contract-write-proc v port mode)
  (match-define (recursive-contract names vals body) v)
  (define recur
    (case mode
      [(#t) write]
      [(#f) display]
      [else (lambda (p port) (print p port mode))]))
  (define-values (open close)
    (if (equal? mode 0)
        (values "(" ")")
        (values "#<" ">")))
  (display open port)
  (fprintf port "rec/sc")
  (display " (" port)
  (define (recur-pair name val)
    (fprintf port "(~a " (syntax->datum name))
    (recur val port)
    (display ")" port))
  (recur-pair (first names) (first vals))
  (for ((name (rest names))
        (val (rest vals)))
       (display " " port)
       (recur-pair name val))
  (display ") " port)
  (recur body port)
  (display close port))

(define (recursive-contract-use-write-proc v port mode)
  (display (syntax->datum (recursive-contract-use-name v)) port))

(define (combinator-write-proc v port mode)
  (match-define (combinator args) v)
  (define name (combinator-name v))
  (define recur
    (case mode
      [(#t) write]
      [(#f) display]
      [else (lambda (p port) (print p port mode))]))
  (define-values (open close)
    (if (equal? mode 0)
        (values "(" ")")
        (values "#<" ">")))
  (display open port)
  (fprintf port name)
  (for ((arg args))
       (display " " port)
       (recur arg port))
  (display close port))

(define ((restrict-write-proc name) v port mode)
  (match-define (restrict body) v)
  (define recur
    (case mode
      [(#t) write]
      [(#f) display]
      [else (lambda (p port) (print p port mode))]))
  (define-values (open close)
    (if (equal? mode 0)
        (values "(" ")")
        (values "#<" ">")))
  (display open port)
  (fprintf port name)
  (display " " port)
  (recur body port)
  (display close port))


(define-values (prop:combinator-name
                has-combinator-name?
                combinator-name)
  (make-struct-type-property 'combinator-name
    (lambda (v _) 
      (unless (string? v)
        (raise-argument-error
          'prop:combinator-name
          "string?"
          v))
      v)))

(define-generics sc-mapable
  [sc-map sc-mapable f])

(define-generics sc-contract
  [sc->contract sc-contract f])



(struct static-contract ()
        #:property prop:custom-print-quotable 'never)

(struct recursive-contract static-contract (names values body)
        #:methods gen:custom-write [(define write-proc recursive-contract-write-proc)])

(struct recursive-contract-use static-contract (name)
        #:methods gen:sc-mapable [(define (sc-map v f) v)]
        #:methods gen:sc-contract [(define (sc->contract v f) (recursive-contract-use-name v))]
        #:methods gen:custom-write [(define write-proc recursive-contract-use-write-proc)])

(struct combinator static-contract (args)
        #:property prop:combinator-name "combinator/sc"
        #:methods gen:custom-write [(define write-proc combinator-write-proc)])
(struct flat-combinator combinator ())
(struct chaperone-combinator combinator ())
(struct impersonator-combinator combinator ())
(struct simple-contract combinator (syntax kind)
        #:methods gen:sc-mapable [(define (sc-map v f) v)]
        #:methods gen:sc-contract [(define (sc->contract v f) (simple-contract-syntax v))]
        #:methods gen:custom-write [(define write-proc simple-contract-write-proc)])


(struct restrict static-contract (body)
        #:methods gen:sc-contract [(define (sc->contract v f) (f (restrict-body v)))])
(struct flat-restrict restrict ()
        #:methods gen:sc-mapable [(define (sc-map v f) (flat-restrict (f (restrict-body v) 'covariant)))]
        #:methods gen:custom-write [(define write-proc (restrict-write-proc "flat-restrict/sc"))])
(struct chaperone-restrict restrict ()
        #:methods gen:sc-mapable [(define (sc-map v f) (chaperone-restrict (f (restrict-body v) 'covariant)))]
        #:methods gen:custom-write [(define write-proc (restrict-write-proc "chaperone-restrict/sc"))])

