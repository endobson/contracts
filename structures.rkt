#lang racket/base

(require racket/match racket/list)

(provide
  (struct-out simple-contract)
  (struct-out recursive-contract)
  (struct-out recursive-contract-use)
  (struct-out combinator)
  (struct-out flat-combinator)
  (struct-out chaperone-combinator)
  (struct-out impersonator-combinator)
  (struct-out restrict)
  (struct-out flat-restrict)
  (struct-out chaperone-restrict)
  prop:combinator-name)


(define (simple-contract-write-proc v port mode)
  (match-define (simple-contract syntax kind) v)
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
  (match-define (combinator _ args) v)
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





(struct simple-contract (syntax kind)
        #:methods gen:custom-write [(define write-proc simple-contract-write-proc)])

(struct recursive-contract (names values body)
        #:methods gen:custom-write [(define write-proc recursive-contract-write-proc)])

(struct recursive-contract-use (name)
        #:methods gen:custom-write [(define write-proc recursive-contract-use-write-proc)])

(struct combinator (make-syntax args)
        #:property prop:combinator-name "combinator/sc"
        #:methods gen:custom-write [(define write-proc combinator-write-proc)])
(struct flat-combinator combinator ())
(struct chaperone-combinator combinator ())
(struct impersonator-combinator combinator ())
(struct restrict (body))
(struct flat-restrict restrict ()
        #:methods gen:custom-write [(define write-proc (restrict-write-proc "flat-restrict/sc"))])
(struct chaperone-restrict restrict ()
        #:methods gen:custom-write [(define write-proc (restrict-write-proc "chaperone-restrict/sc"))])

