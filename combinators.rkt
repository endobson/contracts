#lang racket/base

(require "structures.rkt" racket/list)

;; for syntax
(require racket/set
         (except-in racket/contract recursive-contract))

(provide (all-defined-out))

;;Printing
(define (any-write-proc v port mode)
  (if (equal? mode 0)
      (display "any/sc" port)
      (display "#<any/sc>" port)))

;; Struct Definitions
(struct any-combinator simple-contract ()
        #:methods gen:custom-write [(define write-proc any-write-proc)])
(struct or-combinator flat-combinator ()
        #:property prop:combinator-name "or/sc")
(struct and-combinator flat-combinator ()
        #:property prop:combinator-name "and/sc")
(struct list/c-combinator flat-combinator ()
        #:property prop:combinator-name "list/sc")
(struct listof-combinator flat-combinator ()
        #:property prop:combinator-name "listof/sc")
(struct cons-combinator flat-combinator ()
        #:property prop:combinator-name "cons/sc")
(struct vector/c-combinator chaperone-combinator ()
        #:property prop:combinator-name "vector/sc")
(struct vectorof-combinator chaperone-combinator ()
        #:property prop:combinator-name "vectorof/sc")
(struct set-combinator chaperone-combinator ()
        #:property prop:combinator-name "set/sc")
(struct promise-combinator chaperone-combinator ()
        #:property prop:combinator-name "promise/sc")
(struct syntax-combinator chaperone-combinator ()
        #:property prop:combinator-name "syntax/sc")
(struct hash-combinator chaperone-combinator ()
        #:property prop:combinator-name "hash/sc")
(struct box-combinator impersonator-combinator ()
        #:property prop:combinator-name "box/sc")
(struct parameter-combinator impersonator-combinator ()
        #:property prop:combinator-name "parameter/sc")
(struct sequence-combinator impersonator-combinator ()
        #:property prop:combinator-name "sequence/sc")
(struct struct-combinator chaperone-combinator ())
(struct continuation-mark-key-combinator chaperone-combinator ())
(struct prompt-tag-combinator chaperone-combinator ())
(struct parametric-combinator flat-combinator ())
(struct function-combinator chaperone-combinator ())
(struct case->-combinator chaperone-combinator ())
(struct arr-combinator chaperone-combinator ())

;; Helpers
(define ((app stx) . ctcs) #`(#,stx #,@ctcs))

(define ((combine combinator stx) sc)
  (combinator (app stx) (list sc)))
(define ((combine* combinator stx) scs)
  (combinator (app stx) scs))

;; Combinators
(define (or/sc . scs) (or/sc* scs))
(define (and/sc . scs) (and/sc* scs))
(define or/sc* (combine* or-combinator #'or/c))
(define and/sc* (combine* and-combinator #'and/c))

(define (list/sc . scs) (list/sc* scs))
(define list/sc* (combine* list/c-combinator #'list/c))
(define listof/sc (combine listof-combinator #'listof))
(define (vector/sc . scs) (vector/sc* scs))
(define vector/sc* (combine* vector/c-combinator #'vector/c))
(define vectorof/sc (combine* vectorof-combinator #'vectorof))

(define (flat/sc ctc) (simple-contract ctc 'flat))
(define (chaperone/sc ctc) (simple-contract ctc 'chaperone))
(define (impersonator/sc ctc) (simple-contract ctc 'impersonator))

(define sequence/sc (combine* sequence-combinator #'sequence/c))
(define box/sc (combine box-combinator #'box/c))
(define promise/sc (combine promise-combinator #'promise/c))
(define continuation-mark-key/sc
  (combine continuation-mark-key-combinator #'continuation-mark-key/c))


(define (syntax/sc sc)
  (syntax-combinator (app #'syntax/c)
    (list (flat-restrict sc))))
(define (set/sc sc)
  (set-combinator (app #'set/c)
    (list (chaperone-restrict sc))))

(define (cons/sc left right)
  (cons-combinator (app #'cons/c) (list left right)))
;;TODO make this sound
(define (parameter/sc in out)
  (parameter-combinator (app #'parameter/c) (list out)))
(define (hash/sc key value)
  (hash-combinator (app #'hash/c) (list key value)))

(define (prompt-tag/sc* scs call/cc-sc)
  (prompt-tag-combinator
    (λ (call/cc-ctc . others)
       #`(prompt-tag/c #,@others #:call/cc call/cc-ctc)
       (cons call/cc-sc scs))))

(define (object/sc* methods) (error 'nyi))
(define (class/sc* methods) (error 'nyi))


(define any/sc (any-combinator #'any/c 'flat))
(define identifier/sc (flat/sc #'identifier?))

(define (function/sc mand-args opt-args mand-kws opt-kws rest range)
  (define mand-args-start 0)
  (define mand-args-end (length mand-args))
  (define opt-args-start mand-args-end)
  (define opt-args-end (+ opt-args-start (length opt-args)))
  (define mand-kw-args-start opt-args-end)
  (define mand-kw-args-end (+ mand-kw-args-start (length mand-kws)))
  (define opt-kw-args-start mand-kw-args-end)
  (define opt-kw-args-end (+ opt-kw-args-start (length opt-kws)))
  (define rest-start opt-kw-args-end)
  (define rest-end (if rest (add1 rest-start) rest-start))
  (define range-start rest-end)
  (define range-end (if range (+ range-start (length range)) range-start))
  (function-combinator
    (lambda ctcs
      (define mand-ctcs (drop (take ctcs mand-args-end) mand-args-start))
      (define opt-ctcs (drop (take ctcs opt-args-end) opt-args-start))
      (define mand-kw-ctcs (drop (take ctcs mand-kw-args-end) mand-kw-args-start))
      (define opt-kw-ctcs (drop (take ctcs opt-kw-args-end) opt-kw-args-start))
      (define rest-ctc-stx
        (if rest
            (list '#:rest (first (drop (take ctcs rest-end) rest-start)))
            #'()))
      (define range-ctc
        (if range
            #`(values #,@(drop (take ctcs range-end) range-start))
            #'any))

      (define mand-kws-stx (append-map list (map first mand-kws) mand-kw-ctcs))
      (define opt-kws-stx (append-map list (map first opt-kws) opt-kw-ctcs))


      #`((#,@mand-ctcs #,@mand-kws-stx)
         (#,@opt-ctcs #,@opt-kws-stx) 
         #,@rest-ctc-stx
         . ->* . #,range-ctc))
    (append
      mand-args
      opt-args
      (map second mand-kws)
      (map second opt-kws)
      (if rest (list rest) null)
      (or range null))))

(define case->/sc 
  (combine* case->-combinator #'case->))

(define (arr/sc mand-args rest range)
  (define mand-args-start 0)
  (define mand-args-end (length mand-args))
  (define rest-start mand-args-end)
  (define rest-end (if rest (add1 rest-start) rest-start))
  (define range-start rest-end)
  (define range-end (if range (+ range-start (length range)) range-start))
  (arr-combinator
    (lambda ctcs
      (define mand-ctcs (drop (take ctcs mand-args-end) mand-args-start))
      (define rest-ctc-stx
        (if rest
            (list '#:rest (first (drop (take ctcs rest-end) rest-start)))
            #'()))
      (define range-ctc
        (if range
            #`(values #,@(drop (take ctcs range-end) range-start))
            #'any))
      #`(#,@mand-ctcs #,@rest-ctc-stx . -> . #,range-ctc))
    (append
      mand-args
      (if rest (list rest) null)
      (or range null))))

(define (struct/sc name fields)
  (struct-combinator (λ ctcs #`(struct/c name #,ctcs)) fields))

(define (parametric->/sc vars body)
  (parametric-combinator (λ (ctc) #`(parametric->/c (#,@vars) #,ctc)) body))
