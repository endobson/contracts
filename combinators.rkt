#lang racket/base

(require "structures.rkt"
         "combinators/any.rkt"
         "combinators/function.rkt"
         racket/list racket/match
         (for-syntax racket/base racket/syntax syntax/parse)
         racket/set
         unstable/contract
         (except-in racket/contract recursive-contract))

(provide (all-defined-out)
         (all-from-out "combinators/any.rkt"
                       "combinators/function.rkt"))





(begin-for-syntax
  (define-syntax-class variance-keyword
    #:attributes (variance)
    [pattern (~and kw (~or #:covariant #:contravariant #:invariant))
             #:attr variance (string->symbol (keyword->string (syntax-e (attribute kw))))])

  (define-syntax-class contract-category-keyword
    #:attributes (category struct)
    [pattern (~and kw (~or #:flat #:chaperone #:impersonator))
             #:attr category (string->symbol (keyword->string (syntax-e (attribute kw))))
             #:attr struct (case (attribute category)
                             ((flat) #'flat-combinator)
                             ((chaperone) #'chaperone-combinator)
                             ((impersonator) #'impersonator-combinator))])

  (define-syntax-class argument-description
    #:attributes (variance name restricted-name)
    [pattern ((~or (~optional :contract-category-keyword)
                   (~once :variance-keyword)) ...)
             #:attr name (generate-temporary)
             #:attr restricted-name
               (case (attribute category)
                 ((flat) #'(flat-restrict name))
                 ((chaperone) #'(chaperone-restrict name))
                 (else #'name))])

  (define-syntax-class static-combinator-form
    #:attributes (name struct-name definition combinator2 matcher)
    [pattern (name:id pos:argument-description ... )
             #:with struct-name (generate-temporary #'name)
             #:with matcher-name (format-id #'name "~a:" #'name)
             #:with definition
               #'(define name (λ (pos.name ...) (struct-name (list pos.restricted-name ...))))
             #:attr combinator2
               #'(λ (constructor) (λ (pos.name ...) (constructor (list pos.name ...))))
             #:with matcher
               #'(define-match-expander matcher-name
                   (syntax-parser
                     [(_ pos.name ...)
                      #'(struct-name (list pos.name ...))]))]
    [pattern (name:id . rest:argument-description)
             #:with struct-name (generate-temporary #'name)
             #:with matcher-name (format-id #'name "~a:" #'name)
             #:with definition #'(define name #'(λ args (struct-name args)))
             #:attr combinator2 #'(λ args (struct-name args))
             #:with matcher
               #'(define-match-expander matcher-name
                   (syntax-parser
                    [(_ ctc (... ...))
                     #'(struct-name _ (list ctc (... ...)))]))]))


(define-syntax (combinator-struct stx)
  (syntax-parse stx
    [(_ sc:static-combinator-form c:expr kind:contract-category-keyword)
     #'(begin
         (struct sc.struct-name kind.struct ()
                 #:methods gen:sc-mapable
                   [(define (sc-map v f)
                      (sc.struct-name
                        (for/list ((a (combinator-args v)))
                          (f a 'covariant))))]
                 #:methods gen:sc-contract
                   [(define (sc->contract v recur)
                      (apply
                        (sc.combinator2 (lambda (args) #`(c #,@args)))
                        (map recur (combinator-args v))))]
                 #:property prop:combinator-name (symbol->string 'sc.name))
         sc.matcher
         sc.definition)]))


(define-syntax (combinator-structs stx)
  (syntax-parse stx
    [(_ (e ...) ...)
     #`(begin
         (combinator-struct e ...) ...)]))

(combinator-structs
  ((or/sc . (#:covariant)) or/c #:flat)
  ((and/sc . (#:covariant)) and/c #:flat)
  ((list/sc . (#:covariant)) list/c #:flat)
  ((listof/sc (#:covariant)) listof #:flat)
  ((cons/sc (#:covariant) (#:covariant)) cons/c #:flat)
  ((set/sc (#:covariant #:chaperone)) set/c #:flat)
  ((vector/sc . (#:invariant)) vector/c #:chaperone)
  ((vectorof/sc (#:invariant)) vectorof #:chaperone)
  ((promise/sc (#:covariant)) promise/c #:chaperone)
  ((syntax/sc (#:covariant #:flat)) syntax/c #:flat)
  ((hash/sc (#:invariant #:flat) (#:invariant)) hash/c #:chaperone)
  ((box/sc (#:invariant)) box/c #:chaperone)
  ((parameter/sc (#:contravariant) (#:covariant)) parameter/c #:chaperone)
  ((sequence/sc (#:covariant)) sequence/c #:chaperone))


;; Struct Definitions
(struct struct-combinator chaperone-combinator ())
(struct continuation-mark-key-combinator chaperone-combinator ())
(struct prompt-tag-combinator chaperone-combinator ())
(struct parametric-combinator flat-combinator ())
(struct case->-combinator chaperone-combinator ())
(struct arr-combinator chaperone-combinator ())


;; Combinators
(define (flat/sc ctc) (simple-contract ctc 'flat))
(define (chaperone/sc ctc) (simple-contract ctc 'chaperone))
(define (impersonator/sc ctc) (simple-contract ctc 'impersonator))


(define continuation-mark-key/sc (lambda (sc) (error 'nyi)))

(define (prompt-tag/sc* scs call/cc-sc)
  (prompt-tag-combinator
    (λ (call/cc-ctc . others)
       #`(prompt-tag/c #,@others #:call/cc call/cc-ctc)
       (cons call/cc-sc scs))))

(define (object/sc* methods) (error 'nyi))
(define (class/sc* methods) (error 'nyi))


(define identifier/sc (flat/sc #'identifier?))



(define case->/sc  (lambda (sc) (error 'nyi)))

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



