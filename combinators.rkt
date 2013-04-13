#lang racket/base

(require "structures.rkt" racket/list
         racket/match
         (for-syntax racket/base syntax/parse))

;; for syntax
(require racket/set
         (except-in racket/contract recursive-contract))

(provide (all-defined-out))

;;Printing
(define (any-write-proc v port mode)
  (if (equal? mode 0)
      (display "any/sc" port)
      (display "#<any/sc>" port)))


;; Helpers
(define ((app stx) . ctcs) #`(#,stx #,@ctcs))

(define ((combine combinator stx) sc)
  (combinator (app stx) (list sc)))
(define ((combine* combinator stx) scs)
  (combinator (app stx) scs))

(define ((combinator-map* constructor) v f)
  (match v
    [(combinator stx args) (constructor stx (for/list ((a args))
                                              (f a 'pos)))]))
(define-syntax-rule (combinator-map constructor)
  (combinator-map* (lambda (stx args) (constructor stx args))))

(begin-for-syntax
  (define-splicing-syntax-class contract-form
    [pattern (~seq #:single c:id)
             #:attr fun #'(λ (constructor) (λ (sc) (constructor (app #'c) (list sc))))]
    [pattern (~seq #:double c:id)
             #:attr fun #'(λ (constructor) (λ (sc1 sc2) (constructor (app #'c) (list sc1 sc2))))]
    [pattern (~seq #:list c:id)
             #:attr fun #'(λ (constructor) (λ scs (constructor (app #'c) scs)))])

  (define-syntax-class variance-keyword
    #:attributes (variance)
    [pattern (~and kw (~or #:covariant #:contravariant #:invariant))
             #:attr variance (string->symbol (keyword->string (syntax-e (attribute kw))))])
  (define-syntax-class contract-category-keyword
    #:attributes (category)
    [pattern (~and kw (~or #:flat #:chaperone #:impersonator))
             #:attr category (string->symbol (keyword->string (syntax-e (attribute kw))))])

  (define-syntax-class argument-description
    #:attributes (variance)
    [pattern ((~once :variance-keyword) ...)])

  (define-syntax-class static-combinator-form
    #:attributes (name)
    [pattern (name:id pos:argument-description ... . (~or () rest:argument-description))]))

(define-syntax (combinator-structs stx)
  (syntax-parse stx
    [(_ (struct-name:id sc:static-combinator-form c:contract-form kind:id) ...)
     #`(begin
         (begin
           (struct struct-name kind ()
                   #:methods gen:sc-mapable [(define sc-map (combinator-map struct-name))]
                   #:property prop:combinator-name (symbol->string 'sc.name))
           (define sc.name (c.fun struct-name))) ...)]))
(combinator-structs
  (or-combinator (or/sc . (#:covariant)) #:list or/c flat-combinator)
  (and-combinator (and/sc . (#:covariant)) #:list and/c flat-combinator)
  (list/c-combinator (list/sc . (#:covariant)) #:list list/c flat-combinator)
  (listof-combinator (listof/sc (#:covariant)) #:single listof flat-combinator)
  (cons-combinator (cons/sc (#:covariant) (#:covariant)) #:double cons/c flat-combinator)
  ;; TODO add chaperone restrict
  (set-combinator (set/sc (#:covariant)) #:single set/c flat-combinator))


;; Struct Definitions
(struct any-combinator simple-contract ()
        #:methods gen:custom-write [(define write-proc any-write-proc)])
(struct vector/c-combinator chaperone-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map vector/c-combinator))]
        #:property prop:combinator-name "vector/sc")
(struct vectorof-combinator chaperone-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map vectorof-combinator))]
        #:property prop:combinator-name "vectorof/sc")
(struct promise-combinator chaperone-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map promise-combinator))]
        #:property prop:combinator-name "promise/sc")
(struct syntax-combinator chaperone-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map syntax-combinator))]
        #:property prop:combinator-name "syntax/sc")
(struct hash-combinator chaperone-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map hash-combinator))]
        #:property prop:combinator-name "hash/sc")
(struct box-combinator impersonator-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map box-combinator))]
        #:property prop:combinator-name "box/sc")
(struct parameter-combinator impersonator-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map parameter-combinator))]
        #:property prop:combinator-name "parameter/sc")
(struct sequence-combinator impersonator-combinator ()
        #:methods gen:sc-mapable [(define sc-map (combinator-map sequence-combinator))]
        #:property prop:combinator-name "sequence/sc")
(struct struct-combinator chaperone-combinator ())
(struct continuation-mark-key-combinator chaperone-combinator ())
(struct prompt-tag-combinator chaperone-combinator ())
(struct parametric-combinator flat-combinator ())
(struct function-combinator chaperone-combinator ())
(struct case->-combinator chaperone-combinator ())
(struct arr-combinator chaperone-combinator ())


;; Combinators
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
(define (syntax/sc/raw sc)
  (syntax-combinator (app #'syntax/c)
    (list sc)))

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


;; Match Expanders
;;
(define-syntax single-matchers
  (syntax-parser
    [(_ (name:id struct-name:id) ...)
     #'(begin
         (define-match-expander name
           (syntax-parser
             [(_ ctc)
              #'(struct-name _ (list ctc))])) ...)]))

(define-syntax double-matchers
  (syntax-parser
    [(_ (name:id struct-name:id) ...)
     #'(begin
         (define-match-expander name
           (syntax-parser
             [(_ ctc1 ctc2)
              #'(struct-name _ (list ctc1 ctc2))])) ...)]))

(define-syntax multiple-matchers
  (syntax-parser
    [(_ (name:id struct-name:id) ...)
     #'(begin
         (define-match-expander name
           (syntax-parser
             [(_ ctc (... ...))
              #'(struct-name _ (list ctc (... ...)))])) ...)]))

(single-matchers
  (listof/sc: listof-combinator)
  (vectorof/sc: vectorof-combinator)
  (set/sc: set-combinator)
  (box/sc: box-combinator)
  (syntax/sc: syntax-combinator)
  (promise/sc: promise-combinator))
(double-matchers
  (hash/sc: hash-combinator))
(multiple-matchers
  (list/sc: list-combinator)
  (vector/sc: vector-combinator)
  (sequence/sc: sequence-combinator))



(define-match-expander any/sc:
  (syntax-parser
    [(_) #'(any-combinator _ _)]))


