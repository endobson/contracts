#lang racket/base

(require "structures.rkt" racket/list
         racket/match
         (for-syntax racket/base racket/syntax syntax/parse))

;; for syntax
(require racket/set
         unstable/contract
         (except-in racket/contract recursive-contract))

(provide (except-out (all-defined-out) function/sc)
  (contract-out
    [function/sc (-> (listof static-contract?)
                     (listof static-contract?)
                     (listof (list/c keyword? static-contract?))
                     (listof (list/c keyword? static-contract?))
                     (or/c #f static-contract?)
                     (or/c #f (listof static-contract?))
                     static-contract?)]))


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
                                              (f a 'covariant)))]))
(define-syntax-rule (combinator-map constructor)
  (combinator-map* (lambda (stx args) (constructor stx args))))

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
    #:attributes (name combinator matcher)
    [pattern (name:id pos:argument-description ... )
             #:with matcher-name (format-id #'name "~a:" (syntax-e #'name))
             #:attr combinator
               #'(λ (constructor ctc) (λ (pos.name ...) (constructor (app ctc) (list pos.restricted-name ...))))
             #:attr matcher
               (λ (struct-name)
                 #`(define-match-expander matcher-name
                     (syntax-parser
                       [(_ pos.name ...)
                        #'(#,struct-name _ (list pos.name ...))])))]
    [pattern (name:id . rest:argument-description)
             #:with matcher-name (format-id #'name "~a:" (syntax-e #'name))
             #:attr combinator
               #'(λ (constructor ctc) (λ args (constructor (app ctc) args)))
             #:attr matcher
               (λ (struct-name)
                 #`(define-match-expander matcher-name
                     (syntax-parser
                      [(_ ctc (... ...))
                       #'(#,struct-name _ (list ctc (... ...)))])))]))



(define-syntax (combinator-struct stx)
  (syntax-parse stx
    [(_ sc:static-combinator-form c:expr kind:contract-category-keyword)
     #`(begin
         (struct struct-name kind.struct ()
                 #:methods gen:sc-mapable [(define sc-map (combinator-map struct-name))]
                 #:property prop:combinator-name (symbol->string 'sc.name))
         #,((attribute sc.matcher) #'struct-name)
         (define sc.name (sc.combinator struct-name c)))]))


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
  ;; TODO add chaperone restrict
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
(struct any-combinator simple-contract ()
        #:methods gen:custom-write [(define write-proc any-write-proc)])
(struct struct-combinator chaperone-combinator ())
(struct continuation-mark-key-combinator chaperone-combinator ())
(struct prompt-tag-combinator chaperone-combinator ())
(struct parametric-combinator flat-combinator ())
(struct function-combinator chaperone-combinator (indices mand-kws opt-kws)
        #:property prop:combinator-name "->/sc"
        #:methods gen:equal+hash [(define (equal-proc a b recur) (function-sc-equal? a b recur))
                                  (define (hash-proc v recur) (function-sc-hash v recur))
                                  (define (hash2-proc v recur) (function-sc-hash2 v recur))]
        #:methods gen:sc-mapable [(define (sc-map v f) (function-sc-map v f))])
(struct case->-combinator chaperone-combinator ())
(struct arr-combinator chaperone-combinator ())


;; Combinators
(define (flat/sc ctc) (simple-contract ctc 'flat))
(define (chaperone/sc ctc) (simple-contract ctc 'chaperone))
(define (impersonator/sc ctc) (simple-contract ctc 'impersonator))

(define continuation-mark-key/sc
  (combine continuation-mark-key-combinator #'continuation-mark-key/c))

(define (prompt-tag/sc* scs call/cc-sc)
  (prompt-tag-combinator
    (λ (call/cc-ctc . others)
       #`(prompt-tag/c #,@others #:call/cc call/cc-ctc)
       (cons call/cc-sc scs))))

(define (object/sc* methods) (error 'nyi))
(define (class/sc* methods) (error 'nyi))


(define any/sc (any-combinator #'any/c 'flat))
(define identifier/sc (flat/sc #'identifier?))



(define (split-function-args ctcs mand-args-end opt-args-end
                    mand-kw-args-end opt-kw-args-end rest-end range-end)
  (values
    (drop (take ctcs mand-args-end) 0)
    (drop (take ctcs opt-args-end) mand-args-end)
    (drop (take ctcs mand-kw-args-end) opt-args-end)
    (drop (take ctcs opt-kw-args-end) mand-kw-args-end)
    (and (> rest-end opt-kw-args-end)
         (first (drop (take ctcs rest-end) opt-kw-args-end)))
    (and range-end (drop (take ctcs range-end) rest-end))))

(define (function/sc mand-args opt-args mand-kw-args opt-kw-args rest range)
  (define mand-args-end (length mand-args))
  (define opt-args-end (+ mand-args-end (length opt-args)))
  (define mand-kw-args-end (+ opt-args-end (length mand-kw-args)))
  (define opt-kw-args-end (+ mand-kw-args-end (length opt-kw-args)))
  (define rest-end (if rest (add1 opt-kw-args-end) opt-kw-args-end))
  (define range-end (and range (+ rest-end (length range))))
  (define mand-kws (map first mand-kw-args))
  (define opt-kws (map first opt-kw-args))
  (define end-indices
    (list mand-args-end opt-args-end mand-kw-args-end opt-kw-args-end rest-end range-end))

  (function-combinator
    (lambda ctcs
      (define-values (mand-ctcs opt-ctcs mand-kw-ctcs opt-kw-ctcs rest-ctc range-ctcs)
        (split-function-args ctcs end-indices))

      (define mand-kws-stx (append-map list mand-kws mand-kw-ctcs))
      (define opt-kws-stx (append-map list opt-kws opt-kw-ctcs))
      (define rest-ctc-stx
        (if rest-ctc
          (list '#:rest rest-ctc)
          #'()))

      (define range-ctc
        (if range-ctcs
          #`(values #,@range-ctcs)
          #'any))


      #`((#,@mand-ctcs #,@mand-kws-stx)
         (#,@opt-ctcs #,@opt-kws-stx) 
         #,@rest-ctc-stx
         . ->* . #,range-ctc))
    (append
      mand-args
      opt-args
      (map second mand-kw-args)
      (map second opt-kw-args)
      (if rest (list rest) null)
      (or range null))
    end-indices
    mand-kws
    opt-kws))


(define-match-expander ->/sc:
  (syntax-parser
    [(_ mand-args opt-args mand-kw-args opt-kw-args rest range)
     #'(and (? function-combinator?)
            (app (match-lambda
                   [(function-combinator stx args indices mand-kws opt-kws)
                    (define-values (mand-args* opt-args* mand-kw-args* opt-kw-args* rest* range*)
                      (apply split-function-args args indices))
                    (list
                      mand-args* opt-args*
                      (map list mand-kws mand-kw-args*)
                      (map list opt-kws opt-kw-args*)
                      rest*
                      range*)])
                 (list mand-args opt-args mand-kw-args opt-kw-args rest range)))]))


(define (function-sc-map v f)
  (match-define (function-combinator stx args indices mand-kws opt-kws) v) 

  (define-values (mand-args opt-args mand-kw-args opt-kw-args rest-arg range-args)
    (apply split-function-args args indices))

  (define new-args
    (append 
      (map (lambda (arg) (f arg 'contravariant))
           (append mand-args opt-args mand-kw-args opt-kw-args (if rest-arg (list rest-arg) null)))
      (if range-args
          (map (lambda (arg) (f arg 'covariant))
               range-args)
          empty)))
        

  (function-combinator stx new-args indices mand-kws opt-kws))

(define (function-sc-equal? a b recur)
  (match-define (function-combinator a-stx a-args a-indices a-mand-kws a-opt-kws) a) 
  (match-define (function-combinator b-stx b-args b-indices b-mand-kws b-opt-kws) b) 
  (and
    (recur a-indices b-indices)
    (recur a-mand-kws b-mand-kws)
    (recur a-opt-kws b-opt-kws)
    (recur a-args b-args)))

(define (function-sc-hash v recur)
  (match-define (function-combinator a-stx v-args v-indices v-mand-kws v-opt-kws) v) 
  (+ (recur v-indices) (recur v-mand-kws) (recur v-opt-kws) (recur v-args)))

(define (function-sc-hash2 v recur)
  (match-define (function-combinator a-stx v-args v-indices v-mand-kws v-opt-kws) v) 
  (+ (recur v-indices) (recur v-mand-kws) (recur v-opt-kws) (recur v-args)))


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



(define-match-expander any/sc:
  (syntax-parser
    [(_) #'(any-combinator _ _)]))


