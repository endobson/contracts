#lang racket/base

(require "../structures.rkt" "../constraints.rkt"
         racket/list racket/match
         unstable/contract
         (except-in racket/contract recursive-contract)
         (for-template racket/base racket/class)
         (for-syntax racket/base syntax/parse))

(provide
  (contract-out
    [object/sc ((listof object-member-spec?) . -> . static-contract?)]
    [class/sc ((listof member-spec?) boolean? (listof identifier?) (listof identifier?) . -> . static-contract?)]))



(struct member-spec (modifier id sc) #:transparent)

(define field-modifiers '(field init init-field inherit-field))
(define method-modifiers '(method inherit super inner override augment augride))

(struct object-combinator combinator ()
  #:transparent
  #:property prop:combinator-name "object/sc"
  #:methods gen:sc
    [(define (sc-map v f)
       (object-combinator (member-seq-sc-map f (combinator-args v))))
     (define (sc->contract v f)
       (object/sc->contract v f))
     (define (sc->constraints v f)
       (merge-restricts* 'impersonator (map f (member-seq->list (combinator-args v)))))])

(struct class-combinator combinator (opaque absent-fields absent-methods)
  #:transparent
  #:property prop:combinator-name "class/sc"
  #:methods gen:sc
    [(define (sc-map v f)
       (class-combinator (member-seq-sc-map f (combinator-args v))))
     (define (sc->contract v f)
       (class/sc->contract v f))
     (define (sc->constraints v f)
       (merge-restricts* 'impersonator (map f (member-seq->list (combinator-args v)))))])


(define (member-seq->list seq)
  (match-lambda
    [(member-seq vals) 
     (filter-map member-spec-sc vals)]))

(struct member-seq (vals)
   #:property prop:sequence member-seq->list)

(define (member-seq-sc-map f seq)
  (match seq
    [(member-seq vals)
     (member-seq
       (for/list ([v (in-list vals)])
          (match v
            [(member-spec mod id sc)
             (member-spec mod id (and sc (f sc 'invariant)))])))]))

;; TODO make this the correct subset
(define object-member-spec? member-spec?)

(define (object/sc specs)
  (object-combinator (member-seq specs)))
(define (class/sc specs opaque absent-fields absent-methods)
  (object-combinator (member-seq specs) opaque absent-fields absent-methods))

(define (wrap mod ctc)
  (define mod-stx
    (case mod
     [(method) #f]
     [(field) #'field]
     [(init) #'init]
     [(init-field) #'init-field]
     [(inherit) #'inherit]
     [(inherit-field) #'inherit-field]
     [(super) #'super]
     [(inner) #'inner]
     [(override) #'override]
     [(augment) #'augment]
     [(augride) #'augride]))
  (if mod-stx #`(#,mod-stx #,ctc) ctc))

(define (member-spec->form v f)
  (match v
    [(member-spec modifier id sc)
     (with-syntax ([ctc-stx (and sc (f sc) empty)]
                   [id-stx id])
        (wrap modifier (if sc #`(#,id #,(f sc)) id)))]))

(define (object/sc->contract v f) 
  (match v
   [(object-combinator (member-seq vals))
    #`(object/sc #,(map member-spec->form vals))]))
(define (class/sc->contract v f) 
  (match v
   [(class-combinator (member-seq vals) opaque absent-fields absent-methods)
    #`(class/sc #,@(if opaque (list '#:opaque) empty)
                #,(map member-spec->form vals)
                (absent #,@absent-methods (field #,@absent-fields)))]))
