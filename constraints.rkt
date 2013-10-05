#lang racket/base

(require
  racket/match
  racket/list
  racket/dict
  racket/set
  syntax/id-table
  "kinds.rkt"
  "equations.rkt")

(provide
  simple-contract-restrict
  variable-contract-restrict
  merge-restricts*
  merge-restricts
  add-constraint
  close-loop
  
  
  contract-restrict?
  )

(module structs racket/base
  (require racket/contract
           racket/set
           syntax/id-table
           "kinds.rkt")
  (provide
    (contract-out
      [struct constraint ([value kind-max?] [max contract-kind?])]
      [struct kind-max ([variables free-id-table?] [max contract-kind?])]
      [struct contract-restrict ([value kind-max?] [constraints (set/c constraint?)])]))

  (struct constraint (value max) #:transparent)
  (struct kind-max (variables max) #:transparent)
  (struct contract-restrict (value constraints) #:transparent))
(require 'structs)

(define (free-id-set . elems)
  (for/fold ([table (make-immutable-free-id-table)])
            ([e (in-list elems)])
    (dict-set table e #t)))

(define (free-id-set-union tables)
  (for*/fold ([table (make-immutable-free-id-table)])
             ([new-table (in-list tables)]
              [(k _) (in-dict new-table)])
    (dict-set table k #t)))

(define (simple-contract-restrict kind)
  (contract-restrict (kind-max (free-id-set) kind) (set)))
(define (variable-contract-restrict var)
  (contract-restrict (kind-max (free-id-set var) 'flat) (set)))


(define (add-constraint cr max) 
  (match cr
    [(contract-restrict v constraints)
     (contract-restrict v (set-add constraints (constraint v max)))]))

(define (merge-restricts* min  crs)
  (apply merge-restricts min crs))

(define (merge-restricts min . crs)
  (match crs
    [(list (contract-restrict vs constraints) ...)
     (contract-restrict (merge-kind-maxes min vs) (apply set-union (set) constraints))]))

(define (merge-kind-maxes min-kind vs)
  (match vs
    [(list (kind-max variables maxes) ...)
     (kind-max (free-id-set-union variables) (apply combine-kinds min-kind maxes))]))

(define (close-loop names crs)
  (define eqs (make-equation-set))
  (define vars
    (for*/hash ((name (in-list names)))
      (values name 
              (add-variable! eqs (kind-max (free-id-set) 'flat)))))
  (define (lookup-id name)
    (variable-ref (hash-ref vars name)))

  (for ([name names] [cr crs])
    (add-equation! eqs
      (hash-ref vars name)
      (lambda ()
        (match cr
          [(contract-restrict (kind-max ids max) _)
           (define-values (bound-ids unbound-ids)
             (partition (lambda (id) (member id names)) (dict-keys ids)))
           (merge-kind-maxes 'flat (list*
                                     (kind-max (apply free-id-set unbound-ids) max)
                                     (map lookup-id (cons name bound-ids))))]))))
  (define var-values (resolve-equations eqs))
  (for/hash (((name var) vars))
    (values name (hash-ref var-values var))))
