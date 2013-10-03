#lang racket/base

(require
  racket/match
  racket/list
  syntax/id-table
  "kinds.rkt"
  "equations.rkt")

(provide
  simple-contract-restrict
  merge-restricts
  
  
  )


(struct constraint (value max))
(struct kind-max (variables max))
(struct contract-restrict (value constraints))

(define (simple-contract-restrict kind) (contract-restrict (kind-max empty kind) empty))


(define (add-constraint cr max) 
  (match cr
    [(contract-restrict v constraints)
     (contract-restrict v (cons (constraint v max) constraints))]))

(define (merge-restricts* min  crs)
  (apply merge-restricts min crs))

(define (merge-restricts min . crs)
  (match crs
    [(list (contract-restrict vs constraints) ...)
     (contract-restrict (merge-kind-maxes min vs) (append* constraints))]))

(define (merge-kind-maxes min-kind vs)
  (match vs
    [(list (kind-max variables maxes) ...)
     (kind-max (append* variables) (apply combine-kinds min-kind maxes))]))

(define (close-loop names crs)
  (define eqs (make-equation-set))
  (define vars
    (for*/hash ((name (in-list names)))
      (values name 
              (add-variable! eqs (kind-max empty 'flat)))))
  (define (lookup-id name)
    (variable-ref (hash-ref vars name)))

  (for ([name names] [cr crs])
    (add-equation! eqs
      (hash-ref vars name)
      (lambda ()
        (match cr
          [(contract-restrict (kind-max ids max) _)
           (define-values (bound-ids unbound-ids)
             (partition ids (lambda (id) (member id names))))
           (merge-kind-maxes 'flat (list*
                                     (kind-max unbound-ids max)
                                     (map lookup-id (cons name bound-ids))))]))))

  (define var-values (resolve-equations eqs))
  (for/hash (((name var) vars))
    (values name (hash-ref var-values var))))
