#lang racket/base

(require
  racket/function
  racket/match
  racket/list
  syntax/id-table
  racket/sequence
  "kinds.rkt"
  "structures.rkt"
  "equations.rkt")
(require (prefix-in c: racket/contract))

(provide instantiate)

(struct constraint (value max))
(struct kind-max (variables max))
(struct contract-restrict (value constraints))


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
  


(define (instantiate sc)
  (instantiate/inner sc (compute-recursive-kinds (find-recursive sc))))

(define (find-recursive sc)
  (define (recur sc acc)
    (match sc
      [(recursive-contract-use _) acc]
      [(recursive-contract names values body)
       (for/fold ((acc (cons sc acc))) ((arg (cons body values)))
         (recur arg acc))]
      [(combinator args)
       (for/fold ((acc acc)) ((arg args))
         (recur arg acc))]
      [(restrict body) (recur body acc)]))
  (recur sc null))

(define (compute-recursive-kinds parts)
  (define eqs (make-equation-set))
  (define vars
    (for*/hash ((part parts)
                (name (recursive-contract-names part)))
      (values name 
              (add-variable! eqs 'flat))))
  (define (get-kind sc)
    (match sc
      [(simple-contract _ _ kind) (thunk kind)]
      [(recursive-contract-use name)
       (thunk (variable-ref (hash-ref vars name)))]
      [(recursive-contract names values body)
       (get-kind body)]
      [(flat-combinator args)
       (define kinds (map get-kind args))
       (thunk (apply combine-kinds (map (lambda (f) (f)) kinds)))]
      [(chaperone-combinator args)
       (define kinds (map get-kind args))
       (thunk (apply combine-kinds (cons 'chaperone (map (lambda (f) (f)) kinds))))]
      [(impersonator-combinator args)
       (thunk 'impersonator)]
      [(flat-restrict body)
       (define kind-thunk (get-kind body))
       (thunk
         (define kind (kind-thunk))
         (unless (contract-kind< kind 'flat)
           (error 'instantiate "Cannot convert to regular contract"))
         kind)]
      [(chaperone-restrict body)
       (define kind-thunk (get-kind body))
       (thunk
         (define kind (kind-thunk))
         (unless (contract-kind< kind 'chaperone)
           (error 'instantiate "Cannot convert to regular contract"))
         kind)]
      ))
  (for ([part parts])
    (for ([name (recursive-contract-names part)]
          [value (recursive-contract-values part)])
      (add-equation! eqs
        (hash-ref vars name)
        (get-kind value))))
  (define var-values (resolve-equations eqs))
  (for/hash (((name var) vars))
    (values name (hash-ref var-values var))))
    
(define (instantiate/inner sc recursive-kinds)
  (define (recur sc)
    (match sc
      [(recursive-contract names values body)
       (define bindings
         (for/list ([name names] [value values])
            #`[#,name (c:recursive-contract #,(recur value) 
                                            #,(kind->keyword
                                                (hash-ref recursive-kinds name)))]))
       #`(letrec #,bindings #,(recur body))]
      [(? sc-contract? sc)
       (sc->contract sc recur)]))
  (recur sc))
