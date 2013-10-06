#lang racket/base

(require
  racket/function
  racket/match
  racket/dict
  racket/sequence
  (for-template racket/base (prefix-in c: racket/contract))
  "kinds.rkt"
  "structures.rkt"
  "constraints.rkt"
  "equations.rkt")
(require (prefix-in c: racket/contract))

(provide instantiate)



(define (instantiate sc)
  (instantiate/inner sc (compute-recursive-kinds (contract-restrict-recursive-values (compute-constraints sc)))))

(define (compute-constraints sc)
  (define (recur sc)
    (match sc
      [(recursive-contract names values body)
       (close-loop names (map recur values) (recur body)) ]
      [(? sc?)
       (sc->constraints sc recur)]))
  (define constraints (recur sc))
  (validate-constraints constraints)
  constraints)


(define (compute-recursive-kinds recursives)
  (define eqs (make-equation-set))
  (define vars
    (for/hash ([(name _) (in-dict recursives)])
      (values name (add-variable! eqs 'flat))))

  (define (lookup id)
    (variable-ref (hash-ref vars id)))

  (for ([(name v) (in-dict recursives)])
    (match v
      [(kind-max others max)
       (add-equation! eqs
          (hash-ref vars name)
          (lambda ()
            (apply combine-kinds max (map lookup (dict-keys others)))))]))
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
      [(? sc? sc)
       (sc->contract sc recur)]))
  (recur sc))
