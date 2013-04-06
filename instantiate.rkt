#lang racket/base

(require
  racket/function
  racket/match
  "kinds.rkt"
  "structures.rkt"
  "equations.rkt")

(provide instantiate)

(define (instantiate sc)
  (instantiate/inner sc (compute-recursive-kinds (find-recursive sc))))

(define (find-recursive sc)
  (define (recur sc acc)
    (match sc
      ((simple-contract _ _) acc)
      ((recursive-contract-use _) acc)
      ((recursive-contract names values body)
       (for/fold ((acc (cons sc acc))) ((arg (cons body values)))
         (recur arg acc)))
      ((combinator _ args)
       (for/fold ((acc acc)) ((arg args))
         (recur arg acc)))))
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
      [(simple-contract _ kind) (thunk kind)]
      [(recursive-contract-use name)
       (thunk (variable-ref (hash-ref vars name)))]
      [(recursive-contract names values body)
       (get-kind body)]
      [(flat-combinator _ args)
       (define kinds (map get-kind args))
       (thunk (combine-kinds (map (lambda (f) (f)) kinds)))]
      [(chaperone-combinator _ args)
       (define kinds (map get-kind args))
       (thunk (combine-kinds (cons 'chaperone (map (lambda (f) (f)) kinds))))]
      [(impersonator-combinator _ args)
       (thunk 'impersonator)]))
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
      [(simple-contract stx _) stx]
      [(recursive-contract-use stx) stx]
      [(recursive-contract names values body)
       (define bindings
         (for/list ([name names] [value values])
            #`[#,name (recursive-contract #,(recur value) 
                                          #,(kind->keyword
                                              (hash-ref recursive-kinds name)))]))
       #`(letrec #,bindings #,(recur body))]
      [(combinator make-stx args)
       (apply make-stx (map recur args))]))
  (recur sc))
