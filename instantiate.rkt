#lang racket/base

(require
  racket/function
  racket/match
  "kinds.rkt"
  "structures.rkt"
  "equations.rkt")



(define (instantiate sc)
  (instantiate/inner sc (compute-recursive-kinds (find-recursive sc))))

(define (find-recursive sc)
  (define (recur sc acc)
    (match sc
      ((simple-contract _ _) acc)
      ((recursive-contract-use _) acc)
      ((recursive-contract name body) (recur body (cons sc acc)))
      ((combinator _ args)
       (for/fold ((acc acc)) ((arg args))
         (recur arg acc)))))
  (recur sc null))

(define (compute-recursive-kinds parts)
  (define eqs (make-equation-set))
  (define vars
    (for/hash ((part parts))
      (values (recursive-contract-name part)
              (add-variable! eqs 'flat))))
  (define (get-kind sc)
    (match sc
      ((simple-contract _ kind) (thunk kind))
      ((or (recursive-contract-use name) (recursive-contract name _))
       (define var (hash-ref vars name))
       (thunk (variable-ref var)))
      ((flat-combinator _ args)
       (define kinds (map get-kind args))
       (thunk (combine-kinds (map (lambda (f) (f)) kinds))))
      ((chaperone-combinator _ args)
       (define kinds (map get-kind args))
       (thunk (combine-kinds (cons 'chaperone (map (lambda (f) (f)) kinds)))))
      ((impersonator-combinator _ args)
       (thunk 'impersonator))))

  (for ((part parts))
    (add-equation! eqs
      (hash-ref vars (recursive-contract-name part))
      (get-kind part)))
  (define values (resolve-equations eqs))
  (for/hash (((name var) vars))
    (values name (hash-ref values var))))
    
(define (instantiate/inner sc recursive-kinds)
  (define (recur sc)
    (match sc
      ((simple-contract stx _) stx)
      ((recursive-contract-use stx) stx)
      ((recursive-contract name body)
       (define kind (hash-ref recursive-kinds name))
       #`(letrec ((name (recursive-contract #,(recur body) #,(kind->keyword kind))))
           name))
      ((combinator make-stx args)
       (apply make-stx (map recur args)))))
  (recur sc))
