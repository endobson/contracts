#lang racket

(require
 typed-racket/utils/utils
 syntax/parse
 (rep type-rep filter-rep object-rep)
 (typecheck internal-forms)
 (utils tc-utils require-contract)
 (env type-name-env)
 (types resolve utils)
 (prefix-in t: (types abbrev numeric-tower))
 (private parse-type)
 racket/match unstable/match syntax/struct syntax/stx racket/syntax racket/list
 (only-in racket/contract -> ->* case-> cons/c flat-rec-contract provide/contract any/c)
 (for-template racket/base racket/contract racket/set (utils any-wrap)
               (prefix-in t: (types numeric-predicates))
               (only-in unstable/contract sequence/c)))

(require "structures.rkt" "combinators.rkt")

(define any-wrap/sc (simple-contract #'any-wrap/c 'impersonator))

(define (no-duplicates l)
  (= (length l) (length (remove-duplicates l))))


(define (type->static-contract type fail #:out (out? #f) #:from-typed? (from-typed? #f))

  (let loop ([type type] [pos? #t] [from-typed? from-typed?] [recursive-values (hash)])
    (define (t->sc t #:recursive-values (recursive-values recursive-values))
      (loop t pos? from-typed? recursive-values))
    (define (t->sc/neg t #:recursive-values (recursive-values recursive-values))
      (loop t (not pos?) (not from-typed?) recursive-values))
    (define (t->sc/method t) (t->sc/function t fail out? pos? from-typed? recursive-values loop #t))
    (define (t->sc/fun t) (t->sc/function t fail out? pos? from-typed? recursive-values loop #f))
    (match type
      [(or (App: _ _ _) (Name: _)) (t->sc (resolve-once type))]
      [(Univ:) (if from-typed? any-wrap/sc any/sc)]
      [(Mu: var (Union: (list (Value: '()) (Pair: elem-ty (F: var)))))
       (listof/sc (t->sc elem-ty))]
      [t (=> fail) (or (numeric-type->static-contract t) (fail))]
      [(Base: sym cnt _ _ _)
       (flat/sc #`(flat-named-contract '#,sym (flat-contract-predicate #,cnt)))]
      [(Refinement: par p? cert)
       (and/sc (t->sc par) (flat/sc (cert p?)))]
      [(Union: elems)
       (let-values ([(vars notvars) (partition F? elems)])
         (when (>= (length vars) 1) (exit (fail)))
         (or/sc* (append (map t->sc vars) (map t->sc notvars))))]
      [(and t (Function: _)) (t->sc/fun t)]
      [(Set: t) (set/sc (t->sc t))]
      [(Sequence: ts) (sequence/sc (map t->sc ts))]
      [(Vector: t) (vectorof/sc (t->sc t))]
      [(HeterogeneousVector: ts) (vector/sc* (map t->sc ts))]
      [(Box: t) (box/sc (t->sc t))]
      [(Pair: t1 t2)
       (cons/sc (t->sc t1) (t->sc t2))]
      [(Promise: t)
       (promise/sc (t->sc t))]
      [(Opaque: p? cert)
       (flat/sc #`(flat-named-contract (quote #,(syntax-e p?)) #,(cert p?)))]
      [(Continuation-Mark-Keyof: t)
       (continuation-mark-key/sc (t->sc t))]
      ;; TODO: this is not quite right for case->
      [(Prompt-Tagof: s (Function: (list (arr: (list ts ...) _ _ _ _))))
       (prompt-tag/sc* (map t->sc ts) (t->sc s))]
      ;; TODO
      [(F: v)
       (cond [(assoc v recursive-values) => second]
             [else (int-err "unknown var: ~a" v)])]
      [(Poly: vs b)
       (if from-typed?
           ;; in positive position, no checking needed for the variables
           (let ((recursive-values (for/fold ([rv recursive-values]) ([v vs])
                                     (hash-set rv v any/sc))))
             (t->sc b #:recursive-values recursive-values))
           (error 'nyi)
           ;; in negative position, use `parameteric/c'
           #;
           (match-let ([(Poly-names: vs-nm _) ty])
             (with-syntax ([(v ...) (generate-temporaries vs-nm)])
               (parameterize ([vars (append (map list vs (syntax->list #'(v ...)))
                                            (vars))])
                 (parametric->/sc (v ...) #,(t->c b))))))]
      [(Mu: n b)
       (define n* (generate-temporary n))
       (recursive-contract
         n*
         (t->sc b #:recursive-values (hash-set recursive-values n (recursive-contract-use n*))))]
      [(Value: #f) false/sc]
      [(Instance: (? Mu? t))
       (t->sc (make-Instance (resolve-once t)))]
      [(Instance: (Class: _ _ (list (list names functions) ...)))
       (object/sc* (map list names (map t->sc/method functions)))]
      ;; init args not currently handled by class/c
      [(Class: _ (list (list by-name-inits by-name-init-tys _) ...) (list (list names functions) ...))
       (class/sc* (map list names (map t->sc/method functions))
                  (map list by-name-inits (map t->sc/neg by-name-init-tys)))]
      [(Value: '()) empty/sc]
      #; ;TODO
      [(Struct: nm par (list (fld: flds acc-ids mut?) ...) proc poly? pred?)
       (cond
         [(assf (λ (t) (type-equal? t ty)) structs-seen)
          =>
          cdr]
         [proc (exit (fail))]
         [(and (equal? kind flat-sym) (ormap values mut?))
          (exit (fail))]
         [poly?
          (with-syntax* ([struct-ctc (generate-temporary 'struct-ctc)])
            (define field-contracts
              (for/list ([fty flds] [mut? mut?])
                (with-syntax* ([rec (generate-temporary 'rec)])
                  (define required-recursive-kind
                     (contract-kind-min kind (if mut? impersonator-sym chaperone-sym)))
                  ;(printf "kind: ~a mut-k: ~a req-rec-kind: ~a\n"
                  ;        kind (if mut? impersonator-sym chaperone-sym) required-recursive-kind)
                  (parameterize ((current-contract-kind (contract-kind-min kind chaperone-sym)))
                    (let ((fld-ctc (t->c fty #:seen (cons (cons ty #'rec) structs-seen)
                                         #:kind required-recursive-kind)))
                      #`(let ((rec (recursive-contract
                                     struct-ctc #,(contract-kind->keyword (current-contract-kind)))))
                          #,fld-ctc))))))
            #`(letrec ((struct-ctc (struct/c #,nm #,@field-contracts))) struct-ctc))]
         [else #`(flat-named-contract '#,(syntax-e pred?) #,pred?)])]
      [(Syntax: (Base: 'Symbol _ _ _ _)) identifier/sc]
      [(Syntax: t)
       (syntax/sc (t->sc t))]
      [(Value: v)
       (flat/sc #`(flat-named-contract #,(format "~a" v) (lambda (x) (equal? x '#,v))))]
      ;; TODO Is this sound?
      [(Param: in out) 
       (parameter/sc (t->sc in) (t->sc out))]
      [(Hashtable: k v)
       (hash/sc (t->sc k) (t->sc v))]
      [else
       (exit (fail))])))

(define (t->sc/function f fail out? pos? from-typed? recursive-values loop method?)
  (define (t->sc t #:recursive-values (recursive-values recursive-values))
    (loop t pos? from-typed? recursive-values))
  (define (t->sc/neg t #:recursive-values (recursive-values recursive-values))
    (loop t (not pos?) (not from-typed?) recursive-values))
  (match f
    [(Function: (list (top-arr:))) (if pos? #'(case->) #'procedure?)]
    [(Function: arrs)
     ;; Try to generate a single `->*' contract if possible.
     ;; This allows contracts to be generated for functions with both optional and keyword args.
     ;; (and don't otherwise require full `case->')
     (define conv (match-lambda [(Keyword: kw kty _) (list kw (t->sc/neg kty))]))
     (define (partition-kws kws) (partition (match-lambda [(Keyword: _ _ mand?) mand?]) kws))
     (define (process-dom dom*)  (if method? (cons any/sc dom*) dom*))
     (cond
      ;; To generate a single `->*', everything must be the same for all arrs, except for positional
      ;; arguments which can increase by at most one each time.
      ;; Note: optional arguments can only increase by 1 each time, to avoid problems with
      ;;  functions that take, e.g., either 2 or 6 arguments. These functions shouldn't match,
      ;;  since this code would generate contracts that accept any number of arguments between
      ;;  2 and 6, which is wrong.
      ;; TODO sufficient condition, but may not be necessary
      [(and
        (> (length arrs) 1)
        ;; Keyword args, range and rest specs all the same.
        (let* ([xs (map (match-lambda [(arr: _ rng rest-spec _ kws)
                                       (list rng rest-spec kws)])
                        arrs)]
               [first-x (first xs)])
          (for/and ([x (in-list (rest xs))])
            (equal? x first-x)))
        ;; Positionals are monotonically increasing by at most one.
        (let-values ([(_ ok?)
                      (for/fold ([positionals (arr-dom (first arrs))]
                                 [ok-so-far?  #t])
                          ([arr (in-list (rest arrs))])
                        (match arr
                          [(arr: dom _ _ _ _)
                           (define ldom         (length dom))
                           (define lpositionals (length positionals))
                           (values dom
                                   (and ok-so-far?
                                        (or (= ldom lpositionals)
                                            (= ldom (add1 lpositionals)))
                                        (equal? positionals (take dom lpositionals))))]))])
          ok?))
       (match* ((first arrs) (last arrs))
         [((arr: first-dom (Values: (list (Result: rngs (FilterSet: (Top:) (Top:)) (Empty:)) ...)) rst #f kws)
           (arr: last-dom _ _ _ _)) ; all but dom is the same for all
          (define mand-args (map t->sc/neg first-dom))
          (define opt-args (map t->sc/neg (drop last-dom (length first-dom))))
          (define-values (mand-kws opt-kws)
            (let*-values ([(mand-kws opt-kws) (partition-kws kws)])
              (values (map conv mand-kws)
                      (map conv opt-kws))))
          (define range (map t->sc rngs))
          (define rest (and rst (listof/sc (t->sc/neg rest))))
          (function/sc mand-args opt-args mand-kws opt-kws rest range)])]
      [else
       (define ((f [case-> #f]) a)
         (define (convert-arr arr)
           (match arr
             [(arr: dom (Values: (list (Result: rngs _ _) ...)) rst #f kws)
              (let-values ([(mand-kws opt-kws) (partition-kws kws)])
                ;; Garr, I hate case->!
                (when (and (pair? opt-kws) case->)
                  (exit (fail)))
                (function/sc
                  (map t->sc/neg dom)
                  null
                  (map conv mand-kws)
                  (map conv opt-kws)
                  (and rst (t->sc/neg rst))
                  (map t->sc rngs)))]))
         (match a
           ;; functions with no filters or objects
           [(arr: dom (Values: (list (Result: rngs (FilterSet: (Top:) (Top:)) (Empty:)) ...)) rst #f kws)
            (convert-arr a)]
           ;; functions with filters or objects
           [(arr: dom (Values: (list (Result: rngs _ _) ...)) rst #f kws)
            (if (and out? pos?)
                (convert-arr a)
                (exit (fail)))]
           [_ (exit (fail))]))
       (unless (no-duplicates (for/list ([t arrs])
                                (match t
                                  [(arr: dom _ _ _ _) (length dom)]
                                  ;; is there something more sensible here?
                                  [(top-arr:) (int-err "got top-arr")])))
         (exit (fail)))
       (if (= (length arrs) 1)
           ((f #f) (first arrs))
           (case->/sc (map (f #t) arrs)))])]
    [_ (int-err "not a function" f)]))


(define positive-byte/sc (flat/sc #'(flat-named-contract 'Positive-Byte (and/c byte? positive?))))

(define byte/sc (flat/sc #'(flat-named-contract 'Byte byte?)))
(define positive-index/sc (flat/sc #'(flat-named-contract 'Positive-Index (and/c t:index? positive?))))
(define index/sc (flat/sc #'(flat-named-contract 'Index t:index?)))
(define positive-fixnum/sc (flat/sc #'(flat-named-contract 'Positive-Fixnum (and/c fixnum? positive?))))
(define nonnegative-fixnum/sc (flat/sc #'(flat-named-contract 'Nonnegative-Fixnum (and/c fixnum? (lambda (x) (>= x 0))))))
(define nonpositive-fixnum/sc (flat/sc #'(flat-named-contract 'Nonpositive-Fixnum (and/c fixnum? (lambda (x) (<= x 0))))))
(define fixnum/sc (flat/sc #'(flat-named-contract 'Fixnum fixnum?)))
(define positive-integer/sc (flat/sc #'(flat-named-contract 'Positive-Integer (and/c exact-integer? positive?))))
(define natural/sc (flat/sc #'(flat-named-contract 'Natural (and/c exact-integer? (lambda (x) (>= x 0))))))
(define negative-integer/sc (flat/sc #'(flat-named-contract 'Negative-Integer (and/c exact-integer? negative?))))
(define nonpositive-integer/sc (flat/sc #'(flat-named-contract 'Nonpositive-Integer (and/c exact-integer? (lambda (x) (<= x 0))))))
(define integer/sc (flat/sc #'(flat-named-contract 'Integer exact-integer?)))
(define positive-rational/sc (flat/sc #'(flat-named-contract 'Positive-Rational (and/c t:exact-rational? positive?))))
(define nonnegative-rational/sc (flat/sc #'(flat-named-contract 'Nonnegative-Rational (and/c t:exact-rational? (lambda (x) (>= x 0))))))
(define negative-rational/sc (flat/sc #'(flat-named-contract 'Negative-Rational (and/c t:exact-rational? negative?))))
(define nonpositive-rational/sc (flat/sc #'(flat-named-contract 'Nonpositive-Rational (and/c t:exact-rational? (lambda (x) (<= x 0))))))
(define rational/sc (flat/sc #'(flat-named-contract 'Rational t:exact-rational?)))
(define flonum-zero/sc (flat/sc #'(flat-named-contract 'Float-Zero (and/c flonum? zero?))))
(define nonnegative-flonum/sc (flat/sc #'(flat-named-contract 'Nonnegative-Float (and/c flonum? (lambda (x) (>= x 0))))))
(define nonpositive-flonum/sc (flat/sc #'(flat-named-contract 'Nonpositive-Float (and/c flonum? (lambda (x) (<= x 0))))))
(define flonum/sc (flat/sc #'(flat-named-contract 'Float flonum?)))
(define single-flonum-zero/sc (flat/sc #'(flat-named-contract 'Single-Flonum-Zero (and/c single-flonum? zero?))))
(define inexact-real-zero/sc (flat/sc #'(flat-named-contract 'Inexact-Real-Zero (and/c inexact-real? zero?))))
(define positive-inexact-real/sc (flat/sc #'(flat-named-contract 'Positive-Inexact-Real (and/c inexact-real? positive?))))
(define nonnegative-single-flonum/sc (flat/sc #'(flat-named-contract 'Nonnegative-Single-Flonum (and/c single-flonum? (lambda (x) (>= x 0))))))
(define nonnegative-inexact-real/sc (flat/sc #'(flat-named-contract 'Nonnegative-Inexact-Real (and/c inexact-real? (lambda (x) (>= x 0))))))
(define negative-inexact-real/sc (flat/sc #'(flat-named-contract 'Negative-Inexact-Real (and/c inexact-real? negative?))))
(define nonpositive-single-flonum/sc (flat/sc #'(flat-named-contract 'Nonpositive-Single-Flonum (and/c single-flonum? (lambda (x) (<= x 0))))))
(define nonpositive-inexact-real/sc (flat/sc #'(flat-named-contract 'Nonpositive-Inexact-Real (and/c inexact-real? (lambda (x) (<= x 0))))))
(define single-flonum/sc (flat/sc #'(flat-named-contract 'Single-Flonum single-flonum?)))
(define inexact-real/sc (flat/sc #'(flat-named-contract 'Inexact-Real inexact-real?)))
(define real-zero/sc (flat/sc #'(flat-named-contract 'Real-Zero (and/c real? zero?))))
(define positive-real/sc (flat/sc #'(flat-named-contract 'Positive-Real (and/c real? positive?))))
(define nonnegative-real/sc (flat/sc #'(flat-named-contract 'Nonnegative-Real (and/c real? (lambda (x) (>= x 0))))))
(define negative-real/sc (flat/sc #'(flat-named-contract 'Negative-Real (and/c real? negative?))))
(define nonpositive-real/sc (flat/sc #'(flat-named-contract 'Nonpositive-Real (and/c real? (lambda (x) (<= x 0))))))
(define real/sc (flat/sc #'(flat-named-contract 'Real real?)))
(define exact-number/sc (flat/sc #'(flat-named-contract 'Exact-Number (and/c number? exact?))))
(define inexact-complex/sc
  (flat/sc #'(flat-named-contract 'Inexact-Complex
               (and/c number?
                 (lambda (x)
                   (and (inexact-real? (imag-part x))
                        (inexact-real? (real-part x))))))))
(define number/sc (flat/sc #'(flat-named-contract 'Number number?)))


(define (numeric-type->static-contract type)
  (match type
    ;; numeric special cases
    ;; since often-used types like Integer are big unions, this would
    ;; generate large contracts.
    [(== t:-PosByte type-equal?) positive-byte/sc]
    [(== t:-Byte type-equal?) byte/sc]
    [(== t:-PosIndex type-equal?) positive-index/sc]
    [(== t:-Index type-equal?) index/sc]
    [(== t:-PosFixnum type-equal?) positive-fixnum/sc]
    [(== t:-NonNegFixnum type-equal?) nonnegative-fixnum/sc]
    ;; -NegFixnum is a base type
    [(== t:-NonPosFixnum type-equal?) nonpositive-fixnum/sc]
    [(== t:-Fixnum type-equal?) fixnum/sc]
    [(== t:-PosInt type-equal?) positive-integer/sc]
    [(== t:-Nat type-equal?) natural/sc]
    [(== t:-NegInt type-equal?) negative-integer/sc]
    [(== t:-NonPosInt type-equal?) nonpositive-integer/sc]
    [(== t:-Int type-equal?) integer/sc]
    [(== t:-PosRat type-equal?) positive-rational/sc]
    [(== t:-NonNegRat type-equal?) nonnegative-rational/sc]
    [(== t:-NegRat type-equal?) negative-rational/sc]
    [(== t:-NonPosRat type-equal?) nonpositive-rational/sc]
    [(== t:-Rat type-equal?) rational/sc]
    [(== t:-FlonumZero type-equal?) flonum-zero/sc]
    [(== t:-NonNegFlonum type-equal?) nonnegative-flonum/sc]
    [(== t:-NonPosFlonum type-equal?) nonpositive-flonum/sc]
    [(== t:-Flonum type-equal?) flonum/sc]
    [(== t:-SingleFlonumZero type-equal?) single-flonum-zero/sc]
    [(== t:-InexactRealZero type-equal?) inexact-real-zero/sc]
    [(== t:-PosInexactReal type-equal?) positive-inexact-real/sc]
    [(== t:-NonNegSingleFlonum type-equal?) nonnegative-single-flonum/sc]
    [(== t:-NonNegInexactReal type-equal?) nonnegative-inexact-real/sc]
    [(== t:-NegInexactReal type-equal?) negative-inexact-real/sc]
    [(== t:-NonPosSingleFlonum type-equal?) nonpositive-single-flonum/sc]
    [(== t:-NonPosInexactReal type-equal?) nonpositive-inexact-real/sc]
    [(== t:-SingleFlonum type-equal?) single-flonum/sc]
    [(== t:-InexactReal type-equal?) inexact-real/sc]
    [(== t:-RealZero type-equal?) real-zero/sc]
    [(== t:-PosReal type-equal?) positive-real/sc]
    [(== t:-NonNegReal type-equal?) nonnegative-real/sc]
    [(== t:-NegReal type-equal?) negative-real/sc]
    [(== t:-NonPosReal type-equal?) nonpositive-real/sc]
    [(== t:-Real type-equal?) real/sc]
    [(== t:-ExactNumber type-equal?) exact-number/sc]
    [(== t:-InexactComplex type-equal?) inexact-complex/sc]
    [(== t:-Number type-equal?) number/sc]
    [else #f]))

