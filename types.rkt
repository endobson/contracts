#lang racket

(require
 typed-racket/utils/utils
 syntax/parse
 (rep type-rep filter-rep object-rep)
 (typecheck internal-forms)
 (utils tc-utils require-contract any-wrap)
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

(provide type->static-contract)

(define any-wrap/sc (simple-contract #'any-wrap/c 'impersonator))

(define (no-duplicates l)
  (= (length l) (length (remove-duplicates l))))

(define (from-typed? side)
  (case side
   [(typed both) #t]
   [(untyped) #f]))

(define (from-untyped? side)
  (case side
   [(untyped both) #t]
   [(typed) #f]))

(define (flip-side side)
  (case side
   [(typed) 'untyped]
   [(untyped) 'typed]
   [(both) 'both]))

(struct triple (untyped typed both))
(define (triple-lookup trip side)
  (case side
    ((untyped) (triple-untyped trip))
    ((typed) (triple-typed trip))
    ((both) (triple-both trip))))
(define (same sc)
  (triple sc sc sc))


(define (type->static-contract type fail #:typed-side [typed-side #t])

  (let loop ([type type] [typed-side (if typed-side 'typed 'untyped)] [recursive-values (hash)])
    (define (t->sc t #:recursive-values (recursive-values recursive-values))
      (loop t typed-side recursive-values))
    (define (t->sc/neg t #:recursive-values (recursive-values recursive-values))
      (loop t (flip-side typed-side) recursive-values))
    (define (t->sc/both t #:recursive-values (recursive-values recursive-values))
      (loop t 'both recursive-values))
    (define (t->sc/method t) (t->sc/function t fail typed-side recursive-values loop #t))
    (define (t->sc/fun t) (t->sc/function t fail typed-side recursive-values loop #f))
    (match type
      [(or (App: _ _ _) (Name: _)) (t->sc (resolve-once type))]
      [(Univ:) (if (from-typed? typed-side) any-wrap/sc any/sc)]
      [(Mu: var (Union: (list (Value: '()) (Pair: elem-ty (F: var)))))
       (listof/sc (t->sc elem-ty))]
      [t (=> fail) (or (numeric-type->static-contract t) (fail))]
      [(Base: sym cnt _ _ _)
       (flat/sc #`(flat-named-contract '#,sym (flat-contract-predicate #,cnt)))]
      [(Refinement: par p? cert)
       (and/sc (t->sc par) (flat/sc (cert p?)))]
      [(Union: elems)
       (or/sc* (map t->sc elems))]
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
       (triple-lookup (hash-ref recursive-values v) typed-side)]
      [(Poly: vs b)
       (if (from-typed? typed-side)
           ;; in positive position, no checking needed for the variables
           (let ((recursive-values (for/fold ([rv recursive-values]) ([v vs])
                                     (hash-set rv v (same any/sc)))))
             (t->sc b #:recursive-values recursive-values))
           ;; in negative position, use `parameteric/c'
           (match-let ([(Poly-names: vs-nm _) type])
             (let ((temporaries (generate-temporaries vs-nm)))
               (define rv (for/fold ((rv recursive-values)) ((temp temporaries)
                                                             (v-nm vs-nm))
                            (hash-set rv v-nm (same (simple-contract temp 'impersonator)))))
               (parametric->/sc temporaries
                  (t->sc b #:recursive-values rv)))))]
      [(Mu: n b)
       (match-define (and n*s (list untyped-n* typed-n* both-n*)) (generate-temporaries (list n n n)))
       (define rv
         (hash-set recursive-values n
                   (triple (recursive-contract-use untyped-n*)
                           (recursive-contract-use typed-n*)
                           (recursive-contract-use both-n*))))
       (case typed-side
         [(both) (recursive-contract
                   (list both-n*)
                   (list (loop b 'both rv))
                   (recursive-contract-use both-n*))]
         [(typed untyped)
          ;; TODO not fail in cases that don't get used
          (define untyped (loop b 'untyped rv))
          (define typed (loop b 'typed rv))
          (define both (loop b 'both rv))

          (recursive-contract
                   n*s
                   (list untyped typed both)
                   (recursive-contract-use (if (from-typed? typed-side) typed-n* untyped-n*)))])]
      [(Instance: (? Mu? t))
       (t->sc (make-Instance (resolve-once t)))]
      [(Instance: (Class: _ _ (list (list names functions) ...)))
       (object/sc* (map list names (map t->sc/method functions)))]
      ;; init args not currently handled by class/c
      [(Class: _ (list (list by-name-inits by-name-init-tys _) ...) (list (list names functions) ...))
       (class/sc* (map list names (map t->sc/method functions))
                  (map list by-name-inits (map t->sc/neg by-name-init-tys)))]
      [(Struct: nm par (list (fld: flds acc-ids mut?) ...) proc poly? pred?)
       (cond
         [(assf (λ (v) (equal? v nm)) recursive-values) => second]
         [proc (exit (fail))]
         [poly?
          (define nm* (generate-temporary #'n*))
          (define fields
            (for/list ([fty flds] [mut? mut?])
              (define sc
                (t->sc fty #:recursive-values (hash-set
                                                recursive-values
                                                nm (recursive-contract-use nm*))))
              (if mut? sc (chaperone-restrict sc))))
          (recursive-contract nm* (struct/sc nm fields))]
         [else (flat/sc #`(flat-named-contract '#,(syntax-e pred?) #,pred?))])]
      [(Syntax: (Base: 'Symbol _ _ _ _)) identifier/sc]
      [(Syntax: t)
       (syntax/sc (t->sc t))]
      [(Value: v)
       (flat/sc #`(flat-named-contract #,(format "~a" v) (lambda (x) (equal? x '#,v))))]
      [(Param: in out) 
       (parameter/sc (t->sc in) (t->sc out))]
      [(Hashtable: k v)
       (hash/sc (t->sc k) (t->sc v))]
      [else
       (exit (fail))])))

(define (t->sc/function f fail typed-side recursive-values loop method?)
  (define (t->sc t #:recursive-values (recursive-values recursive-values))
    (loop t typed-side recursive-values))
  (define (t->sc/neg t #:recursive-values (recursive-values recursive-values))
    (loop t (flip-side typed-side) recursive-values))
  (match f
    [(Function: (list (top-arr:))) #'(case->)]
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
            (if typed-side
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

(define-syntax-rule (numeric/sc name body)
 (flat/sc #'(flat-named-contract 'name body)))
(module predicates racket/base
  (provide nonnegative? nonpositive?)
  (define nonnegative? #'(lambda (x) (>= x 0)))
  (define nonpositive? #'(lambda (x) (<= x 0))))
(require (for-template 'predicates))

(define positive-byte/sc (numeric/sc Positive-Byte (and/c byte? positive?)))
(define byte/sc (numeric/sc Byte byte?))
(define positive-index/sc (numeric/sc Positive-Index (and/c t:index? positive?)))
(define index/sc (numeric/sc Index t:index?))
(define positive-fixnum/sc (numeric/sc Positive-Fixnum (and/c fixnum? positive?)))
(define nonnegative-fixnum/sc (numeric/sc Nonnegative-Fixnum (and/c fixnum? non-negative)))
(define nonpositive-fixnum/sc (numeric/sc Nonpositive-Fixnum (and/c fixnum? non-positive)))
(define fixnum/sc (numeric/sc Fixnum fixnum?))
(define positive-integer/sc (numeric/sc Positive-Integer (and/c exact-integer? positive?)))
(define natural/sc (numeric/sc Natural exact-nonegative-integer?))
(define negative-integer/sc (numeric/sc Negative-Integer (and/c exact-integer? negative?)))
(define nonpositive-integer/sc (numeric/sc Nonpositive-Integer (and/c exact-integer? nonpostive?)))
(define integer/sc (numeric/sc Integer exact-integer?))
(define positive-rational/sc (numeric/sc Positive-Rational (and/c t:exact-rational? positive?)))
(define nonnegative-rational/sc (numeric/sc Nonnegative-Rational (and/c t:exact-rational? nonnegative?)))
(define negative-rational/sc (numeric/sc Negative-Rational (and/c t:exact-rational? negative?)))
(define nonpositive-rational/sc (numeric/sc Nonpositive-Rational (and/c t:exact-rational? nonpositive?)))
(define rational/sc (numeric/sc Rational t:exact-rational?))
(define flonum-zero/sc (numeric/sc Float-Zero (and/c flonum? zero?)))
(define nonnegative-flonum/sc (numeric/sc Nonnegative-Float (and/c flonum? nonnegative?)))
(define nonpositive-flonum/sc (numeric/sc Nonpositive-Float (and/c flonum? nonpositive?)))
(define flonum/sc (numeric/sc Float flonum?))
(define single-flonum-zero/sc (numeric/sc Single-Flonum-Zero (and/c single-flonum? zero?)))
(define inexact-real-zero/sc (numeric/sc Inexact-Real-Zero (and/c inexact-real? zero?)))
(define positive-inexact-real/sc (numeric/sc Positive-Inexact-Real (and/c inexact-real? positive?)))
(define nonnegative-single-flonum/sc (numeric/sc Nonnegative-Single-Flonum (and/c single-flonum? nonnegative?)))
(define nonnegative-inexact-real/sc (numeric/sc Nonnegative-Inexact-Real (and/c inexact-real? nonpositive?)))
(define negative-inexact-real/sc (numeric/sc Negative-Inexact-Real (and/c inexact-real? negative?)))
(define nonpositive-single-flonum/sc (numeric/sc Nonpositive-Single-Flonum (and/c single-flonum? nonnegative?)))
(define nonpositive-inexact-real/sc (numeric/sc Nonpositive-Inexact-Real (and/c inexact-real? nonpositive?)))
(define single-flonum/sc (numeric/sc Single-Flonum single-flonum?))
(define inexact-real/sc (numeric/sc Inexact-Real inexact-real?))
(define real-zero/sc (numeric/sc Real-Zero (and/c real? zero?)))
(define positive-real/sc (numeric/sc Positive-Real (and/c real? positive?)))
(define nonnegative-real/sc (numeric/sc Nonnegative-Real (and/c real? nonnegative?)))
(define negative-real/sc (numeric/sc Negative-Real (and/c real? negative?)))
(define nonpositive-real/sc (numeric/sc Nonpositive-Real (and/c real? nonpositive?)))
(define real/sc (numeric/sc Real real?))
(define exact-number/sc (numeric/sc Exact-Number (and/c number? exact?)))
(define inexact-complex/sc
  (numeric/sc Inexact-Complex
               (and/c number?
                 (lambda (x)
                   (and (inexact-real? (imag-part x))
                        (inexact-real? (real-part x)))))))
(define number/sc (numeric/sc Number number?))


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

