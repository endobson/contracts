#lang racket/base

(provide
  (struct-out simple-contract)
  (struct-out recursive-contract)
  (struct-out recursive-contract-use)
  (struct-out combinator)
  (struct-out flat-combinator)
  (struct-out chaperone-combinator)
  (struct-out impersonator-combinator)
  (struct-out flat-restrict)
  (struct-out chaperone-restrict))


(struct simple-contract (syntax kind))
(struct recursive-contract (name body))
(struct recursive-contract-use (name))
(struct combinator (make-syntax args))
(struct flat-combinator combinator ())
(struct chaperone-combinator combinator ())
(struct impersonator-combinator combinator ())
(struct flat-restrict (body))
(struct chaperone-restrict (body))

