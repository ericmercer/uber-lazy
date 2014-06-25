#lang racket

(require redex/reduction-semantics)
(provide (all-defined-out))

(define SimpleSwap
  (term (class SimpleSwap 
          (
           [Container x]
           [Container y]
          )
          
          (
           (Container run () (var Container t := (this $ x) in
                                  (begin
                                    (this $ x := (this $ y))
                                    (this $ y := t)
                                   )))
          )``
          )
))

