#lang racket

(require redex/reduction-semantics)
(provide (all-defined-out))

(define SimpleExample
  (term (class SimpleExample
          (
           [T a]
           [T b]
          )
          
          (
           (T run () (if ((this $ a) = (this $ b))
                         (this $ a)
                      else
                         (this $ b)
                      ))
          )
          )
))
