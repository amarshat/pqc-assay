; Escape 2 (integer core): the Barrett identity in UNBOUNDED integer arithmetic.
; Claim: for all x in [0, 2^46), remainder = x - floor(x*M/2^46)*Q lies in [0, 2Q).
; Encoded as the negation; `unsat` => identity holds over the whole domain.
; Result (z3 4.8.14, this development): unsat in ~0.04 s.
; Contrast: the bit-vector form of the SAME goal (escape2_barrett_bv.smt2) times out >300 s.
(set-logic NIA)
(declare-const x Int)
(define-fun M () Int 8396807)
(define-fun Q () Int 8380417)
(define-fun K () Int 70368744177664) ; 2^46
(assert (and (<= 0 x) (< x K)))
(assert (let ((quot (div (* x M) K)))
          (let ((rem (- x (* quot Q))))
            (not (and (<= 0 rem) (< rem (* 2 Q)))))))
(check-sat)
