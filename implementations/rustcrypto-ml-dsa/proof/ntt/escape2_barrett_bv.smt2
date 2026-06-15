; Bit-vector form of the SAME Barrett identity as escape2_barrett_int.smt2.
; `unsat` would mean the identity holds; in practice z3 does NOT finish.
; Result (z3 4.8.14, this development): timeout (>120 s cap shown; >300 s in the table).
; This is the wall: identical goal, bit-blasted, intractable at x<2^46.
(set-logic QF_BV)
(declare-const x (_ BitVec 128))
(define-fun M () (_ BitVec 128) (_ bv8396807 128))
(define-fun Q () (_ BitVec 128) (_ bv8380417 128))
(assert (bvult x (_ bv70368744177664 128)))   ; x < 2^46
(assert (let ((quot (bvlshr (bvmul x M) (_ bv46 128))))
          (let ((rem (bvsub x (bvmul quot Q))))
            (not (and (bvule (_ bv0 128) rem) (bvult rem (bvmul (_ bv2 128) Q)))))))
(check-sat)
