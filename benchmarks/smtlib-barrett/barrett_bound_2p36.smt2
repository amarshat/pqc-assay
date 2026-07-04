(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
 FIPS 204 (ML-DSA) Barrett reduction, remainder-bound identity. Q = 8380417, M = floor(2^46 / Q) = 8396807.
 rem = x - ((x * M) >> 46) * Q over 128-bit bit-vectors. The assertion is NOT (0 <= rem < 2*Q); an
 unsat answer means the Barrett bound 0 <= rem < 2*Q holds over the stated input domain (from which one
 conditional subtraction yields x mod Q). Input domain x < 2^36.
 This benchmark family sweeps the input bound to expose a tractability cliff on a standardized, deployed
 cryptographic primitive: eager bit-blasting back-ends (z3, cvc5, yices, abc) stall past 2^34, while
 bitwuzla's abstraction-refinement crosses to 2^46 (551 s). Source and a reproducible harness:
 https://github.com/amarshat/pqc-assay  (archived: https://doi.org/10.5281/zenodo.21178811).
|)
(set-info :license "https://creativecommons.org/licenses/by/4.0/")
(set-info :category "crafted")
(set-info :status unsat)
(declare-const x (_ BitVec 128))
(define-fun M () (_ BitVec 128) (_ bv8396807 128))
(define-fun Q () (_ BitVec 128) (_ bv8380417 128))
(assert (bvult x (_ bv68719476736 128)))
(assert (let ((quot (bvlshr (bvmul x M) (_ bv46 128))))
          (let ((rem (bvsub x (bvmul quot Q))))
            (not (and (bvule (_ bv0 128) rem) (bvult rem (bvmul (_ bv2 128) Q)))))))
(check-sat)
(exit)
