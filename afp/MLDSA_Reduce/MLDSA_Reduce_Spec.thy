(* Title:      MLDSA_Reduce/MLDSA_Reduce_Spec.thy
   Author:     Amar Akshat, 2026

   Specification of the modular-reduction layer of ML-DSA (FIPS 204), at the integer level.

   FIPS 204 fixes the prime modulus q = 8380417. The reduction routines below are implementation
   devices rather than algorithms the standard spells out: a deployed implementation needs values
   reduced modulo q into a specific window, and the reference implementation does that with
   Montgomery reduction, a Barrett-style reduce32, a conditional add and their composition. This
   theory states what each routine must satisfy. MLDSA_Reduce.thy defines fixed-width
   implementations of them and proves the implementations meet these contracts. *)

theory MLDSA_Reduce_Spec
  imports Main
begin

definition q :: int where "q = 8380417"

(* Input domain for the strict-bound correctness claim: HALF-OPEN  -2^31*q <= a < 2^31*q.
   NB: PQClean's reduce.c comment documents the INCLUSIVE domain -2^31*q <= a <= q*2^31 together
   with the strict postcondition -q < r < q, but those are inconsistent at the upper endpoint:
   montgomery_reduce(2^31*q) = q, violating r < q (see docs/ASSUMPTIONS.md, finding OF-1). The
   strict postcondition holds exactly on the half-open domain below, which is what we specify. *)
definition mont_input_ok :: "int \<Rightarrow> bool" where
  "mont_input_ok a \<longleftrightarrow> -(2^31 * q) \<le> a \<and> a < 2^31 * q"

(* r is a correct Montgomery reduction of a iff  2^32 * r \<equiv> a  (mod q)  and  -q < r < q.
   (Equivalently r \<equiv> a * 2^-32 (mod q), since gcd(2,q)=1.) *)
definition is_montgomery_reduction :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_montgomery_reduction a r \<longleftrightarrow> (2^32 * r) mod q = a mod q \<and> -q < r \<and> r < q"

(* --- the rest of the reduce.c layer -------------------------------------------------------- *)

(* caddq: add q iff a is negative. Preserves the residue, and maps (-q, q) into [0, q). *)
definition is_caddq :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_caddq a r \<longleftrightarrow> r mod q = a mod q \<and> (-q \<le> a \<and> a < q \<longrightarrow> 0 \<le> r \<and> r < q)"

(* Input domain for reduce32, matching the SAW leg's precondition: the one-sided bound that keeps
   a + (1<<22) from overflowing int32. (a >= -2^31 holds automatically for an int32 value.) *)
definition reduce32_input_ok :: "int \<Rightarrow> bool" where
  "reduce32_input_ok a \<longleftrightarrow> a \<le> 2143289343"  (* 2^31 - 2^22 - 1 *)

(* reduce32 (Barrett-style): r \<equiv> a (mod q) within the TRUE reachable output window.
   NB: PQClean's reduce.c comment claims [-6283008, 6283008], but under its (one-sided) precondition
   a <= 2^31-2^22-1 the input a = -2143289344 is admissible and gives reduce32 a = -6283009, one below
   the documented bound (see docs/ASSUMPTIONS.md, finding OF-2). The documented bound holds only under
   a symmetric |a| <= 2^31-2^22-1. We specify the honest reachable window, which is asymmetric. *)
definition is_reduce32 :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_reduce32 a r \<longleftrightarrow> r mod q = a mod q \<and> -6283009 \<le> r \<and> r \<le> 6283008"

(* freeze = caddq \<circ> reduce32: the canonical representative in [0, q). *)
definition is_freeze :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_freeze a r \<longleftrightarrow> r mod q = a mod q \<and> 0 \<le> r \<and> r < q"


(* The integer core of Montgomery reduction: if T is congruent to A * QINV modulo 2^32 and lies in
   the signed 32-bit range, then (A - T*q) / 2^32 is a correct Montgomery reduction of A. Every
   fixed-width implementation in MLDSA_Reduce.thy reduces to this lemma. *)
lemma mont_core:
  fixes A T :: int
  assumes Tc:  "(T - A * 58728449) mod 4294967296 = 0"
      and Tlo: "- 2147483648 \<le> T" and Thi: "T < 2147483648"
      and Alo: "- (2147483648 * 8380417) \<le> A" and Ahi: "A < 2147483648 * 8380417"
  shows "(4294967296 * ((A - T * 8380417) div 4294967296)) mod 8380417 = A mod 8380417
       \<and> - 8380417 < (A - T * 8380417) div 4294967296
       \<and> (A - T * 8380417) div 4294967296 < 8380417"
proof -
  from Tc have "(4294967296::int) dvd (T - A * 58728449)" by (simp add: mod_eq_0_iff_dvd)
  then obtain k where k: "T - A * 58728449 = 4294967296 * k" by (auto elim: dvdE)
  hence T_eq: "T = A * 58728449 + 4294967296 * k" by simp
  define r where "r = - (A * 114592 + k * 8380417)"
  have D_eq: "A - T * 8380417 = 4294967296 * r"
    unfolding r_def T_eq by (simp add: algebra_simps)
  hence r_is: "(A - T * 8380417) div 4294967296 = r" by simp
  \<comment> \<open>congruence: 2^32*r = A - T*Q \<equiv> A (mod Q), since Q dvd T*Q (NO presburger: huge modulus)\<close>
  have cong: "(4294967296 * r) mod 8380417 = A mod 8380417"
  proof -
    have eq: "4294967296 * r = A - T * 8380417" using D_eq by simp
    have "(A - T * 8380417) mod (8380417::int) = A mod 8380417"
      using mod_mult_self1[of A "- T" 8380417] by (simp add: algebra_simps)
    thus ?thesis using eq by simp
  qed
  \<comment> \<open>bounds: multiply the range hyps by Q, then divide the 2^32*r relation. Evaluate the big
      numeral products up front so linarith only sees plain integers.\<close>
  have e1: "(2147483648::int) * 8380417 = 17996808470921216" by simp
  have e2: "(4294967296::int) * 8380417 = 35993616941842432" by simp
  have Tq_lo: "T * 8380417 \<ge> - 17996808470921216" using Tlo by (simp add: mult_right_mono)
  have Tq_hi: "T * 8380417 \<le> 17996808462540799" using Thi by (simp add: mult_right_mono)
  have Ahi': "A < 17996808470921216" using Ahi e1 by simp
  have Alo': "- 17996808470921216 \<le> A" using Alo e1 by simp
  have ub: "4294967296 * r < 35993616941842432" using D_eq Ahi' Tq_lo by linarith
  have lb: "- 35993616941842432 < 4294967296 * r" using D_eq Alo' Tq_hi by linarith
  from ub have rub: "r < 8380417" by simp
  from lb have rlb: "- 8380417 < r" by simp
  from cong rub rlb r_is show ?thesis by simp
qed

end
