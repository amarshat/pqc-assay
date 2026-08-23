(* Title:      MLDSA_Reduce/MLDSA_Reduce_Spec.thy
   Author:     Amar Akshat <amar.akshat@gmail.com>, 2026
   License:    BSD 3-clause

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

section \<open>The modulus\<close>

text \<open>FIPS 204 \<^cite>\<open>"fips204"\<close> fixes the prime modulus of ML-DSA. Everything below is stated
relative to it.\<close>

definition q :: int where "q = 8380417"

section \<open>What each routine must satisfy\<close>

text \<open>The reference implementation \<^cite>\<open>"dilithium_ref"\<close> carries four routines in its
reduction layer. FIPS 204 does not specify them: they are the device by which an implementation keeps
coefficients in a workable range, and the standard constrains only the values they stand for. The
contracts below are therefore read off the reference implementation's own documented behaviour, with
two deliberate exceptions that are set out where they occur.\<close>

text \<open>\<^bold>\<open>First deliberate departure.\<close> The reference implementation documents the
\<^emph>\<open>inclusive\<close> input domain \<open>-2 ^ 31 * q \<le> a \<le> 2 ^ 31 * q\<close> together with the strict
postcondition \<open>- q < r < q\<close>. Those two are inconsistent at the upper endpoint: the routine returns
exactly \<open>q\<close> for \<open>a = 2 ^ 31 * q\<close>, which violates \<open>r < q\<close>. The strict postcondition holds on the
half-open domain, and that is what is specified here. A reader comparing this entry with the reference
implementation's comment will find the difference at that one endpoint and nowhere else.\<close>
definition mont_input_ok :: "int \<Rightarrow> bool" where
  "mont_input_ok a \<longleftrightarrow> -(2^31 * q) \<le> a \<and> a < 2^31 * q"

text \<open>\<open>r\<close> is a correct Montgomery reduction \<^cite>\<open>"montgomery1985"\<close> of \<open>a\<close> when
\<open>2 ^ 32 * r\<close> is congruent to \<open>a\<close> modulo \<open>q\<close> and \<open>r\<close> lies strictly between \<open>-q\<close> and \<open>q\<close>.\<close>
definition is_montgomery_reduction :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_montgomery_reduction a r \<longleftrightarrow> (2^32 * r) mod q = a mod q \<and> -q < r \<and> r < q"

text \<open>\<open>caddq\<close> adds \<open>q\<close> exactly when its argument is negative: it preserves the residue and maps
\<open>(-q, q)\<close> into \<open>[0, q)\<close>.\<close>
definition is_caddq :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_caddq a r \<longleftrightarrow> r mod q = a mod q \<and> (-q \<le> a \<and> a < q \<longrightarrow> 0 \<le> r \<and> r < q)"

text \<open>The input domain for \<open>reduce32\<close> is the one-sided bound that keeps \<open>a + 2 ^ 22\<close> from
overflowing a signed 32-bit word; the lower bound holds automatically for such a word.\<close>
definition reduce32_input_ok :: "int \<Rightarrow> bool" where
  "reduce32_input_ok a \<longleftrightarrow> a \<le> 2143289343"  (* 2^31 - 2^22 - 1 *)

text \<open>\<^bold>\<open>Second deliberate departure.\<close> The reference implementation documents the symmetric
output window \<open>[-6283008, 6283008]\<close> for \<open>reduce32\<close>. Under its own one-sided precondition
\<open>a \<le> 2 ^ 31 - 2 ^ 22 - 1\<close> the input \<open>a = -2143289344\<close> is admissible and produces \<open>-6283009\<close>,
one below the documented bound; the documented window is correct only under the symmetric precondition
\<open>\<bar>a\<bar> \<le> 2 ^ 31 - 2 ^ 22 - 1\<close>. What is specified here is the true reachable window, which is
asymmetric, and both of its endpoints are attained.\<close>
definition is_reduce32 :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_reduce32 a r \<longleftrightarrow> r mod q = a mod q \<and> -6283009 \<le> r \<and> r \<le> 6283008"

text \<open>\<open>freeze\<close> is \<open>caddq\<close> after \<open>reduce32\<close>, giving the canonical representative in \<open>[0, q)\<close>.\<close>
definition is_freeze :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "is_freeze a r \<longleftrightarrow> r mod q = a mod q \<and> 0 \<le> r \<and> r < q"


section \<open>The arithmetic core\<close>

text \<open>If \<open>T\<close> is congruent to \<open>A * QINV\<close> modulo \<open>2 ^ 32\<close>, lies in the signed 32-bit range, and
\<open>A\<close> lies in the half-open domain above, then \<open>(A - T * q) / 2 ^ 32\<close> is a correct Montgomery reduction
of \<open>A\<close>. All four results in the next theory reduce to this lemma. The bound on \<open>A\<close> is not optional:
without it the conclusion fails for large \<open>A\<close>.\<close>
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
  \<comment> \<open>congruence: the reduced value times two-to-the-32 is congruent to A modulo Q, since Q divides T*Q. Note: presburger does not cope with a modulus this large\<close>
  have cong: "(4294967296 * r) mod 8380417 = A mod 8380417"
  proof -
    have eq: "4294967296 * r = A - T * 8380417" using D_eq by simp
    have "(A - T * 8380417) mod (8380417::int) = A mod 8380417"
      using mod_mult_self1[of A "- T" 8380417] by (simp add: algebra_simps)
    thus ?thesis using eq by simp
  qed
  \<comment> \<open>bounds: multiply the range hypotheses by Q, then divide the relation through. Evaluate the big
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
