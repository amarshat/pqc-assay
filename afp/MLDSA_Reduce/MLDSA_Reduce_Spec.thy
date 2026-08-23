(* Title:      MLDSA_Reduce/MLDSA_Reduce_Spec.thy
   Author:     Amar Akshat <amar.akshat@gmail.com>, 2026
   License:    BSD 3-clause

   Specification of the modular-reduction layer of ML-DSA (FIPS 204), at the integer level.

   FIPS 204 fixes the prime modulus mldsa_q = 8380417. The reduction routines below are implementation
   devices rather than algorithms the standard spells out: a deployed implementation needs values
   reduced modulo mldsa_q into a specific window, and the reference implementation does that with
   Montgomery reduction, a Barrett-style mldsa_reduce32, a conditional add and their composition. This
   theory states what each routine must satisfy. MLDSA_Reduce.thy defines fixed-width
   implementations of them and proves the implementations meet these contracts. *)

theory MLDSA_Reduce_Spec
  imports Main
begin

section \<open>The modulus\<close>

text \<open>FIPS 204 \<^cite>\<open>"fips204"\<close> fixes the prime modulus of ML-DSA. Everything below is stated
relative to it.

Every constant this entry introduces carries an \<open>mldsa_\<close> prefix, so that importing the entry does
not put names as common as \<open>q\<close> or \<open>freeze\<close> into scope. The prose writes the modulus as \<open>q\<close>
where it reads as mathematics; the constant itself is \<open>mldsa_q\<close>.\<close>

definition mldsa_q :: int where "mldsa_q = 8380417"

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
definition mldsa_mont_input_ok :: "int \<Rightarrow> bool" where
  "mldsa_mont_input_ok a \<longleftrightarrow> -(2^31 * mldsa_q) \<le> a \<and> a < 2^31 * mldsa_q"

text \<open>\<open>r\<close> is a correct Montgomery reduction \<^cite>\<open>"montgomery1985"\<close> of \<open>a\<close> when
\<open>2 ^ 32 * r\<close> is congruent to \<open>a\<close> modulo \<open>q\<close> and \<open>r\<close> lies strictly between \<open>-q\<close> and \<open>q\<close>.\<close>
definition mldsa_is_montgomery_reduction :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "mldsa_is_montgomery_reduction a r \<longleftrightarrow> (2^32 * r) mod mldsa_q = a mod mldsa_q \<and> -mldsa_q < r \<and> r < mldsa_q"

text \<open>\<open>mldsa_caddq\<close> adds \<open>q\<close> exactly when its argument is negative: it preserves the residue and maps
\<open>(-q, q)\<close> into \<open>[0, q)\<close>.\<close>
definition mldsa_is_caddq :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "mldsa_is_caddq a r \<longleftrightarrow> r mod mldsa_q = a mod mldsa_q \<and> (-mldsa_q \<le> a \<and> a < mldsa_q \<longrightarrow> 0 \<le> r \<and> r < mldsa_q)"

text \<open>The input domain for \<open>mldsa_reduce32\<close>. The upper bound is what keeps \<open>a + 2 ^ 22\<close> from
overflowing a signed 32-bit word. The lower bound is recorded here even though every 32-bit word
satisfies it, because without it this predicate does not characterise the domain: the output window
below is false for inputs far enough below \<open>-2 ^ 31\<close>, for instance \<open>a = -10 ^ 10\<close>, which the upper
bound alone admits. A specification stated at the integer level should not depend on the caller's type
for its own soundness.\<close>
definition mldsa_reduce32_input_ok :: "int \<Rightarrow> bool" where
  "mldsa_reduce32_input_ok a \<longleftrightarrow> -2147483648 \<le> a \<and> a \<le> 2143289343"  (* -2^31 .. 2^31-2^22-1 *)

text \<open>\<^bold>\<open>Second deliberate departure.\<close> The reference implementation documents the symmetric
output window \<open>[-6283008, 6283008]\<close> for \<open>mldsa_reduce32\<close>. Under its own one-sided precondition
\<open>a \<le> 2 ^ 31 - 2 ^ 22 - 1\<close> the input \<open>a = -2143289344\<close> is admissible and produces \<open>-6283009\<close>,
one below the documented bound; the documented window is correct only under the symmetric precondition
\<open>\<bar>a\<bar> \<le> 2 ^ 31 - 2 ^ 22 - 1\<close>. What is specified here is the true reachable window, which is
asymmetric, and both of its endpoints are attained.\<close>
definition mldsa_is_reduce32 :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "mldsa_is_reduce32 a r \<longleftrightarrow> r mod mldsa_q = a mod mldsa_q \<and> -6283009 \<le> r \<and> r \<le> 6283008"

text \<open>\<open>mldsa_freeze\<close> is \<open>mldsa_caddq\<close> after \<open>mldsa_reduce32\<close>, giving the canonical representative in \<open>[0, q)\<close>.\<close>
definition mldsa_is_freeze :: "int \<Rightarrow> int \<Rightarrow> bool" where
  "mldsa_is_freeze a r \<longleftrightarrow> r mod mldsa_q = a mod mldsa_q \<and> 0 \<le> r \<and> r < mldsa_q"


text \<open>\<open>mldsa_qinv\<close> is the inverse of \<open>q\<close> modulo \<open>2 ^ 32\<close>, as fixed by the reference
implementation. The next theory proves that, rather than asserting it in prose.\<close>

definition mldsa_qinv :: int where "mldsa_qinv = 58728449"

end
