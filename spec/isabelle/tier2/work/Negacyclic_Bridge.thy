(* Tier-2 final bridge (WIP): the lifted forward NTT computes the FIPS-204
   negacyclic transform in bit-reversed output order.

   Target theorem (route A, self-contained closed form):
     cf (nttFwdAllRef w) k
       = (\<Sum>j<256. cf w j * 1753^((2*(brv 8 k)+1)*j)) mod 8380417   (k<256, bounded w)

   i.e. output position k holds the negacyclic DFT coefficient at index brv 8 k.
   This matches FIPS-204's bit-reversed forward-NTT convention (zeta = 1753, the
   primitive 512th root of unity mod q = 8380417).

   We build on `fwd_as_bfly` (CT_Routing): the lifted NTT already equals the
   8-fold abstract butterfly `fwdBfly` on the int-coefficient view, so the rest
   is a pure int-mod-q partial-sum invariant over the DIF butterfly layers.

   This file is WIP: it currently establishes the foundational facts only. The
   central invariant is NOT yet proven; nothing here is admitted with sorry. *)
theory Negacyclic_Bridge
  imports CT_Routing
begin

text \<open>The primitive root and modulus, as int.\<close>
abbreviation (input) qq :: int where "qq \<equiv> 8380417"
abbreviation (input) zr :: int where "zr \<equiv> 1753"

text \<open>Foundation: the lifted twiddle table holds real powers of the root in
  bit-reversed index order: \<open>zt j = zr ^ (brv 8 j) mod q\<close>. Proven by evaluation
  over the concrete 256-entry table (same device as \<open>zeta_bound\<close>).\<close>

lemma zt_eval_pow:
  "\<forall>i<256. uint_seq (nth_seq zetabrv i) = (zr ^ (brv 8 i)) mod qq"
  by eval

lemma zt_pow:
  assumes "j < 256"
  shows "zt j = (zr ^ (brv 8 j)) mod qq"
  using zt_eval_pow assms by (simp add: zt_def)

text \<open>Range of the twiddle power (re-derived from the closed form; matches the
  existing \<open>zeta_bound\<close>).\<close>
lemma zt_ge0: "j < 256 \<Longrightarrow> 0 \<le> zt j"
  by (simp add: zt_pow)

lemma zt_lt: "j < 256 \<Longrightarrow> zt j < qq"
  by (simp add: zt_pow)

section \<open>Stage-invariant scaffold for the closed-form correctness proof\<close>

text \<open>The root wraps at 256: \<open>\<zeta>^256 \<equiv> -1 (mod q)\<close> (\<open>\<zeta>\<close> is the primitive 512th
  root). This is what turns the odd-output half of each butterfly into the
  \<open>2A + e'\<close> exponent shift in the induction step.\<close>
lemma zwrap_eval: "(zr ^ 256) mod qq = qq - 1"
  by eval

lemma zwrap_cong: "[zr ^ 256 = - 1] (mod qq)"
  unfolding cong_def by eval

text \<open>Bit-reversal recursion in the form the step needs (from \<open>Bitrev.brv\<close>):
  doubling appends a low 0, \<open>2a+1\<close> appends a low 1 that reverses to the new top bit.\<close>
lemma brv_double:  "brv (Suc s) (2*a)     = brv s a"
  by simp
lemma brv_double1: "brv (Suc s) (2*a + 1) = brv s a + 2^s"
  by simp

text \<open>One abstract layer of the schedule, indexed by step \<open>s = 0..7\<close>: stride
  \<open>2^(7-s)\<close>, twiddle base \<open>2^s - 1\<close>. Matches the \<open>fwdBfly\<close> composition order.\<close>
definition bstep :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
  "bstep s g = bflyLayer (2^(7-s)) (2^s - 1) g"

fun applyN :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
  "applyN 0 g = g"
| "applyN (Suc s) g = bstep s (applyN s g)"

text \<open>The 8-fold schedule unfolds to the explicit \<open>fwdBfly\<close> composition.\<close>
lemma applyN_8_eq_fwdBfly: "applyN 8 g = fwdBfly g"
  by (simp add: fwdBfly_def bstep_def eval_nat_numeral comp_def)

text \<open>The stage invariant (no inner mod; carried as a congruence mod q). After
  \<open>s\<close> layers, position \<open>n = a\<cdot>B + c\<close> (with \<open>B = 2^(8-s)\<close>, \<open>A = 2^s\<close>,
  \<open>a = n div B\<close>, \<open>c = n mod B\<close>) holds the length-\<open>A\<close> sub-DFT of the stride-\<open>B\<close>
  subvector at offset \<open>c\<close>, evaluated at frequency \<open>2\<cdot>brv\<^sub>s a + 1\<close>.\<close>
definition inv_form :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "inv_form s g n =
     (\<Sum>m < 2^s. g (n mod 2^(8-s) + m * 2^(8-s))
                 * zr ^ ((2 * brv s (n div 2^(8-s)) + 1) * m * 2^(8-s)))"

text \<open>Base case: zero layers is the identity (the singleton sub-DFT).\<close>
lemma inv_form_0: "n < 256 \<Longrightarrow> inv_form 0 g n = g n"
  by (simp add: inv_form_def)

text \<open>Target specialisation: at \<open>s = 8\<close> the invariant is the negacyclic DFT
  coefficient at the bit-reversed output index.\<close>
lemma inv_form_8:
  "inv_form 8 g n = (\<Sum>m<256. g m * zr ^ ((2 * brv 8 n + 1) * m))"
  by (simp add: inv_form_def)

end
