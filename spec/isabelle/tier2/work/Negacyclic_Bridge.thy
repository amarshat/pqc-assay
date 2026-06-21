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

subsection \<open>Helper lemmas for the induction step\<close>

text \<open>Bit-reversal of a single top bit plus a low residue: \<open>brv\<^sub>8(2^s + a)\<close>.
  The bit \<open>2^s\<close> reverses to weight \<open>2^(7-s)\<close>; the low \<open>s\<close> bits \<open>a\<close> reverse and
  shift to the top, weight \<open>2^(8-s)\<close>. Proven bitwise via \<open>bit_brv\<close> / \<open>bit_add_push\<close>.\<close>
lemma brv8_pow_add:
  assumes s: "s < 8" and a: "a < 2^s"
  shows "brv 8 (2^s + a) = 2^(7-s) + brv s a * 2^(8-s)"
proof (rule bit_eqI)
  fix j :: nat
  \<comment> \<open>bit of the argument \<open>2^s + a\<close>: low bits from \<open>a\<close>, then the set bit at \<open>s\<close>.\<close>
  have arg: "bit (2^s + a) i = (if i < s then bit a i else i = s)" for i
  proof (cases "i < s")
    case True
    thus ?thesis using bit_add_push[OF a, of 1 i] by (simp add: add.commute)
  next
    case False
    have bit1: "bit (1::nat) k = (k = 0)" for k by (auto simp: bit_simps)
    have step: "bit (2^s + a) i = bit (1::nat) (i - s)"
      using bit_add_push[OF a, of 1 i] False by (simp add: add.commute)
    have "bit (1::nat) (i - s) = (i = s)" using bit1[of "i - s"] False by presburger
    thus ?thesis using step False by simp
  qed
  \<comment> \<open>bit of the result \<open>2^(7-s) + brv s a * 2^(8-s)\<close>: the lone bit \<open>7-s\<close>, then
     the reversed low part shifted up by \<open>8-s\<close>.\<close>
  have res: "bit (2^(7-s) + brv s a * 2^(8-s)) j
             = (if j < 8 - s then j = 7 - s else bit (brv s a) (j - (8 - s)))"
  proof -
    have r: "(2::nat)^(7-s) < 2^(8-s)" using s by simp
    have "bit (2^(7-s) + brv s a * 2^(8-s)) j
          = (if j < 8-s then bit ((2::nat)^(7-s)) j else bit (brv s a) (j-(8-s)))"
      using bit_add_push[OF r, of "brv s a" j] by simp
    moreover have "bit ((2::nat)^(7-s)) j = (j = 7 - s)"
      by (auto simp: bit_simps)
    ultimately show ?thesis by simp
  qed
  show "bit (brv 8 (2^s + a)) j = bit (2^(7-s) + brv s a * 2^(8-s)) j"
  proof (cases "j < 8")
    case True
    have "bit (brv 8 (2^s + a)) j = bit (2^s + a) (7 - j)"
      using True by (simp add: bit_brv)
    also have "\<dots> = (if 7 - j < s then bit a (7 - j) else 7 - j = s)" by (subst arg) simp
    finally have L: "bit (brv 8 (2^s + a)) j = (if 7-j < s then bit a (7-j) else 7-j = s)" .
    show ?thesis
    proof (cases "j < 8 - s")
      case True
      \<comment> \<open>here \<open>7-j \<ge> s\<close>, so the argument bit is the lone bit-test \<open>7-j = s\<close>,
         i.e. \<open>j = 7-s\<close>; matches the lone result bit.\<close>
      have "\<not> 7 - j < s" using True s by linarith
      hence "bit (brv 8 (2^s+a)) j = (7 - j = s)" using L by simp
      moreover have "(7 - j = s) = (j = 7 - s)" using True s \<open>j<8\<close> by linarith
      ultimately show ?thesis using True res by simp
    next
      case False
      \<comment> \<open>here \<open>7-j < s\<close>, so the argument bit is \<open>bit a (7-j)\<close>; on the result side
         it is \<open>bit (brv s a) (j-(8-s))\<close>; relate via \<open>bit_brv\<close>.\<close>
      have hj: "7 - j < s" using False \<open>j<8\<close> s by linarith
      hence "bit (brv 8 (2^s+a)) j = bit a (7 - j)" using L by simp
      moreover have "bit (brv s a) (j - (8-s)) = bit a (7 - j)"
      proof -
        have lt: "j - (8 - s) < s" using False \<open>j<8\<close> s by linarith
        have "bit (brv s a) (j-(8-s)) = bit a (s - Suc (j - (8-s)))"
          using lt by (simp add: bit_brv)
        moreover have "s - Suc (j - (8-s)) = 7 - j" using False \<open>j<8\<close> s by linarith
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis using False res by simp
    qed
  next
    case False
    \<comment> \<open>\<open>j \<ge> 8\<close>: both sides are 0 (values \<open>< 256 = 2^8\<close>).\<close>
    have "\<not> j < 8 - s" using False by simp
    have "bit (brv 8 (2^s+a)) j = False" using False by (simp add: bit_brv)
    moreover have "bit (2^(7-s) + brv s a * 2^(8-s)) j = bit (brv s a) (j-(8-s))"
      using res \<open>\<not> j < 8 - s\<close> by simp
    moreover have "brv s a < 2^s" by (rule brv_lt)
    hence "bit (brv s a) (j - (8-s)) = False"
      using bit_lt[of "brv s a" s "j-(8-s)"] False s by force
    ultimately show ?thesis by simp
  qed
qed

text \<open>The twiddle of step \<open>s\<close> at block \<open>a\<close> in closed form: \<open>zt(a + 2^s)\<close> is the
  root to the power \<open>(2\<cdot>brv\<^sub>s a + 1)\<cdot>2^(7-s)\<close> (mod q).\<close>
lemma z_closed:
  assumes s: "s < 8" and a: "a < 2^s"
  shows "[zt (a + 2^s) = zr ^ ((2 * brv s a + 1) * 2^(7-s))] (mod qq)"
proof -
  have xb: "(2::nat)^s \<le> 128" using s power_increasing[of s 7 "2::nat"] by simp
  have lt: "a + 2^s < 256" using a xb by linarith
  have exp: "brv 8 (a + 2^s) = (2 * brv s a + 1) * 2^(7-s)"
  proof -
    have "brv 8 (a + 2^s) = 2^(7-s) + brv s a * 2^(8-s)"
      using brv8_pow_add[OF s a] by (simp add: add.commute)
    also have "(8::nat) - s = Suc (7 - s)" using s by linarith
    hence "2^(7-s) + brv s a * 2^(8-s) = (2 * brv s a + 1) * 2^(7-s)" by simp
    finally show ?thesis .
  qed
  have "zt (a + 2^s) = (zr ^ (brv 8 (a + 2^s))) mod qq" by (rule zt_pow[OF lt])
  also have "\<dots> = (zr ^ ((2 * brv s a + 1) * 2^(7-s))) mod qq" by (simp add: exp)
  finally show ?thesis by (simp add: cong_def)
qed

text \<open>Splitting a length-\<open>2A\<close> sum into its even- and odd-indexed halves.\<close>
lemma sum_pair_split:
  fixes f :: "nat \<Rightarrow> 'a::comm_monoid_add"
  shows "(\<Sum>m<2*A. f m) = (\<Sum>m<A. f (2*m)) + (\<Sum>m<A. f (2*m+1))"
proof (induct A)
  case 0 show ?case by simp
next
  case (Suc A)
  have "(\<Sum>m<2*Suc A. f m) = (\<Sum>m<2*A. f m) + f (2*A) + f (2*A+1)"
    by (simp add: mult_Suc_right)
  also have "\<dots> = ((\<Sum>m<A. f (2*m)) + (\<Sum>m<A. f (2*m+1))) + f (2*A) + f (2*A+1)"
    by (simp add: Suc.hyps)
  also have "\<dots> = (\<Sum>m<Suc A. f (2*m)) + (\<Sum>m<Suc A. f (2*m+1))"
    by (simp add: add.assoc add.left_commute)
  finally show ?case .
qed

text \<open>Evaluate \<open>inv_form\<close> at a position written as \<open>a\<cdot>B + c\<close> with \<open>c < B\<close>
  (\<open>B = 2^(8-s)\<close>): the div/mod resolve to \<open>a\<close> and \<open>c\<close> exactly. Done once here so
  the recursion lemmas avoid repeating it.\<close>
lemma inv_form_ac:
  assumes c: "c < 2^(8-s)"
  shows "inv_form s g (a * 2^(8-s) + c)
       = (\<Sum>m<2^s. g (c + m * 2^(8-s)) * zr ^ ((2 * brv s a + 1) * m * 2^(8-s)))"
  using c by (simp add: inv_form_def)

text \<open>Lower-leg recursion (exact identity): for \<open>off < 2^(7-s)\<close>, one step of the
  invariant at the even output block \<open>2a\<close> is the additive butterfly leg.\<close>
lemma inv_form_lower:
  fixes g :: "nat \<Rightarrow> int"
  assumes s: "s < 8" and off: "off < 2 ^ (7 - s)"
  shows "inv_form (Suc s) g (a * 2 ^ (8 - s) + off)
       = inv_form s g (a * 2 ^ (8 - s) + off)
         + zr ^ ((2 * brv s a + 1) * 2 ^ (7 - s))
           * inv_form s g (a * 2 ^ (8 - s) + off + 2 ^ (7 - s))"
proof -
  define e where "e = 2 * brv s a + 1"
  have suc:  "8 - s = Suc (7 - s)" using s by linarith
  have ssuc: "8 - Suc s = 7 - s"   using s by simp
  have B2L:  "(2::nat) ^ (8 - s) = 2 * 2 ^ (7 - s)" by (simp add: suc)
  have accL: "off < 2 ^ (8 - Suc s)" using off by (simp add: ssuc)
  have offB: "off < 2 ^ (8 - s)" using off by (simp add: B2L)
  have offLB: "off + 2 ^ (7 - s) < 2 ^ (8 - s)" using off by (simp add: B2L)
  have arw: "a * 2 ^ (8 - s) = (2 * a) * 2 ^ (8 - Suc s)" by (simp add: ssuc B2L)
  \<comment> \<open>Step 1: unfold LHS at level \<open>Suc s\<close>, block \<open>2a\<close>.\<close>
  have L1: "inv_form (Suc s) g (a * 2 ^ (8 - s) + off)
        = (\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (7 - s)) * zr ^ (e * m' * 2 ^ (7 - s)))"
  proof -
    have "inv_form (Suc s) g (a * 2 ^ (8 - s) + off)
        = inv_form (Suc s) g ((2 * a) * 2 ^ (8 - Suc s) + off)" by (simp add: arw)
    also have "\<dots> = (\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (8 - Suc s))
                      * zr ^ ((2 * brv (Suc s) (2 * a) + 1) * m' * 2 ^ (8 - Suc s)))"
      by (rule inv_form_ac[OF accL])
    also have "\<dots> = (\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (7 - s)) * zr ^ (e * m' * 2 ^ (7 - s)))"
      by (simp add: ssuc brv_double e_def)
    finally show ?thesis .
  qed
  \<comment> \<open>Step 2: even/odd split.\<close>
  have L2: "(\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (7 - s)) * zr ^ (e * m' * 2 ^ (7 - s)))
        = (\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7 - s)) * zr ^ (e * (2*m) * 2 ^ (7 - s)))
        + (\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7 - s)) * zr ^ (e * (2*m+1) * 2 ^ (7 - s)))"
    using sum_pair_split[where A = "2 ^ s"
            and f = "\<lambda>m'. g (off + m' * 2 ^ (7-s)) * zr ^ (e * m' * 2 ^ (7-s))"]
    by simp
  \<comment> \<open>Step 3: first half = invariant at \<open>off\<close>.\<close>
  have FIRST: "(\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7 - s)) * zr ^ (e * (2*m) * 2 ^ (7 - s)))
        = inv_form s g (a * 2 ^ (8 - s) + off)"
  proof -
    have iac: "inv_form s g (a * 2 ^ (8 - s) + off)
        = (\<Sum>m<2 ^ s. g (off + m * 2 ^ (8 - s)) * zr ^ (e * m * 2 ^ (8 - s)))"
      using inv_form_ac[OF offB, of g a] by (simp add: e_def)
    have "(\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7 - s)) * zr ^ (e * (2*m) * 2 ^ (7 - s)))
        = (\<Sum>m<2 ^ s. g (off + m * 2 ^ (8 - s)) * zr ^ (e * m * 2 ^ (8 - s)))"
    proof (rule sum.cong[OF refl])
      fix m :: nat assume "m \<in> {..<2 ^ s}"
      have b1: "off + (2*m) * 2 ^ (7-s) = off + m * 2 ^ (8-s)" by (simp add: B2L)
      have b2: "e * (2*m) * 2 ^ (7-s) = e * m * 2 ^ (8-s)" by (simp add: B2L)
      show "g (off + (2*m) * 2 ^ (7-s)) * zr ^ (e * (2*m) * 2 ^ (7-s))
          = g (off + m * 2 ^ (8-s)) * zr ^ (e * m * 2 ^ (8-s))"
        by (simp add: b1 b2)
    qed
    thus ?thesis by (simp add: iac)
  qed
  \<comment> \<open>Step 4: second half = twiddle times invariant at \<open>off + 2^(7-s)\<close>.\<close>
  have SECOND: "(\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7 - s)) * zr ^ (e * (2*m+1) * 2 ^ (7 - s)))
        = zr ^ (e * 2 ^ (7 - s)) * inv_form s g (a * 2 ^ (8 - s) + off + 2 ^ (7 - s))"
  proof -
    have iac: "inv_form s g (a * 2 ^ (8 - s) + off + 2 ^ (7 - s))
        = (\<Sum>m<2 ^ s. g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * zr ^ (e * m * 2 ^ (8-s)))"
    proof -
      have eq: "a * 2 ^ (8-s) + off + 2 ^ (7-s) = a * 2 ^ (8-s) + (off + 2 ^ (7-s))"
        by (simp add: add.assoc)
      show ?thesis unfolding eq using inv_form_ac[OF offLB, of g a] by (simp add: e_def)
    qed
    have "(\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7 - s)) * zr ^ (e * (2*m+1) * 2 ^ (7 - s)))
        = (\<Sum>m<2 ^ s. zr ^ (e * 2 ^ (7-s))
              * (g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * zr ^ (e * m * 2 ^ (8-s))))"
    proof (rule sum.cong[OF refl])
      fix m :: nat assume "m \<in> {..<2 ^ s}"
      have a1: "off + (2*m+1) * 2 ^ (7-s) = (off + 2 ^ (7-s)) + m * 2 ^ (8-s)"
        by (simp add: B2L algebra_simps)
      have a2: "e * (2*m+1) * 2 ^ (7-s) = e * 2 ^ (7-s) + e * m * 2 ^ (8-s)"
        by (simp add: B2L algebra_simps)
      show "g (off + (2*m+1) * 2 ^ (7-s)) * zr ^ (e * (2*m+1) * 2 ^ (7-s))
          = zr ^ (e * 2 ^ (7-s)) * (g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * zr ^ (e * m * 2 ^ (8-s)))"
        unfolding a1 a2 by (simp add: power_add mult.assoc mult.left_commute mult.commute)
    qed
    also have "\<dots> = zr ^ (e * 2 ^ (7-s))
          * (\<Sum>m<2 ^ s. g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * zr ^ (e * m * 2 ^ (8-s)))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = zr ^ (e * 2 ^ (7-s)) * inv_form s g (a * 2 ^ (8-s) + off + 2 ^ (7-s))"
      by (simp add: iac)
    finally show ?thesis .
  qed
  have "inv_form (Suc s) g (a * 2 ^ (8-s) + off)
      = (\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7-s)) * zr ^ (e * (2*m) * 2 ^ (7-s)))
      + (\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7-s)) * zr ^ (e * (2*m+1) * 2 ^ (7-s)))"
    using L1 L2 by simp
  also have "\<dots> = inv_form s g (a * 2 ^ (8-s) + off)
      + zr ^ (e * 2 ^ (7-s)) * inv_form s g (a * 2 ^ (8-s) + off + 2 ^ (7-s))"
    using FIRST SECOND by simp
  finally show ?thesis by (simp add: e_def)
qed

end
