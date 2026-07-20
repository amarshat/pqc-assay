(* Slice 3 (ML-KEM Tier-2), brick (c): connect the abstract 7-fold Cooley-Tukey
   recurrence (Kyber_Route.ntt_recurrence, the composed bflyK) to the FIPS-203
   forward-NTT closed form (128 degree-2 residues). This file starts the bridge:
   bit reversal, the normal twiddle as a power of zeta = 17 at the bit-reversed
   index, and the wrap-around zeta^128 = -1 (mod q).

   Numerically validated (scratchpad, before formalising):
   - composed bflyK == FIPS-203 forward NTT (200 random trials);
   - stage invariant value_s[n] = SUM m<2^s. g[c+m*2^(8-s)]
       * 17^((2*brv s a + 1) * m * 2^(7-s)) with c = n mod 2^(8-s), a = n div 2^(8-s)
     holds for s = 0..7 (the induction target);
   - twiddle closed form zntt(2^s + a) = 17^(2^(6-s) * (2*brv s a + 1)) for a < 2^s;
   - the concrete montgomery table satisfies zntt k = 17^(brv 7 k) mod q for k < 128. *)
theory Kyber_Residue
  imports Kyber_Route
begin

unbundle bit_operations_syntax

section \<open>Bit reversal of the low N bits\<close>

text \<open>Same content as the ML-DSA \<open>Bitrev\<close> theory (which lives in a different session).
  \<open>brv\<close> is small and pure, so it is re-derived here rather than coupling the sessions.\<close>

lemma bit_lt: "k < (2::nat)^N \<Longrightarrow> bit k j \<Longrightarrow> j < N"
  by (metis bit_take_bit_iff take_bit_nat_eq_self_iff)

text \<open>Bit of \<open>r + c*2^N\<close> when \<open>r < 2^N\<close>: the low \<open>N\<close> bits come from \<open>r\<close>, the rest from \<open>c\<close>.\<close>
lemma bit_add_push:
  assumes r: "r < (2::nat)^N"
  shows "bit (r + c * 2^N) j \<longleftrightarrow> (if j < N then bit r j else bit c (j - N))"
proof -
  have tr: "take_bit N r = r" using r by (simp add: take_bit_nat_eq_self)
  have disj: "take_bit N r AND push_bit N c = 0"
    by (auto simp: bit_eq_iff bit_simps)
  have "r + c * 2^N = take_bit N r + push_bit N c"
    by (simp add: tr push_bit_eq_mult)
  also have "\<dots> = take_bit N r OR push_bit N c"
    using disj by (rule disjunctive_add_eq_or)
  finally have "bit (r + c*2^N) j = (bit (take_bit N r) j \<or> bit (push_bit N c) j)"
    by (simp add: bit_or_iff)
  thus ?thesis by (auto simp: bit_take_bit_iff bit_push_bit_iff)
qed

fun brv :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "brv 0 k = 0"
| "brv (Suc N) k = brv N (k div 2) + (k mod 2) * 2^N"

lemma brv_lt: "brv N k < 2^N"
proof (induction N arbitrary: k)
  case 0 thus ?case by simp
next
  case (Suc N)
  have a: "brv N (k div 2) < 2^N" by (rule Suc.IH)
  have b: "(k mod 2) * 2^N \<le> 2^N"
    using mod_less_divisor[of 2 k] by (simp add: mult_le_mono1)
  have e: "brv (Suc N) k = brv N (k div 2) + (k mod 2) * 2^N" by simp
  from a b e have "brv (Suc N) k < 2^N + 2^N" by linarith
  thus ?case by simp
qed

lemma bit_brv: "bit (brv N k) j \<longleftrightarrow> j < N \<and> bit k (N - Suc j)"
proof (induction N arbitrary: k j)
  case 0 thus ?case by simp
next
  case (Suc N)
  have step: "bit (brv (Suc N) k) j
              = (if j < N then bit (brv N (k div 2)) j else bit (k mod 2) (j - N))"
    using brv_lt[of N "k div 2"] by (simp add: bit_add_push)
  show ?case
  proof (cases "j < N")
    case True
    have "bit (brv (Suc N) k) j = bit (brv N (k div 2)) j" using step True by simp
    also have "\<dots> = (j < N \<and> bit (k div 2) (N - Suc j))" by (rule Suc.IH)
    also have "\<dots> = (j < N \<and> bit k (Suc (N - Suc j)))" by (simp add: bit_Suc)
    also have "Suc (N - Suc j) = Suc N - Suc j" using True by simp
    finally show ?thesis using True by simp
  next
    case False
    show ?thesis
    proof (cases "j = N")
      case True
      have "bit (brv (Suc N) k) j = bit (k mod 2) 0" using step False True by simp
      also have "\<dots> = bit k 0" by (simp add: bit_0)
      finally show ?thesis using True by (simp add: bit_0)
    next
      case False
      with \<open>\<not> j < N\<close> have jg: "j > N" by simp
      have m2: "k mod 2 < (2::nat)^1" by simp
      have "\<not> bit (k mod 2) (j - N)" using bit_lt[OF m2] jg by force
      thus ?thesis using step jg by simp
    qed
  qed
qed

lemma brv_brv: "k < 2^N \<Longrightarrow> brv N (brv N k) = k"
proof (rule bit_eqI)
  fix j assume k: "k < 2^N"
  have idx: "j < N \<Longrightarrow> N - Suc (N - Suc j) = j"
  proof -
    assume j: "j < N"
    have "N - Suc (N - Suc j) = N - (N - j)" using j by (simp add: Suc_diff_Suc)
    also have "\<dots> = j" using j by simp
    finally show ?thesis .
  qed
  have "bit (brv N (brv N k)) j \<longleftrightarrow> (j < N \<and> bit k (N - Suc (N - Suc j)))"
    by (auto simp: bit_brv)
  also have "\<dots> \<longleftrightarrow> bit k j"
    using idx k bit_lt[of k N j] by auto
  finally show "bit (brv N (brv N k)) j = bit k j" .
qed

lemma brv_bij: "bij_betw (brv N) {0..<2^N} {0..<2^N}"
proof (rule bij_betw_byWitness[where f' = "brv N"])
  show "\<forall>k\<in>{0..<2^N}. brv N (brv N k) = k" by (auto simp: brv_brv)
  show "\<forall>k\<in>{0..<2^N}. brv N (brv N k) = k" by (auto simp: brv_brv)
  show "brv N ` {0..<2^N} \<subseteq> {0..<2^N}" by (auto simp: brv_lt)
  show "brv N ` {0..<2^N} \<subseteq> {0..<2^N}" by (auto simp: brv_lt)
qed

text \<open>The two recursion cases the stage step needs (even / odd argument).\<close>
lemma brv_double:  "brv (Suc s) (2*a)     = brv s a"       by simp
lemma brv_double1: "brv (Suc s) (2*a + 1) = brv s a + 2^s" by simp

section \<open>The normal twiddle is a power of zeta = 17 at the bit-reversed index\<close>

text \<open>The concrete montgomery table pulled back to the normal domain (\<open>zntt\<close>, defined in
  \<open>Kyber_Route\<close>) is \<open>17^(brv 7 k) mod q\<close>: the Kyber twiddle table is \<open>17^(brv 7 k) * 2^16\<close>
  and \<open>zntt\<close> divides out the \<open>2^16\<close>. Proven by evaluation over the 128-entry table (the
  ML-KEM analogue of the ML-DSA \<open>zt_eval_pow\<close>). Index 0 holds \<open>2^16 mod q\<close>, so the relation
  also holds there (\<open>zntt 0 = 1 = 17^0\<close>).\<close>
lemma zntt_eval_pow: "\<forall>i<128. zntt i = ((17::int) ^ (brv 7 i)) mod 3329"
  unfolding zntt_def by eval

lemma zntt_pow: "k < 128 \<Longrightarrow> zntt k = ((17::int) ^ (brv 7 k)) mod 3329"
  using zntt_eval_pow by simp

section \<open>zeta = 17 is a primitive 256th root of unity: zeta^128 = -1 (mod q)\<close>

lemma zwrap_eval: "((17::int) ^ 128) mod 3329 = 3328" by eval

lemma zwrap_cong: "[(17::int) ^ 128 = - 1] (mod 3329)"
  unfolding cong_def by eval

section \<open>The 7-layer schedule and the stage invariant\<close>

text \<open>One abstract layer of the ML-KEM schedule, indexed by step \<open>s = 0..6\<close>: stride
  \<open>2^(7-s)\<close>, block size \<open>2^(8-s)\<close>, twiddle base \<open>2^s\<close>. Matches the \<open>ntt_recurrence\<close>
  composition order (\<open>bstepK 0\<close> is the outermost-applied first layer).\<close>
definition bstepK :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
  "bstepK s g = bflyK (2^(7-s)) (2^(8-s)) (2^s) g"

fun applyNK :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
  "applyNK 0 g = g"
| "applyNK (Suc s) g = bstepK s (applyNK s g)"

text \<open>The 7-fold schedule unfolds to the explicit \<open>bflyK\<close> composition that is the
  right-hand side of \<open>ntt_recurrence\<close>.\<close>
lemma applyNK_7_eq:
  "applyNK 7 g = bflyK 2 4 64 (bflyK 4 8 32 (bflyK 8 16 16 (bflyK 16 32 8
       (bflyK 32 64 4 (bflyK 64 128 2 (bflyK 128 256 1 g))))))"
  by (simp add: bstepK_def eval_nat_numeral)

text \<open>The stage invariant (no inner mod; carried as a congruence mod q). After \<open>s\<close> layers,
  position \<open>n = a*B + c\<close> (with \<open>B = 2^(8-s)\<close>, \<open>A = 2^s\<close>, \<open>a = n div B\<close>, \<open>c = n mod B\<close>) holds
  the length-\<open>A\<close> sub-DFT of the stride-\<open>B\<close> subvector at offset \<open>c\<close>, evaluated at frequency
  \<open>2*brv\<^sub>s a + 1\<close>. Note the exponent factor is \<open>2^(7-s)\<close> (ML-KEM is the incomplete NTT with
  \<open>zeta = 17\<close> of order 256), one power of two less than the ML-DSA \<open>inv_form\<close>.\<close>
definition inv_formK :: "nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "inv_formK s g n =
     (\<Sum>m < 2^s. g (n mod 2^(8-s) + m * 2^(8-s))
                 * 17 ^ ((2 * brv s (n div 2^(8-s)) + 1) * m * 2^(7-s)))"

lemma inv_formK_0: "n < 256 \<Longrightarrow> inv_formK 0 g n = g n"
  by (simp add: inv_formK_def)

text \<open>Target specialisation: at \<open>s = 7\<close> the invariant is the FIPS-203 degree-2 residue
  coefficient. Position \<open>n = 2i + c\<close> (c the parity) holds \<open>SUM j<128. g(c + 2j) * 17^((2*brv 7 i + 1)*j)\<close>,
  i.e. the even (\<open>c=0\<close>) / odd (\<open>c=1\<close>) coefficient of \<open>f mod (X^2 - 17^(2*brv 7 i + 1))\<close>.\<close>
lemma inv_formK_7:
  "inv_formK 7 g n = (\<Sum>m<128. g (n mod 2 + m * 2) * 17 ^ ((2 * brv 7 (n div 2) + 1) * m))"
  by (simp add: inv_formK_def)

subsection \<open>Twiddle-index identity for the induction step\<close>

text \<open>Bit-reversal of a single top bit plus a low residue: \<open>brv\<^sub>7(2^s + a)\<close>. The bit \<open>2^s\<close>
  reverses to weight \<open>2^(6-s)\<close>; the low \<open>s\<close> bits \<open>a\<close> reverse and shift up to weight \<open>2^(7-s)\<close>.
  This is the ML-KEM analogue of ML-DSA \<open>brv8_pow_add\<close> (7 instead of 8 bits), giving the level-\<open>s\<close>
  twiddle \<open>zntt(2^s + a) = 17^(2^(6-s) * (2*brv s a + 1))\<close>.\<close>
lemma brv7_pow_add:
  assumes s: "s < 7" and a: "a < 2^s"
  shows "brv 7 (2^s + a) = 2^(6-s) + brv s a * 2^(7-s)"
proof (rule bit_eqI)
  fix j :: nat
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
  have res: "bit (2^(6-s) + brv s a * 2^(7-s)) j
             = (if j < 7 - s then j = 6 - s else bit (brv s a) (j - (7 - s)))"
  proof -
    have r: "(2::nat)^(6-s) < 2^(7-s)" using s by simp
    have "bit (2^(6-s) + brv s a * 2^(7-s)) j
          = (if j < 7-s then bit ((2::nat)^(6-s)) j else bit (brv s a) (j-(7-s)))"
      using bit_add_push[OF r, of "brv s a" j] by simp
    moreover have "bit ((2::nat)^(6-s)) j = (j = 6 - s)"
      by (auto simp: bit_simps)
    ultimately show ?thesis by simp
  qed
  show "bit (brv 7 (2^s + a)) j = bit (2^(6-s) + brv s a * 2^(7-s)) j"
  proof (cases "j < 7")
    case True
    have "bit (brv 7 (2^s + a)) j = bit (2^s + a) (6 - j)"
      using True by (simp add: bit_brv)
    also have "\<dots> = (if 6 - j < s then bit a (6 - j) else 6 - j = s)" by (subst arg) simp
    finally have L: "bit (brv 7 (2^s + a)) j = (if 6-j < s then bit a (6-j) else 6-j = s)" .
    show ?thesis
    proof (cases "j < 7 - s")
      case True
      have "\<not> 6 - j < s" using True s by linarith
      hence "bit (brv 7 (2^s+a)) j = (6 - j = s)" using L by simp
      moreover have "(6 - j = s) = (j = 6 - s)" using True s \<open>j<7\<close> by linarith
      ultimately show ?thesis using True res by simp
    next
      case False
      have hj: "6 - j < s" using False \<open>j<7\<close> s by linarith
      hence "bit (brv 7 (2^s+a)) j = bit a (6 - j)" using L by simp
      moreover have "bit (brv s a) (j - (7-s)) = bit a (6 - j)"
      proof -
        have lt: "j - (7 - s) < s" using False \<open>j<7\<close> s by linarith
        have "bit (brv s a) (j-(7-s)) = bit a (s - Suc (j - (7-s)))"
          using lt by (simp add: bit_brv)
        moreover have "s - Suc (j - (7-s)) = 6 - j" using False \<open>j<7\<close> s by linarith
        ultimately show ?thesis by simp
      qed
      ultimately show ?thesis using False res by simp
    qed
  next
    case False
    have "\<not> j < 7 - s" using False by simp
    have "bit (brv 7 (2^s+a)) j = False" using False by (simp add: bit_brv)
    moreover have "bit (2^(6-s) + brv s a * 2^(7-s)) j = bit (brv s a) (j-(7-s))"
      using res \<open>\<not> j < 7 - s\<close> by simp
    moreover have "brv s a < 2^s" by (rule brv_lt)
    hence "bit (brv s a) (j - (7-s)) = False"
      using bit_lt[of "brv s a" s "j-(7-s)"] False s by force
    ultimately show ?thesis by simp
  qed
qed

text \<open>Hence the level-\<open>s\<close> twiddle in normal-domain closed form.\<close>
lemma zntt_level:
  assumes s: "s < 7" and a: "a < 2^s"
  shows "zntt (2^s + a) = (17 ^ (2^(6-s) + brv s a * 2^(7-s))) mod 3329"
proof -
  have lt: "(2::nat)^s + a < 128"
  proof -
    have sle: "Suc s \<le> 7" using s by simp
    have "(2::nat)^s + a < 2^(Suc s)" using a by simp
    also have "(2::nat)^(Suc s) \<le> 2^7"
      using power_increasing[of "Suc s" 7 "2::nat"] sle by simp
    finally show ?thesis by simp
  qed
  show ?thesis using zntt_pow[OF lt] brv7_pow_add[OF s a] by simp
qed

subsection \<open>Stage recursion lemmas\<close>

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

text \<open>Evaluate \<open>inv_formK\<close> at a position written as \<open>a*B + c\<close> with \<open>c < B\<close> (\<open>B = 2^(8-s)\<close>):
  the div/mod resolve to \<open>a\<close> and \<open>c\<close>. Note the position stride \<open>2^(8-s)\<close> and the exponent
  factor \<open>2^(7-s)\<close> differ (the incomplete-NTT signature).\<close>
lemma inv_formK_ac:
  assumes c: "c < 2^(8-s)"
  shows "inv_formK s g (a * 2^(8-s) + c)
       = (\<Sum>m<2^s. g (c + m * 2^(8-s)) * 17 ^ ((2 * brv s a + 1) * m * 2^(7-s)))"
  using c by (simp add: inv_formK_def)

text \<open>Lower-leg recursion (exact): one step of the invariant at the even output block \<open>2a\<close>
  is the additive butterfly leg. ML-KEM analogue of ML-DSA \<open>inv_form_lower\<close>; the position
  powers are unchanged, the exponent powers drop by one (\<open>2^(7-s)\<close> becomes \<open>2^(6-s)\<close>).\<close>
lemma inv_formK_lower:
  fixes g :: "nat \<Rightarrow> int"
  assumes s: "s < 7" and off: "off < 2 ^ (7 - s)"
  shows "inv_formK (Suc s) g (a * 2 ^ (8 - s) + off)
       = inv_formK s g (a * 2 ^ (8 - s) + off)
         + 17 ^ ((2 * brv s a + 1) * 2 ^ (6 - s))
           * inv_formK s g (a * 2 ^ (8 - s) + off + 2 ^ (7 - s))"
proof -
  define e where "e = 2 * brv s a + 1"
  have suc:   "8 - s = Suc (7 - s)" using s by linarith
  have h7:    "7 - s = Suc (6 - s)" using s by linarith
  have ssuc:  "8 - Suc s = 7 - s"   using s by simp
  have ssuc2: "7 - Suc s = 6 - s"   using s by simp
  have B2L:   "(2::nat) ^ (8 - s) = 2 * 2 ^ (7 - s)" by (simp add: suc)
  have E2E:   "(2::nat) ^ (7 - s) = 2 * 2 ^ (6 - s)" by (simp add: h7)
  have accL:  "off < 2 ^ (8 - Suc s)" using off by (simp add: ssuc)
  have offB:  "off < 2 ^ (8 - s)" using off by (simp add: B2L)
  have offLB: "off + 2 ^ (7 - s) < 2 ^ (8 - s)" using off by (simp add: B2L)
  have arw:   "a * 2 ^ (8 - s) = (2 * a) * 2 ^ (8 - Suc s)" by (simp add: ssuc B2L)
  have L1: "inv_formK (Suc s) g (a * 2 ^ (8 - s) + off)
        = (\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (7 - s)) * 17 ^ (e * m' * 2 ^ (6 - s)))"
  proof -
    have "inv_formK (Suc s) g (a * 2 ^ (8 - s) + off)
        = inv_formK (Suc s) g ((2 * a) * 2 ^ (8 - Suc s) + off)" by (simp add: arw)
    also have "\<dots> = (\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (8 - Suc s))
                      * 17 ^ ((2 * brv (Suc s) (2 * a) + 1) * m' * 2 ^ (7 - Suc s)))"
      by (rule inv_formK_ac[OF accL])
    also have "\<dots> = (\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (7 - s)) * 17 ^ (e * m' * 2 ^ (6 - s)))"
      by (simp add: ssuc ssuc2 brv_double e_def)
    finally show ?thesis .
  qed
  have L2: "(\<Sum>m'<2 ^ Suc s. g (off + m' * 2 ^ (7 - s)) * 17 ^ (e * m' * 2 ^ (6 - s)))
        = (\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7 - s)) * 17 ^ (e * (2*m) * 2 ^ (6 - s)))
        + (\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7 - s)) * 17 ^ (e * (2*m+1) * 2 ^ (6 - s)))"
    using sum_pair_split[where A = "2 ^ s"
            and f = "\<lambda>m'. g (off + m' * 2 ^ (7-s)) * 17 ^ (e * m' * 2 ^ (6-s))"]
    by simp
  have FIRST: "(\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7 - s)) * 17 ^ (e * (2*m) * 2 ^ (6 - s)))
        = inv_formK s g (a * 2 ^ (8 - s) + off)"
  proof -
    have iac: "inv_formK s g (a * 2 ^ (8 - s) + off)
        = (\<Sum>m<2 ^ s. g (off + m * 2 ^ (8 - s)) * 17 ^ (e * m * 2 ^ (7 - s)))"
      using inv_formK_ac[OF offB, of g a] by (simp add: e_def)
    have "(\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7 - s)) * 17 ^ (e * (2*m) * 2 ^ (6 - s)))
        = (\<Sum>m<2 ^ s. g (off + m * 2 ^ (8 - s)) * 17 ^ (e * m * 2 ^ (7 - s)))"
    proof (rule sum.cong[OF refl])
      fix m :: nat assume "m \<in> {..<2 ^ s}"
      have b1: "off + (2*m) * 2 ^ (7-s) = off + m * 2 ^ (8-s)" by (simp add: B2L)
      have b2: "e * (2*m) * 2 ^ (6-s) = e * m * 2 ^ (7-s)" by (simp add: E2E)
      show "g (off + (2*m) * 2 ^ (7-s)) * 17 ^ (e * (2*m) * 2 ^ (6-s))
          = g (off + m * 2 ^ (8-s)) * 17 ^ (e * m * 2 ^ (7-s))"
        by (simp add: b1 b2)
    qed
    thus ?thesis by (simp add: iac)
  qed
  have SECOND: "(\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7 - s)) * 17 ^ (e * (2*m+1) * 2 ^ (6 - s)))
        = 17 ^ (e * 2 ^ (6 - s)) * inv_formK s g (a * 2 ^ (8 - s) + off + 2 ^ (7 - s))"
  proof -
    have iac: "inv_formK s g (a * 2 ^ (8 - s) + off + 2 ^ (7 - s))
        = (\<Sum>m<2 ^ s. g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * 17 ^ (e * m * 2 ^ (7-s)))"
    proof -
      have eq: "a * 2 ^ (8-s) + off + 2 ^ (7-s) = a * 2 ^ (8-s) + (off + 2 ^ (7-s))"
        by (simp add: add.assoc)
      show ?thesis unfolding eq using inv_formK_ac[OF offLB, of g a] by (simp add: e_def)
    qed
    have "(\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7 - s)) * 17 ^ (e * (2*m+1) * 2 ^ (6 - s)))
        = (\<Sum>m<2 ^ s. 17 ^ (e * 2 ^ (6-s))
              * (g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * 17 ^ (e * m * 2 ^ (7-s))))"
    proof (rule sum.cong[OF refl])
      fix m :: nat assume "m \<in> {..<2 ^ s}"
      have a1: "off + (2*m+1) * 2 ^ (7-s) = (off + 2 ^ (7-s)) + m * 2 ^ (8-s)"
        by (simp add: B2L algebra_simps)
      have a2: "e * (2*m+1) * 2 ^ (6-s) = e * 2 ^ (6-s) + e * m * 2 ^ (7-s)"
        by (simp add: E2E algebra_simps)
      show "g (off + (2*m+1) * 2 ^ (7-s)) * 17 ^ (e * (2*m+1) * 2 ^ (6-s))
          = 17 ^ (e * 2 ^ (6-s)) * (g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * 17 ^ (e * m * 2 ^ (7-s)))"
        unfolding a1 a2 by (simp add: power_add mult.assoc mult.left_commute mult.commute)
    qed
    also have "\<dots> = 17 ^ (e * 2 ^ (6-s))
          * (\<Sum>m<2 ^ s. g ((off + 2 ^ (7-s)) + m * 2 ^ (8-s)) * 17 ^ (e * m * 2 ^ (7-s)))"
      by (simp add: sum_distrib_left)
    also have "\<dots> = 17 ^ (e * 2 ^ (6-s)) * inv_formK s g (a * 2 ^ (8-s) + off + 2 ^ (7-s))"
      by (simp add: iac)
    finally show ?thesis .
  qed
  have "inv_formK (Suc s) g (a * 2 ^ (8-s) + off)
      = (\<Sum>m<2 ^ s. g (off + (2*m) * 2 ^ (7-s)) * 17 ^ (e * (2*m) * 2 ^ (6-s)))
      + (\<Sum>m<2 ^ s. g (off + (2*m+1) * 2 ^ (7-s)) * 17 ^ (e * (2*m+1) * 2 ^ (6-s)))"
    using L1 L2 by simp
  also have "\<dots> = inv_formK s g (a * 2 ^ (8-s) + off)
      + 17 ^ (e * 2 ^ (6-s)) * inv_formK s g (a * 2 ^ (8-s) + off + 2 ^ (7-s))"
    using FIRST SECOND by simp
  finally show ?thesis by (simp add: e_def)
qed

end
