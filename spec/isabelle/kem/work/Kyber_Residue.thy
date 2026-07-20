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

end
