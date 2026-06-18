(* Tier-2 Bridge 2 infrastructure: N-bit bit-reversal as a permutation of
   {0..<2^N}. ML-DSA's iterative in-place NTT leaves its output in bit-reversed
   order; relating it to AFP's natural-order FNTT needs this permutation. *)
theory Bitrev
  imports Main
begin

unbundle bit_operations_syntax

lemma bit_lt: "k < (2::nat)^N \<Longrightarrow> bit k j \<Longrightarrow> j < N"
  by (metis bit_take_bit_iff take_bit_nat_eq_self_iff)

text \<open>Bit of \<open>r + c\<cdot>2^N\<close> when \<open>r < 2^N\<close>: the low \<open>N\<close> bits come from \<open>r\<close>, the
  rest from \<open>c\<close>.\<close>
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

text \<open>\<open>brv N k\<close> reverses the low \<open>N\<close> bits of \<open>k\<close>: the LSB of \<open>k\<close> becomes the
  bit of weight \<open>2^(N-1)\<close>, etc.\<close>
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

text \<open>The defining property: the \<open>j\<close>-th bit of the reversal is the \<open>(N-1-j)\<close>-th
  bit of the original.\<close>
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

text \<open>\<open>brv N\<close> is an involution on \<open>N\<close>-bit values.\<close>
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

text \<open>Hence \<open>brv N\<close> permutes \<open>{0..<2^N}\<close>.\<close>
lemma brv_bij: "bij_betw (brv N) {0..<2^N} {0..<2^N}"
proof (rule bij_betw_byWitness[where f' = "brv N"])
  show "\<forall>k\<in>{0..<2^N}. brv N (brv N k) = k" by (auto simp: brv_brv)
  show "\<forall>k\<in>{0..<2^N}. brv N (brv N k) = k" by (auto simp: brv_brv)
  show "brv N ` {0..<2^N} \<subseteq> {0..<2^N}" by (auto simp: brv_lt)
  show "brv N ` {0..<2^N} \<subseteq> {0..<2^N}" by (auto simp: brv_lt)
qed

end
