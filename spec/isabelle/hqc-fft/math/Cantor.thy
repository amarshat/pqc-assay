theory Cantor
  imports Main
begin

text \<open>The subspace polynomials of a Cantor basis, as functions on a commutative ring of characteristic 2.
  \<open>sv i\<close> is the polynomial \<open>s\<^sub>i\<close> with \<open>s\<^sub>0 = x\<close> and \<open>s\<^sub>i\<^sub>+\<^sub>1 = s\<^sub>i\<^sup>2 + s\<^sub>i\<close>; a Cantor basis
  is a sequence \<open>\<beta>\<close> with \<open>\<beta>\<^sub>0 = 1\<close> and \<open>\<beta>\<^sub>j\<^sub>+\<^sub>1\<^sup>2 + \<beta>\<^sub>j\<^sub>+\<^sub>1 = \<beta>\<^sub>j\<close>; \<open>cantor \<beta> v\<close> is the
  element whose coordinates in that basis are the bits of \<open>v\<close>. The result is
  \<open>s\<^sub>i(cantor v) = cantor (v div 2\<^sup>i)\<close>, which is how the additive FFT computes its twiddles.\<close>

class char2 = comm_ring_1 +
  assumes one_plus_one: "1 + 1 = (0 :: 'a)"
begin

lemma two_zero [simp]: "(2 :: 'a) = 0"
  using one_plus_one by (simp only: one_add_one)

lemma add_self [simp]: "x + x = 0"
  by (simp only: mult_2[symmetric] two_zero mult_zero_left)

lemma sq_add: "(x + y) * (x + y) = x * x + y * y"
proof -
  have "(x + y) * (x + y) = x * x + y * y + (x * y + x * y)"
    by (simp add: algebra_simps del: add_self)
  then show ?thesis by (simp only: add_self add_0_right)
qed

end

fun sv :: "nat \<Rightarrow> 'a :: char2 \<Rightarrow> 'a" where
  "sv 0 x = x"
| "sv (Suc i) x = sv i x * sv i x + sv i x"

lemma sv_add: "sv i (x + y) = sv i x + sv i y"
  by (induction i) (simp_all add: sq_add ac_simps)

lemma sv_zero [simp]: "sv i 0 = 0"
  by (induction i) simp_all

lemma sv_Suc': "sv (Suc i) x = sv i (sv (Suc 0) x)"
proof (induction i arbitrary: x)
  case 0 then show ?case by simp
next
  case (Suc i)
  have "sv (Suc (Suc i)) x = sv (Suc i) x * sv (Suc i) x + sv (Suc i) x" by simp
  also have "\<dots> = sv i (sv (Suc 0) x) * sv i (sv (Suc 0) x) + sv i (sv (Suc 0) x)"
    using Suc by simp
  also have "\<dots> = sv (Suc i) (sv (Suc 0) x)" by simp
  finally show ?case .
qed

text \<open>A Cantor basis of length \<open>n\<close> (GF(2^64) has one of length 64 and no longer).\<close>

definition cantor_basis :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: char2) \<Rightarrow> bool" where
  "cantor_basis n \<beta> \<longleftrightarrow> \<beta> 0 = 1 \<and> (\<forall>j. Suc j < n \<longrightarrow> \<beta> (Suc j) * \<beta> (Suc j) + \<beta> (Suc j) = \<beta> j)"

fun cantor_from :: "(nat \<Rightarrow> 'a :: char2) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "cantor_from \<beta> k v = (if v = 0 then 0
     else (if odd v then \<beta> k else 0) + cantor_from \<beta> (Suc k) (v div 2))"

declare cantor_from.simps [simp del]

definition cantor :: "(nat \<Rightarrow> 'a :: char2) \<Rightarrow> nat \<Rightarrow> 'a" where
  "cantor \<beta> v = cantor_from \<beta> 0 v"

lemma sv1_shift:
  assumes "cantor_basis n \<beta>" "v < 2 ^ (n - Suc k)"
  shows "sv (Suc 0) (cantor_from \<beta> (Suc k) v) = cantor_from \<beta> k v"
  using assms(2)
proof (induction v arbitrary: k rule: less_induct)
  case (less v)
  show ?case
  proof (cases "v = 0")
    case True then show ?thesis by (simp add: cantor_from.simps)
  next
    case False
    then have lt: "v div 2 < v" by simp
    have nk: "Suc k < n" using False less.prems by (cases "n - Suc k") auto
    have bnd: "v div 2 < 2 ^ (n - Suc (Suc k))"
      using less.prems nk by (simp add: Suc_diff_Suc less_mult_imp_div_less power_Suc2[symmetric])
    have b: "sv (Suc 0) (\<beta> (Suc k)) = \<beta> k" using assms(1) nk by (simp add: cantor_basis_def)
    have "sv (Suc 0) (cantor_from \<beta> (Suc k) v)
        = sv (Suc 0) (if odd v then \<beta> (Suc k) else 0) + sv (Suc 0) (cantor_from \<beta> (Suc (Suc k)) (v div 2))"
      using False by (simp only: cantor_from.simps[of \<beta> "Suc k" v] if_False sv_add)
    also have "\<dots> = (if odd v then \<beta> k else 0) + cantor_from \<beta> (Suc k) (v div 2)"
    proof -
      have "sv (Suc 0) (if odd v then \<beta> (Suc k) else 0) = (if odd v then \<beta> k else 0)"
        using b by (cases "odd v") (simp_all only: if_True if_False not_False_eq_True sv_zero)
      then show ?thesis by (simp only: less.IH[OF lt bnd])
    qed
    also have "\<dots> = cantor_from \<beta> k v" using False by (simp add: cantor_from.simps[of \<beta> k v])
    finally show ?thesis .
  qed
qed

lemma sv1_cantor:
  assumes "cantor_basis n \<beta>" "v < 2 ^ n"
  shows "sv (Suc 0) (cantor \<beta> v) = cantor \<beta> (v div 2)"
proof (cases "v = 0")
  case True then show ?thesis by (simp add: cantor_def cantor_from.simps)
next
  case False
  have b0: "sv (Suc 0) (\<beta> 0) = 0" using assms(1) by (simp add: cantor_basis_def one_plus_one)
  have bnd: "v div 2 < 2 ^ (n - Suc 0)"
    using assms(2) False by (cases n) (simp_all add: less_mult_imp_div_less)
  have "sv (Suc 0) (cantor \<beta> v)
      = sv (Suc 0) (if odd v then \<beta> 0 else 0) + sv (Suc 0) (cantor_from \<beta> (Suc 0) (v div 2))"
    using False by (simp only: cantor_def cantor_from.simps[of \<beta> 0 v] if_False sv_add)
  also have "\<dots> = cantor \<beta> (v div 2)"
  proof -
    have "sv (Suc 0) (if odd v then \<beta> 0 else 0) = 0" using b0 by (cases "odd v") (simp_all only: if_True if_False not_False_eq_True sv_zero)
    then show ?thesis by (simp only: sv1_shift[OF assms(1) bnd] cantor_def add_0_left)
  qed
  finally show ?thesis .
qed

lemma cantor_from_sum:
  "v < 2 ^ N \<Longrightarrow> cantor_from \<beta> k v = (\<Sum>i<N. if bit v i then \<beta> (i + k) else 0)"
proof (induction N arbitrary: v k)
  case 0 then show ?case by (simp add: cantor_from.simps)
next
  case (Suc N)
  have h: "v div 2 < 2 ^ N" using Suc.prems by (simp add: less_mult_imp_div_less power_Suc2[symmetric])
  have "cantor_from \<beta> k v = (if odd v then \<beta> k else 0) + cantor_from \<beta> (Suc k) (v div 2)"
    by (cases "v = 0") (simp_all add: cantor_from.simps[of \<beta> k v] cantor_from.simps[of \<beta> "Suc k" 0] cantor_from.simps[of \<beta> k 0])
  also have "\<dots> = (if bit v 0 then \<beta> (0 + k) else 0) + (\<Sum>i<N. if bit v (Suc i) then \<beta> (Suc i + k) else 0)"
    by (simp add: Suc.IH[OF h] bit_Suc bit_0 cong: if_cong)
  also have "\<dots> = (\<Sum>i<Suc N. if bit v i then \<beta> (i + k) else 0)"
    by (simp only: sum.lessThan_Suc_shift)
  finally show ?case .
qed

lemma cantor_sum: "v < 2 ^ N \<Longrightarrow> cantor \<beta> v = (\<Sum>i<N. if bit v i then \<beta> i else 0)"
  unfolding cantor_def by (subst cantor_from_sum) (simp_all cong: if_cong)

theorem sv_cantor:
  assumes "cantor_basis n \<beta>" "v < 2 ^ n"
  shows "sv i (cantor \<beta> v) = cantor \<beta> (v div 2 ^ i)"
  using assms(2)
proof (induction i arbitrary: v)
  case 0 then show ?case by simp
next
  case (Suc i)
  have "sv (Suc i) (cantor \<beta> v) = sv i (cantor \<beta> (v div 2))"
    by (subst sv_Suc') (simp only: sv1_cantor[OF assms(1) Suc.prems])
  also have "\<dots> = cantor \<beta> (v div 2 div 2 ^ i)" by (rule Suc.IH) (use Suc.prems in simp)
  also have "\<dots> = cantor \<beta> (v div 2 ^ Suc i)" by (simp add: div_mult2_eq)
  finally show ?case .
qed

end
