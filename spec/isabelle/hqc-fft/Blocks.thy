theory Blocks
  imports NovelBasis
begin

text \<open>Polynomials cut into blocks of \<open>W\<close> coefficients. \<open>bnd W p\<close>: \<open>p\<close> has no coefficient at or
  above \<open>W\<close>. \<open>blk W j f\<close> is block \<open>j\<close>, \<open>bmap n W h f\<close> applies \<open>h\<close> to each of the \<open>n\<close> blocks.
  The basis conversion's layers are \<open>bmap\<close>s of one block operation.\<close>

definition bnd :: "nat \<Rightarrow> 'a :: zero poly \<Rightarrow> bool" where
  "bnd W p \<longleftrightarrow> (\<forall>k \<ge> W. coeff p k = 0)"

definition blk :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: zero poly \<Rightarrow> 'a poly" where
  "blk W j f = poly_cutoff W (poly_shift (W * j) f)"

definition bmap :: "nat \<Rightarrow> nat \<Rightarrow> ('a :: comm_ring_1 poly \<Rightarrow> 'a poly) \<Rightarrow> 'a poly \<Rightarrow> 'a poly" where
  "bmap n W h f = (\<Sum>j<n. h (blk W j f) * monom 1 (W * j))"

lemma coeff_mult_monom: "coeff (p * monom c n) k = (if k < n then 0 else c * coeff p (k - n))"
  by (simp add: mult.commute[of p] coeff_monom_mult)

lemma bnd_cutoff: "bnd W (poly_cutoff W p)"
  by (simp add: bnd_def coeff_poly_cutoff)

lemma bnd_cutoff_id: "bnd W p \<Longrightarrow> poly_cutoff W p = p"
  by (rule poly_eqI) (auto simp: bnd_def coeff_poly_cutoff)

lemma bnd_add: "bnd W p \<Longrightarrow> bnd W q \<Longrightarrow> bnd W (p + q)"
  by (simp add: bnd_def)

lemma bnd_sum: "(\<And>i. i \<in> S \<Longrightarrow> bnd W (h i)) \<Longrightarrow> bnd W (\<Sum>i\<in>S. h i)"
  by (induction S rule: infinite_finite_induct) (simp_all add: bnd_def coeff_sum)

lemma bnd_mono: "bnd V p \<Longrightarrow> V \<le> W \<Longrightarrow> bnd W p"
  by (simp add: bnd_def)

lemma bnd_smult: "bnd W p \<Longrightarrow> bnd W (smult c p)"
  by (simp add: bnd_def)

lemma bnd_mult_monom:
  "bnd V p \<Longrightarrow> V + s \<le> W \<Longrightarrow> bnd W (p * monom 1 s)"
  by (auto simp: bnd_def coeff_mult_monom)

lemma bnd_degree: "p = 0 \<or> degree p < W \<Longrightarrow> bnd W p"
  by (auto simp: bnd_def coeff_eq_0)

lemma bnd_iff_degree: "bnd W p \<longleftrightarrow> p = 0 \<or> degree p < W"
proof
  assume b: "bnd W p"
  show "p = 0 \<or> degree p < W"
  proof (rule ccontr)
    assume "\<not> (p = 0 \<or> degree p < W)"
    then have "p \<noteq> 0" "degree p \<ge> W" by auto
    then show False using b leading_coeff_0_iff[of p] by (simp add: bnd_def)
  qed
qed (rule bnd_degree)

lemma bnd_mult:
  assumes "bnd V p" "bnd U q" "V + U \<le> W + 1"
  shows "bnd W (p * q)"
proof -
  have "p * q = 0 \<or> degree (p * q) < W"
  proof (cases "p = 0 \<or> q = 0")
    case True then show ?thesis by auto
  next
    case False
    then have "degree p < V" "degree q < U" using assms by (auto simp: bnd_iff_degree)
    then show ?thesis using assms(3) degree_mult_le[of p q] by linarith
  qed
  then show ?thesis by (rule bnd_degree)
qed

text \<open>The coefficient of a packed sum: only the block that holds position \<open>W j + t\<close> contributes.\<close>

lemma coeff_packed:
  fixes B :: "nat \<Rightarrow> 'a :: comm_ring_1 poly"
  assumes b: "\<And>i. i < n \<Longrightarrow> bnd W (B i)" and t: "t < W"
  shows "coeff (\<Sum>i<n. B i * monom 1 (W * i)) (W * j + t) = (if j < n then coeff (B j) t else 0)"
proof -
  have tm: "coeff (B i * monom 1 (W * i)) (W * j + t) = (if i = j then coeff (B i) t else 0)" if "i < n" for i
  proof (cases "i = j")
    case True then show ?thesis by (simp add: coeff_mult_monom)
  next
    case False
    show ?thesis
    proof (cases "W * i \<le> W * j + t")
      case True
      have "i < j"
      proof (rule ccontr)
        assume "\<not> i < j"
        then have "Suc j \<le> i" using \<open>i \<noteq> j\<close> by simp
        then have "W * Suc j \<le> W * i" by (rule mult_le_mono2)
        then show False using True t by simp
      qed
      then have "W * Suc i \<le> W * j" by (intro mult_le_mono2) simp
      then have "W * j + t - W * i \<ge> W" by simp
      then show ?thesis using False True b[OF that] by (simp add: coeff_mult_monom bnd_def)
    next
      case False then show ?thesis using \<open>i \<noteq> j\<close> by (simp add: coeff_mult_monom)
    qed
  qed
  have "coeff (\<Sum>i<n. B i * monom 1 (W * i)) (W * j + t) = (\<Sum>i<n. coeff (B i * monom 1 (W * i)) (W * j + t))"
    by (simp add: coeff_sum)
  also have "\<dots> = (\<Sum>i<n. if i = j then coeff (B i) t else 0)"
    by (rule sum.cong) (simp_all add: tm)
  finally have "coeff (\<Sum>i<n. B i * monom 1 (W * i)) (W * j + t) = (\<Sum>i<n. if i = j then coeff (B i) t else 0)" .
  then show ?thesis by simp
qed

lemma blk_packed:
  fixes B :: "nat \<Rightarrow> 'a :: comm_ring_1 poly"
  assumes "\<And>i. i < n \<Longrightarrow> bnd W (B i)"
  shows "blk W j (\<Sum>i<n. B i * monom 1 (W * i)) = (if j < n then B j else 0)"
proof (rule poly_eqI)
  fix t
  show "coeff (blk W j (\<Sum>i<n. B i * monom 1 (W * i))) t = coeff (if j < n then B j else 0) t"
  proof (cases "t < W")
    case True
    have c: "coeff (\<Sum>i<n. B i * monom 1 (W * i)) (W * j + t) = (if j < n then coeff (B j) t else 0)"
      by (rule coeff_packed[where B=B and W=W and n=n and t=t and j=j]) (simp_all add: assms True)
    then show ?thesis using True
      by (simp add: blk_def coeff_poly_cutoff coeff_poly_shift add.commute)
  next
    case False
    then show ?thesis using assms by (auto simp: blk_def coeff_poly_cutoff bnd_def)
  qed
qed

theorem bmap_packed:
  fixes B :: "nat \<Rightarrow> 'a :: comm_ring_1 poly"
  assumes "\<And>i. i < n \<Longrightarrow> bnd W (B i)"
  shows "bmap n W h (\<Sum>i<n. B i * monom 1 (W * i)) = (\<Sum>i<n. h (B i) * monom 1 (W * i))"
  unfolding bmap_def by (rule sum.cong) (simp_all add: blk_packed[OF assms])

end
