theory BC
  imports Blocks
begin

text \<open>The inverse basis conversion (\<open>ibc\<close>) of the additive-FFT multiplier, as an algorithm on
  packed polynomials, and the theorem that it maps novel-basis coordinates to the polynomial:
  digits \<open>D\<^sub>d\<close> of width \<open>u\<close> at positions \<open>u d\<close> go to \<open>\<Sum> D\<^sub>d \<cdot> (X\<^sub>d \<circ> x\<^sup>u)\<close>.

  One layer \<open>mulBlock L T\<close> replaces a block \<open>r + q x\<^sup>L\<close> by \<open>q (x\<^sup>L + x\<^sup>T) + r\<close>. \<open>irad\<close> is the radix
  recombination: digits \<open>G\<^sub>c\<close> at positions \<open>u 2\<^sup>M c\<close> become \<open>\<Sum> G\<^sub>c \<sigma>\<^sup>c\<close> with
  \<open>\<sigma> = s\<^sub>M \<circ> x\<^sup>u\<close>, \<open>M = 2\<^sup>j\<close>. A conversion is a schedule tree: a leaf is the identity on one
  or two digits; \<open>Nd j hi lo\<close> converts each block of \<open>2\<^sup>M\<close> digits by \<open>lo\<close>, the blocks as
  digits of width \<open>u 2\<^sup>M\<close> by \<open>hi\<close>, and recombines in powers of \<open>\<sigma>\<close>.\<close>

lemma pcompose_monom_c: "pcompose (monom c n) q = smult c ((q :: 'a :: comm_ring_1 poly) ^ n)"
proof -
  have "monom c n = smult c (monom 1 n)" by (simp add: smult_monom)
  then show ?thesis by (simp add: pcompose_smult pcompose_monom1)
qed

lemma poly_sum_lt:
  "degree p < N \<Longrightarrow> p = (\<Sum>c<N. monom (coeff p c) c)"
  by (rule poly_eqI) (auto simp: coeff_sum coeff_eq_0 sum.If_cases)

lemma pcompose_expand:
  "degree p < N \<Longrightarrow> pcompose p q = (\<Sum>c<N. smult (coeff p c) ((q :: 'a :: comm_ring_1 poly) ^ c))"
  by (subst poly_sum_lt[of p N]) (simp_all add: pcompose_sum pcompose_monom_c coeff_sum)

lemma sum_lt_mult:
  "(\<Sum>d<(m :: nat) * n. h d) = (\<Sum>b<n. \<Sum>a<m. h (a + m * b))"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "(\<Sum>d<m * Suc n. h d) = (\<Sum>d<m * n + m. h d)" by (simp add: algebra_simps)
  also have "\<dots> = (\<Sum>d<m * n. h d) + (\<Sum>a<m. h (a + m * n))"
    by (simp add: sum_lessThan_add)
  finally show ?case using Suc by simp
qed

lemma degree_sp: "degree (sp i :: 'a :: char2 poly) \<le> 2 ^ i"
proof (induction i)
  case 0 then show ?case by (simp add: degree_pCons_le)
next
  case (Suc i)
  have m: "degree (sp i * sp i :: 'a poly) \<le> 2 ^ i + 2 ^ i"
    using degree_mult_le[of "sp i :: 'a poly" "sp i"] Suc by linarith
  have "degree (sp i * sp i + sp i :: 'a poly) \<le> 2 ^ i + 2 ^ i"
    by (rule degree_add_le[OF m]) (use Suc in simp)
  then show ?case by (simp add: mult_2)
qed

lemma degree_XPf: "degree (XPf i k :: 'a :: char2 poly) \<le> 2 ^ i * k"
proof (induction k arbitrary: i rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k = 0")
    case True then show ?thesis by simp
  next
    case False
    then have lt: "k div 2 < k" by simp
    have b: "degree (XPf (Suc i) (k div 2) :: 'a poly) \<le> 2 ^ Suc i * (k div 2)" by (rule less.IH[OF lt])
    show ?thesis
    proof (cases "odd k")
      case True
      have e: "XPf i k = sp i * (XPf (Suc i) (k div 2) :: 'a poly)" using True by (subst XPf_unfold) simp
      have "degree (XPf i k :: 'a poly) \<le> 2 ^ i + 2 ^ Suc i * (k div 2)"
        unfolding e by (rule order_trans[OF degree_mult_le add_mono[OF degree_sp b]])
      also have "2 ^ i + 2 ^ Suc i * (k div 2) = 2 ^ i * (2 * (k div 2) + 1)" by (simp add: algebra_simps)
      also have "2 * (k div 2) + 1 = k" using True by simp
      finally show ?thesis .
    next
      case False
      have e: "XPf i k = (XPf (Suc i) (k div 2) :: 'a poly)" using False by (subst XPf_unfold) simp
      have "degree (XPf i k :: 'a poly) \<le> 2 ^ Suc i * (k div 2)" unfolding e by (rule b)
      also have "2 ^ Suc i * (k div 2) = 2 ^ i * (2 * (k div 2))" by (simp add: algebra_simps)
      also have "2 * (k div 2) = k" using False by simp
      finally show ?thesis .
    qed
  qed
qed

lemma degree_XP: "degree (XP k :: 'a :: char2 poly) \<le> k"
  using degree_XPf[of 0 k] by (simp add: XP_def)

subsection \<open>One layer and the radix recombination\<close>

definition mulBlock :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: comm_ring_1 poly \<Rightarrow> 'a poly" where
  "mulBlock L T B = poly_shift L B * (monom 1 L + monom 1 T) + poly_cutoff L B"

lemma mulBlock_split:
  assumes "bnd L r" "bnd L q"
  shows "mulBlock L T (r + q * monom 1 L) = q * (monom 1 L + monom 1 T) + r"
proof -
  have s: "poly_shift L (r + q * monom 1 L) = q"
    using assms(1) by (intro poly_eqI) (simp add: coeff_poly_shift coeff_mult_monom bnd_def)
  have c: "poly_cutoff L (r + q * monom 1 L) = r"
    using assms(1) by (intro poly_eqI) (auto simp: coeff_poly_cutoff coeff_mult_monom bnd_def)
  show ?thesis by (simp add: mulBlock_def s c)
qed

fun irad :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a :: comm_ring_1 poly \<Rightarrow> 'a poly" where
  "irad M u 0 f = f"
| "irad M u (Suc t) f = mulBlock (u * 2 ^ M * 2 ^ t) (u * 2 ^ t) (bmap 2 (u * 2 ^ M * 2 ^ t) (irad M u t) f)"

definition sig :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: char2 poly" where
  "sig M u = pcompose (sp M) (monom 1 u)"

lemma degree_sig: "degree (sig M u :: 'a :: char2 poly) \<le> u * 2 ^ M"
proof -
  have "degree (sp M :: 'a poly) * degree (monom 1 u :: 'a poly) \<le> 2 ^ M * u"
    by (rule mult_le_mono[OF degree_sp degree_monom_le])
  then show ?thesis
    using le_trans[OF degree_pcompose_le[of "sp M :: 'a poly" "monom 1 u"]] by (simp add: sig_def mult.commute)
qed

lemma pcompose_power_left: "pcompose (p ^ n) q = (pcompose p q :: 'a :: comm_ring_1 poly) ^ n"
  by (induction n) (simp_all add: pcompose_mult)

lemma sig_pow:
  "sig (2 ^ j) u ^ (2 ^ t) = (monom 1 (u * 2 ^ 2 ^ j * 2 ^ t) + monom 1 (u * 2 ^ t) :: 'a :: char2 poly)"
proof -
  have "sig (2 ^ j) u ^ (2 ^ t) = pcompose (sp (2 ^ j) ^ (2 ^ t)) (monom 1 u :: 'a poly)"
    by (simp add: sig_def pcompose_power_left)
  also have "\<dots> = pcompose (monom 1 (2 ^ (2 ^ j + t)) + monom 1 (2 ^ t)) (monom 1 u :: 'a poly)"
    by (simp only: sp_two_term_pow)
  also have "\<dots> = monom 1 (u * 2 ^ 2 ^ j * 2 ^ t) + monom 1 (u * 2 ^ t)"
    by (simp add: pcompose_add pcompose_monom1 monom_pow power_add ac_simps)
  finally show ?thesis .
qed

lemma bnd_packed:
  fixes G :: "nat \<Rightarrow> 'a :: comm_ring_1 poly"
  assumes "\<And>c. c < n \<Longrightarrow> bnd W (G c)"
  shows "bnd (W * n) (\<Sum>c<n. G c * monom 1 (W * c))"
proof (rule bnd_sum)
  fix c assume "c \<in> {..<n}"
  then have "W + W * c \<le> W * n" by (metis lessThan_iff mult_Suc_right mult_le_mono2 Suc_leI)
  then show "bnd (W * n) (G c * monom 1 (W * c))" using assms \<open>c \<in> {..<n}\<close> by (intro bnd_mult_monom) auto
qed

lemma bnd_sig_sum:
  fixes G :: "nat \<Rightarrow> 'a :: char2 poly"
  assumes "\<And>c. c < n \<Longrightarrow> bnd (u * 2 ^ M) (G c)"
  shows "bnd (u * 2 ^ M * n) (\<Sum>c<n. G c * sig M u ^ c)"
proof (rule bnd_sum)
  fix c assume c: "c \<in> {..<n}"
  have "degree (sig M u ^ c :: 'a poly) \<le> u * 2 ^ M * c"
    by (rule order_trans[OF degree_power_le]) (simp add: mult_le_mono1 degree_sig)
  then have "bnd (u * 2 ^ M * c + 1) (sig M u ^ c :: 'a poly)"
    by (intro bnd_degree) simp
  moreover have "u * 2 ^ M + (u * 2 ^ M * c + 1) \<le> u * 2 ^ M * n + 1"
  proof -
    have "Suc c \<le> n" using c by simp
    then have "Suc c * (u * 2 ^ M) \<le> n * (u * 2 ^ M)" by (rule mult_le_mono1)
    then show ?thesis by (simp add: algebra_simps)
  qed
  ultimately show "bnd (u * 2 ^ M * n) (G c * sig M u ^ c)"
    using assms c by (intro bnd_mult) auto
qed

theorem irad_spec:
  fixes G :: "nat \<Rightarrow> 'a :: char2 poly"
  assumes "\<And>c. c < 2 ^ t \<Longrightarrow> bnd (u * 2 ^ 2 ^ j) (G c)"
  shows "irad (2 ^ j) u t (\<Sum>c<2 ^ t. G c * monom 1 (u * 2 ^ 2 ^ j * c)) = (\<Sum>c<2 ^ t. G c * sig (2 ^ j) u ^ c)"
  using assms
proof (induction t arbitrary: G)
  case 0 then show ?case by simp
next
  case (Suc t)
  define W where "W = u * 2 ^ 2 ^ j"
  define B where "B = (\<lambda>i. \<Sum>c<2 ^ t. G (c + 2 ^ t * i) * monom 1 (W * c))"
  have bG: "bnd W (G (c + 2 ^ t * i))" if "i < 2" "c < 2 ^ t" for i c
  proof -
    have "i = 0 \<or> i = 1" using that(1) by auto
    then have "c + 2 ^ t * i < 2 ^ Suc t" using that(2) by auto
    then show ?thesis using Suc.prems by (simp add: W_def)
  qed
  have bB: "bnd (W * 2 ^ t) (B i)" if "i < 2" for i
    unfolding B_def by (rule bnd_packed) (rule bG[OF that])
  have split: "(\<Sum>c<2 ^ Suc t. G c * monom 1 (W * c)) = (\<Sum>i<2. B i * monom 1 (W * 2 ^ t * i))"
  proof -
    have "(\<Sum>c<2 ^ Suc t. G c * monom 1 (W * c)) = (\<Sum>i<2. \<Sum>c<2 ^ t. G (c + 2 ^ t * i) * monom 1 (W * (c + 2 ^ t * i)))"
      using sum_lt_mult[of "\<lambda>c. G c * monom 1 (W * c)" "2 ^ t" 2] by (simp add: mult.commute)
    also have "\<dots> = (\<Sum>i<2. B i * monom 1 (W * 2 ^ t * i))"
      unfolding B_def sum_distrib_right
    proof (intro sum.cong refl)
      fix i c
      show "G (c + 2 ^ t * i) * monom 1 (W * (c + 2 ^ t * i)) = G (c + 2 ^ t * i) * monom 1 (W * c) * monom 1 (W * 2 ^ t * i)"
        by (simp add: mult_monom distrib_left mult.assoc)
    qed
    finally show ?thesis .
  qed
  have ih: "irad (2 ^ j) u t (B i) = (\<Sum>c<2 ^ t. G (c + 2 ^ t * i) * sig (2 ^ j) u ^ c)" if "i < 2" for i
    unfolding B_def W_def by (rule Suc.IH) (use bG[OF that] in \<open>simp add: W_def\<close>)
  define P where "P = (\<lambda>i. \<Sum>c<2 ^ t. G (c + 2 ^ t * i) * sig (2 ^ j) u ^ c)"
  have bP: "bnd (W * 2 ^ t) (P i)" if "i < 2" for i
    unfolding P_def W_def by (rule bnd_sig_sum) (use bG[OF that] in \<open>simp add: W_def\<close>)
  have "bmap 2 (W * 2 ^ t) (irad (2 ^ j) u t) (\<Sum>c<2 ^ Suc t. G c * monom 1 (W * c))
      = (\<Sum>i<2. P i * monom 1 (W * 2 ^ t * i))"
    by (simp only: split bmap_packed[OF bB]) (simp add: ih P_def)
  also have "\<dots> = P 0 + P 1 * monom 1 (W * 2 ^ t)" by (simp add: numeral_2_eq_2)
  finally have bm: "bmap 2 (W * 2 ^ t) (irad (2 ^ j) u t) (\<Sum>c<2 ^ Suc t. G c * monom 1 (W * c))
      = P 0 + P 1 * monom 1 (W * 2 ^ t)" .
  have "irad (2 ^ j) u (Suc t) (\<Sum>c<2 ^ Suc t. G c * monom 1 (W * c))
      = P 1 * (monom 1 (W * 2 ^ t) + monom 1 (u * 2 ^ t)) + P 0"
  proof -
    have r: "irad (2 ^ j) u (Suc t) f = mulBlock (W * 2 ^ t) (u * 2 ^ t) (bmap 2 (W * 2 ^ t) (irad (2 ^ j) u t) f)"
      for f :: "'a poly" by (simp only: irad.simps W_def)
    have "irad (2 ^ j) u (Suc t) (\<Sum>c<2 ^ Suc t. G c * monom 1 (W * c))
        = mulBlock (W * 2 ^ t) (u * 2 ^ t) (P 0 + P 1 * monom 1 (W * 2 ^ t))" by (simp only: r bm)
    also have "\<dots> = P 1 * (monom 1 (W * 2 ^ t) + monom 1 (u * 2 ^ t)) + P 0"
      by (rule mulBlock_split) (simp_all add: bP)
    finally show ?thesis .
  qed
  also have "\<dots> = P 1 * sig (2 ^ j) u ^ (2 ^ t) + P 0" by (simp add: sig_pow W_def)
  also have "\<dots> = (\<Sum>c<2 ^ Suc t. G c * sig (2 ^ j) u ^ c)"
  proof -
    have "(\<Sum>c<2 ^ Suc t. G c * sig (2 ^ j) u ^ c) = (\<Sum>i<2. \<Sum>c<2 ^ t. G (c + 2 ^ t * i) * sig (2 ^ j) u ^ (c + 2 ^ t * i))"
      using sum_lt_mult[of "\<lambda>c. G c * sig (2 ^ j) u ^ c" "2 ^ t" 2] by (simp add: mult.commute)
    also have "\<dots> = P 0 + P 1 * sig (2 ^ j) u ^ (2 ^ t)"
      by (simp add: P_def numeral_2_eq_2 sum_distrib_left sum_distrib_right power_add algebra_simps)
    finally show ?thesis by (simp add: add.commute)
  qed
  finally show ?case by (simp add: W_def)
qed

end
