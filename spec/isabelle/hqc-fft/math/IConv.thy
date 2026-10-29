theory IConv
  imports BC
begin

text \<open>A conversion schedule. \<open>Lf k\<close> (\<open>k \<le> 1\<close>) is the identity on \<open>2\<^sup>k\<close> digits. \<open>Nd j hi lo\<close>
  with \<open>M = 2\<^sup>j\<close> converts \<open>2\<^sup>M\<^sup>+\<^sup>K\<close> digits (\<open>K = sz hi\<close>): each block of \<open>2\<^sup>M\<close> digits by
  \<open>lo\<close>, the \<open>2\<^sup>K\<close> blocks as digits of width \<open>u 2\<^sup>M\<close> by \<open>hi\<close>, then \<open>irad\<close>. The theorem
  \<open>iconv_spec\<close>: for every well-formed schedule, digits \<open>D\<^sub>d\<close> (each of width \<open>u\<close>) at positions
  \<open>u d\<close> become \<open>\<Sum> D\<^sub>d \<cdot> (X\<^sub>d \<circ> x\<^sup>u)\<close>. At \<open>u = 1\<close> with constant digits this says the
  output is \<open>\<Sum> c\<^sub>d X\<^sub>d\<close>: the input was the novel-basis coordinate vector of the output.\<close>

datatype sch = Lf nat | Nd nat sch sch

fun sz :: "sch \<Rightarrow> nat" where
  "sz (Lf k) = k"
| "sz (Nd j hi lo) = 2 ^ j + sz hi"

fun wf :: "sch \<Rightarrow> bool" where
  "wf (Lf k) \<longleftrightarrow> k \<le> 1"
| "wf (Nd j hi lo) \<longleftrightarrow> sz lo = 2 ^ j \<and> wf hi \<and> wf lo"

fun iconv :: "sch \<Rightarrow> nat \<Rightarrow> 'a :: char2 poly \<Rightarrow> 'a poly" where
  "iconv (Lf k) u f = f"
| "iconv (Nd j hi lo) u f =
     irad (2 ^ j) u (sz hi) (iconv hi (u * 2 ^ 2 ^ j) (bmap (2 ^ sz hi) (u * 2 ^ 2 ^ j) (iconv lo u) f))"

lemma XP_0 [simp]: "XP 0 = 1"
  by (simp add: XP_def)

lemma XP_1 [simp]: "XP (Suc 0) = ([:0, 1:] :: 'a :: char2 poly)"
  by (simp add: XP_def XPf_unfold[of 0 "Suc 0"])

lemma degree_pcompose_monom: "degree (pcompose p (monom 1 u) :: 'a :: comm_ring_1 poly) \<le> degree p * u"
  using degree_pcompose_le[of p "monom 1 u"] degree_monom_le[of "1 :: 'a" u]
  by (meson le_trans mult_le_mono2)

lemma bnd_term:
  fixes D :: "'a :: char2 poly"
  assumes "bnd u D" "a < N"
  shows "bnd (u * N) (D * pcompose (XP a) (monom 1 u))"
proof -
  have "degree (pcompose (XP a) (monom 1 u) :: 'a poly) \<le> a * u"
    using degree_pcompose_monom[of "XP a" u] degree_XP[of a] by (meson le_trans mult_le_mono1)
  then have "bnd (a * u + 1) (pcompose (XP a) (monom 1 u) :: 'a poly)" by (intro bnd_degree) simp
  moreover have "u + (a * u + 1) \<le> u * N + 1"
  proof -
    have "Suc a * u \<le> N * u" using assms(2) by (intro mult_le_mono1) simp
    then show ?thesis by (simp add: algebra_simps)
  qed
  ultimately show ?thesis using assms(1) by (intro bnd_mult) auto
qed

theorem iconv_spec:
  fixes D :: "nat \<Rightarrow> 'a :: char2 poly"
  assumes "wf s" "\<And>d. d < 2 ^ sz s \<Longrightarrow> bnd u (D d)"
  shows "iconv s u (\<Sum>d<2 ^ sz s. D d * monom 1 (u * d)) = (\<Sum>d<2 ^ sz s. D d * pcompose (XP d) (monom 1 u))"
  using assms
proof (induction s arbitrary: u D)
  case (Lf k)
  then have "k = 0 \<or> k = 1" by auto
  then show ?case by (auto simp: numeral_2_eq_2 pcompose_pCons)
next
  case (Nd j hi lo)
  define M where "M = (2 :: nat) ^ j"
  define K where "K = sz hi"
  define W where "W = u * 2 ^ M"
  have szlo: "sz lo = M" and wfhi: "wf hi" and wflo: "wf lo" using Nd.prems(1) by (simp_all add: M_def)
  have szs: "sz (Nd j hi lo) = M + K" by (simp add: M_def K_def)
  have Dd: "bnd u (D d)" if "d < 2 ^ M * 2 ^ K" for d
    using Nd.prems(2) that by (simp add: szs power_add M_def K_def)
  have Dab: "bnd u (D (a + 2 ^ M * b))" if "a < 2 ^ M" "b < 2 ^ K" for a b
  proof -
    have "a + 2 ^ M * b < 2 ^ M * Suc b" using that(1) by simp
    also have "2 ^ M * Suc b \<le> 2 ^ M * 2 ^ K" using that(2) by (intro mult_le_mono2) simp
    finally show ?thesis by (rule Dd)
  qed
  define Bl where "Bl = (\<lambda>b. \<Sum>a<2 ^ M. D (a + 2 ^ M * b) * monom 1 (u * a))"
  define E where "E = (\<lambda>b. \<Sum>a<2 ^ M. D (a + 2 ^ M * b) * pcompose (XP a) (monom 1 u))"
  have bBl: "bnd W (Bl b)" if "b < 2 ^ K" for b
    unfolding Bl_def W_def by (rule bnd_packed) (simp add: Dab that)
  have bE: "bnd W (E b)" if "b < 2 ^ K" for b
    unfolding E_def W_def by (rule bnd_sum) (simp add: bnd_term Dab that)
  have in_split: "(\<Sum>d<2 ^ sz (Nd j hi lo). D d * monom 1 (u * d)) = (\<Sum>b<2 ^ K. Bl b * monom 1 (W * b))"
  proof -
    have "(\<Sum>d<2 ^ sz (Nd j hi lo). D d * monom 1 (u * d)) = (\<Sum>b<2 ^ K. \<Sum>a<2 ^ M. D (a + 2 ^ M * b) * monom 1 (u * (a + 2 ^ M * b)))"
      by (simp only: szs power_add sum_lt_mult)
    also have "\<dots> = (\<Sum>b<2 ^ K. Bl b * monom 1 (W * b))"
      unfolding Bl_def sum_distrib_right
    proof (intro sum.cong refl)
      fix b a :: nat
      show "D (a + 2 ^ M * b) * monom 1 (u * (a + 2 ^ M * b)) = D (a + 2 ^ M * b) * monom 1 (u * a) * monom 1 (W * b)"
        by (simp add: W_def mult_monom distrib_left mult.assoc)
    qed
    finally show ?thesis .
  qed
  have step_lo: "bmap (2 ^ K) W (iconv lo u) (\<Sum>b<2 ^ K. Bl b * monom 1 (W * b)) = (\<Sum>b<2 ^ K. E b * monom 1 (W * b))"
  proof -
    have "bmap (2 ^ K) W (iconv lo u) (\<Sum>b<2 ^ K. Bl b * monom 1 (W * b)) = (\<Sum>b<2 ^ K. iconv lo u (Bl b) * monom 1 (W * b))"
      by (rule bmap_packed) (rule bBl)
    also have "\<dots> = (\<Sum>b<2 ^ K. E b * monom 1 (W * b))"
    proof (intro sum.cong refl)
      fix b :: nat assume "b \<in> {..<2 ^ K}"
      then have "b < 2 ^ K" by simp
      have "iconv lo u (\<Sum>a<2 ^ sz lo. D (a + 2 ^ M * b) * monom 1 (u * a))
          = (\<Sum>a<2 ^ sz lo. D (a + 2 ^ M * b) * pcompose (XP a) (monom 1 u))"
        by (rule Nd.IH(2)[OF wflo]) (simp add: szlo Dab \<open>b < 2 ^ K\<close>)
      then show "iconv lo u (Bl b) * monom 1 (W * b) = E b * monom 1 (W * b)"
        by (simp add: Bl_def E_def szlo)
    qed
    finally show ?thesis .
  qed
  have step_hi: "iconv hi W (\<Sum>b<2 ^ K. E b * monom 1 (W * b)) = (\<Sum>b<2 ^ K. E b * pcompose (XP b) (monom 1 W))"
    unfolding K_def by (rule Nd.IH(1)[OF wfhi]) (simp add: bE K_def)
  define G where "G = (\<lambda>c. \<Sum>b<2 ^ K. smult (coeff (XP b) c) (E b))"
  have degXP: "degree (XP b :: 'a poly) < 2 ^ K" if "b < 2 ^ K" for b
    by (rule le_less_trans[OF degree_XP that])
  have regroup: "(\<Sum>b<2 ^ K. E b * pcompose (XP b) q) = (\<Sum>c<2 ^ K. G c * q ^ c)" for q :: "'a poly"
  proof -
    have "(\<Sum>b<2 ^ K. E b * pcompose (XP b) q) = (\<Sum>b<2 ^ K. E b * (\<Sum>c<2 ^ K. smult (coeff (XP b) c) (q ^ c)))"
      by (intro sum.cong refl) (simp add: pcompose_expand[OF degXP])
    also have "\<dots> = (\<Sum>b<2 ^ K. \<Sum>c<2 ^ K. smult (coeff (XP b) c) (E b) * q ^ c)"
      by (simp only: sum_distrib_left mult_smult_right mult_smult_left)
    also have "\<dots> = (\<Sum>c<2 ^ K. \<Sum>b<2 ^ K. smult (coeff (XP b) c) (E b) * q ^ c)"
      by (rule sum.swap)
    also have "\<dots> = (\<Sum>c<2 ^ K. G c * q ^ c)"
      by (simp only: G_def sum_distrib_right)
    finally show ?thesis .
  qed
  have bG: "bnd W (G c)" for c
    unfolding G_def by (rule bnd_sum) (simp add: bnd_smult bE)
  have step_rad: "irad M u K (\<Sum>c<2 ^ K. G c * monom 1 (W * c)) = (\<Sum>c<2 ^ K. G c * sig M u ^ c)"
    unfolding M_def W_def by (rule irad_spec) (use bG in \<open>simp add: W_def M_def\<close>)
  have mono_pow: "monom 1 W ^ c = (monom 1 (W * c) :: 'a poly)" for c
    by (simp add: monom_pow)
  have "iconv (Nd j hi lo) u (\<Sum>d<2 ^ sz (Nd j hi lo). D d * monom 1 (u * d))
      = irad M u K (iconv hi W (bmap (2 ^ K) W (iconv lo u) (\<Sum>b<2 ^ K. Bl b * monom 1 (W * b))))"
    by (simp only: in_split iconv.simps) (simp add: M_def K_def W_def)
  also have "\<dots> = irad M u K (\<Sum>b<2 ^ K. E b * pcompose (XP b) (monom 1 W))"
    by (simp only: step_lo step_hi)
  also have "\<dots> = irad M u K (\<Sum>c<2 ^ K. G c * monom 1 (W * c))"
    by (simp only: regroup mono_pow)
  also have "\<dots> = (\<Sum>c<2 ^ K. G c * sig M u ^ c)" by (rule step_rad)
  also have "\<dots> = (\<Sum>b<2 ^ K. E b * pcompose (XP b) (sig M u))" by (simp only: regroup)
  also have "\<dots> = (\<Sum>b<2 ^ K. \<Sum>a<2 ^ M. D (a + 2 ^ M * b) * pcompose (XP (a + 2 ^ M * b)) (monom 1 u))"
  proof (intro sum.cong refl)
    fix b :: nat
    have "E b * pcompose (XP b) (sig M u) = (\<Sum>a<2 ^ M. D (a + 2 ^ M * b) * (pcompose (XP a) (monom 1 u) * pcompose (XP b) (sig M u)))"
      by (simp add: E_def sum_distrib_right mult.assoc)
    also have "\<dots> = (\<Sum>a<2 ^ M. D (a + 2 ^ M * b) * pcompose (XP (a + 2 ^ M * b)) (monom 1 u))"
    proof (intro sum.cong refl)
      fix a :: nat assume "a \<in> {..<2 ^ M}"
      then have "a < 2 ^ M" by simp
      have "pcompose (XP (a + 2 ^ M * b)) (monom 1 u) = pcompose (XP a * pcompose (XP b) (sp M)) (monom 1 u :: 'a poly)"
        by (simp only: XP_factor[OF \<open>a < 2 ^ M\<close>])
      also have "\<dots> = pcompose (XP a) (monom 1 u) * pcompose (XP b) (sig M u)"
        by (simp add: pcompose_mult sig_def pcompose_assoc)
      finally show "D (a + 2 ^ M * b) * (pcompose (XP a) (monom 1 u) * pcompose (XP b) (sig M u))
          = D (a + 2 ^ M * b) * pcompose (XP (a + 2 ^ M * b)) (monom 1 u)" by simp
    qed
    finally show "E b * pcompose (XP b) (sig M u) = (\<Sum>a<2 ^ M. D (a + 2 ^ M * b) * pcompose (XP (a + 2 ^ M * b)) (monom 1 u))" .
  qed
  also have "\<dots> = (\<Sum>d<2 ^ sz (Nd j hi lo). D d * pcompose (XP d) (monom 1 u))"
    by (simp only: szs power_add sum_lt_mult)
  finally show ?case .
qed

corollary iconv_novel:
  fixes c :: "nat \<Rightarrow> 'a :: char2"
  assumes "wf s"
  shows "iconv s 1 (\<Sum>d<2 ^ sz s. monom (c d) d) = (\<Sum>d<2 ^ sz s. smult (c d) (XP d))"
proof -
  have "iconv s 1 (\<Sum>d<2 ^ sz s. [:c d:] * monom 1 (1 * d)) = (\<Sum>d<2 ^ sz s. [:c d:] * pcompose (XP d) (monom 1 1))"
    by (rule iconv_spec[OF assms]) (simp add: bnd_def coeff_pCons split: nat.split)
  moreover have "monom 1 1 = ([:0, 1:] :: 'a poly)" by (simp add: monom_altdef)
  ultimately show ?thesis by (simp add: smult_monom)
qed

end
