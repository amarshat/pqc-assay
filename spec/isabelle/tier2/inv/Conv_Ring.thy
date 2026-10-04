(* v4 O8, ring side: the convolution theorem as an integer congruence at q = 8380417.

   Negacyclic_Conv proves negconv_via_NNTT inside the locale, over 'a mod_ring lists. The C-side
   bridges (Signed_Bridge, Inv_Signed_Bridge, Pointwise_Bridge) speak integers mod 8380417 with the
   inverse exponent kept in Z/512 by zpw. This theory instantiates the locale at the ML-DSA model
   (mldsa_model) and pushes the result through of_int, so the conclusion mentions no locale
   constant and no mod_ring: it can be consumed by a theory that also imports the Cryptol model.

   The exponent 1753^(nat ((-(2t+1)k) mod 512)) is zpw (-(2t+1)k) unfolded; it is written out here
   so this theory does not depend on Inv_Mont_Bridge. *)
theory Conv_Ring
  imports Mldsa_Instance Negacyclic_Poly
begin

text \<open>Negacyclic convolution on integer coefficient functions, the same shape as the locale's
\<open>negconv\<close> at \<open>n = 256\<close>.\<close>

definition negconv_int :: "(nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> nat \<Rightarrow> int" where
  "negconv_int f g k =
     (\<Sum>i<256. if i \<le> k then f i * g (k - i) else - (f i * g (k + 256 - i)))"

context negacyclic_butterfly
begin

text \<open>The inverse transform written out at one index: the AFP \<open>intt\<close> sum, untwisted.\<close>

lemma INNTT_nth:
  assumes kk: "kk < n"
  shows "INNTT ys ! kk = (\<Sum>t<n. ys ! t * ((\<psi>*\<mu>)^kk * \<mu>^(kk*t)))"
proof -
  have "INNTT ys ! kk = (\<psi>*\<mu>)^kk * (INTT ys ! kk)"
    using kk by (simp add: INNTT_def)
  also have "INTT ys ! kk = (\<Sum>t<n. ys ! t * \<mu>^(kk*t))"
    using kk by (simp add: INTT_def intt_def atLeast0LessThan)
  finally show ?thesis
    by (simp add: sum_distrib_left mult.commute mult.left_commute)
qed

text \<open>\<open>negconv_via_NNTT\<close> read at index \<open>kk\<close>.\<close>

lemma conv_sum:
  assumes kk: "kk < n"
  shows "(\<Sum>t<n. nntt xs t * nntt ys t * ((\<psi>*\<mu>)^kk * \<mu>^(kk*t)))
           = of_int_mod_ring (int n) * negconv xs ys ! kk"
proof -
  have "INNTT (pointwise (NNTT xs) (NNTT ys)) ! kk
          = map (\<lambda>c. of_int_mod_ring (int n) * c) (negconv xs ys) ! kk"
    by (simp only: negconv_via_NNTT)
  also have "\<dots> = of_int_mod_ring (int n) * negconv xs ys ! kk"
    using kk by simp
  finally have e: "INNTT (pointwise (NNTT xs) (NNTT ys)) ! kk
                     = of_int_mod_ring (int n) * negconv xs ys ! kk" .
  have "INNTT (pointwise (NNTT xs) (NNTT ys)) ! kk
          = (\<Sum>t<n. pointwise (NNTT xs) (NNTT ys) ! t * ((\<psi>*\<mu>)^kk * \<mu>^(kk*t)))"
    by (rule INNTT_nth[OF kk])
  also have "\<dots> = (\<Sum>t<n. nntt xs t * nntt ys t * ((\<psi>*\<mu>)^kk * \<mu>^(kk*t)))"
    by (rule sum.cong) (simp_all add: pointwise_def NNTT_def)
  finally show ?thesis using e by simp
qed

end

subsection \<open>Pushing the instance through \<open>of_int\<close>\<close>

lemma ps_of_int: "ps = of_int 1753"
  by (simp add: ps_def of_int_of_int_mod_ring)

lemma ps_512: "ps ^ 512 = 1"
proof -
  have "ps ^ 512 = ps ^ (2 * 256)" by simp
  also have "\<dots> = (ps * ps) ^ 256" by (simp only: power_mult power2_eq_square)
  also have "\<dots> = 1" by (simp add: ps_sq w_256)
  finally show ?thesis .
qed

lemma ps_pow_mod: "ps ^ a = ps ^ (a mod 512)"
proof -
  have "ps ^ a = ps ^ (512 * (a div 512) + a mod 512)" by simp
  also have "\<dots> = (ps ^ 512) ^ (a div 512) * ps ^ (a mod 512)"
    by (simp only: power_add power_mult)
  finally show ?thesis by (simp add: ps_512)
qed

lemma mu_ps: "mu = ps ^ 510"
proof -
  have "mu = mu * ps ^ 512" by (simp add: ps_512)
  also have "\<dots> = (mu * (ps * ps)) * ps ^ 510"
    by (simp add: power_add[symmetric] mult.assoc power2_eq_square[symmetric])
  also have "\<dots> = ps ^ 510" by (simp add: ps_sq mu_w)
  finally show ?thesis .
qed

text \<open>The inverse twiddle \<open>(\<psi>\<mu>)^k \<mu>^(kt) = \<psi>^(-(2t+1)k)\<close>, with the exponent kept in \<open>Z/512\<close>.\<close>

lemma inv_twiddle:
  "(ps * mu) ^ k * mu ^ (k * t) = of_int (1753 ^ nat ((- (2 * int t + 1) * int k) mod 512))"
proof -
  have p511: "ps * ps ^ 510 = ps ^ 511" using power_add[of ps 1 510] by simp
  have "(ps * mu) ^ k * mu ^ (k * t) = (ps ^ 511) ^ k * (ps ^ 510) ^ (k * t)"
    by (simp only: mu_ps p511)
  also have "\<dots> = ps ^ (511 * k + 510 * (k * t))"
    by (simp only: power_add power_mult)
  also have "\<dots> = ps ^ ((511 * k + 510 * (k * t)) mod 512)" by (rule ps_pow_mod)
  also have "(511 * k + 510 * (k * t)) mod 512 = nat ((- (2 * int t + 1) * int k) mod 512)"
  proof -
    have i: "int (511 * k + 510 * (k * t))
               = (- (2 * int t + 1) * int k) + 512 * (int k + int k * int t)"
      by (simp add: algebra_simps)
    have "int ((511 * k + 510 * (k * t)) mod 512) = int (511 * k + 510 * (k * t)) mod 512"
      by (simp only: of_nat_mod) simp
    also have "\<dots> = (- (2 * int t + 1) * int k) mod 512"
      by (simp only: i mod_mult_self2)
    finally show ?thesis by simp
  qed
  finally show ?thesis by (simp add: ps_of_int)
qed

lemma omr_eq_mod:
  assumes "(of_int a :: fin8380417 mod_ring) = of_int b"
  shows "a mod 8380417 = b mod 8380417"
  using arg_cong[OF assms, of to_int_mod_ring] by (simp add: of_int_of_int_mod_ring to_int_omr)

theorem conv_int:
  fixes f g :: "nat \<Rightarrow> int"
  assumes k: "k < 256"
  shows "(\<Sum>t<256. (\<Sum>j<256. f j * 1753 ^ ((2 * t + 1) * j))
                  * (\<Sum>j<256. g j * 1753 ^ ((2 * t + 1) * j))
                  * 1753 ^ nat ((- (2 * int t + 1) * int k) mod 512)) mod 8380417
       = (256 * negconv_int f g k) mod 8380417"
proof -
  interpret M: negacyclic_butterfly 8380417 256 32736 w mu ps 8 by (rule mldsa_model)
  define F :: "fin8380417 mod_ring list" where "F = map (\<lambda>j. of_int (f j)) [0..<256]"
  define G :: "fin8380417 mod_ring list" where "G = map (\<lambda>j. of_int (g j)) [0..<256]"
  have fwd: "M.nntt (map (\<lambda>j. of_int (h j)) [0..<256]) t
               = (of_int (\<Sum>j<256. h j * 1753 ^ ((2 * t + 1) * j)) :: fin8380417 mod_ring)"
    for h :: "nat \<Rightarrow> int" and t
    unfolding M.nntt_def atLeast0LessThan
    by (simp add: ps_of_int)
  have nc: "M.negconv F G ! k = (of_int (negconv_int f g k) :: fin8380417 mod_ring)"
    unfolding negconv_int_def F_def G_def using k
    by (auto simp: M.negconv_nth intro!: sum.cong)
  have "(\<Sum>t<256. M.nntt F t * M.nntt G t * ((ps * mu) ^ k * mu ^ (k * t)))
          = of_int_mod_ring (int 256) * M.negconv F G ! k"
    using M.conv_sum[of k F G] k by simp
  hence "(of_int (\<Sum>t<256. (\<Sum>j<256. f j * 1753 ^ ((2 * t + 1) * j))
                  * (\<Sum>j<256. g j * 1753 ^ ((2 * t + 1) * j))
                  * 1753 ^ nat ((- (2 * int t + 1) * int k) mod 512)) :: fin8380417 mod_ring)
        = of_int (256 * negconv_int f g k)"
    unfolding F_def G_def fwd inv_twiddle
    by (simp add: nc[unfolded F_def G_def] of_int_of_int_mod_ring[symmetric])
  thus ?thesis by (rule omr_eq_mod)
qed


text \<open>The ring reading. Any integer coefficient function that agrees with \<open>negconv_int f g\<close> mod q
on \<open>[0,256)\<close> is, as a polynomial over \<open>Z_q\<close>, the product of \<open>f\<close> and \<open>g\<close> reduced mod
\<open>X^256 + 1\<close>. This is \<open>negconv_is_mult\<close> at \<open>mldsa_model\<close>, pushed through \<open>of_int\<close>.\<close>

theorem negconv_int_ring:
  fixes f g h :: "nat \<Rightarrow> int"
  assumes agree: "\<And>k. k < 256 \<Longrightarrow> h k mod 8380417 = negconv_int f g k mod 8380417"
  shows "Poly (map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256])
       = (Poly (map (\<lambda>j. of_int (f j)) [0..<256]) * Poly (map (\<lambda>j. of_int (g j)) [0..<256]))
           mod (monom 1 256 + 1)"
proof -
  interpret M: negacyclic_butterfly 8380417 256 32736 w mu ps 8 by (rule mldsa_model)
  define F :: "fin8380417 mod_ring list" where "F = map (\<lambda>j. of_int (f j)) [0..<256]"
  define G :: "fin8380417 mod_ring list" where "G = map (\<lambda>j. of_int (g j)) [0..<256]"
  have nc: "M.negconv F G ! k = (of_int (negconv_int f g k) :: fin8380417 mod_ring)"
    if k: "k < 256" for k
    using k by (auto simp: M.negconv_nth negconv_int_def F_def G_def intro!: sum.cong)
  have hk: "(of_int (h k) :: fin8380417 mod_ring) = of_int (negconv_int f g k)"
    if k: "k < 256" for k
  proof -
    have "(of_int (h k) :: fin8380417 mod_ring) = of_int_mod_ring (h k mod Q)"
      by (simp add: of_int_of_int_mod_ring omr_modQ[symmetric])
    also have "\<dots> = of_int_mod_ring (negconv_int f g k mod Q)" using agree[OF k] by simp
    also have "\<dots> = of_int (negconv_int f g k)"
      by (simp add: of_int_of_int_mod_ring omr_modQ[symmetric])
    finally show ?thesis .
  qed
  have eq: "map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256] = M.negconv F G"
    by (rule nth_equalityI) (simp_all add: hk nc del: M.negconv_nth)
  show ?thesis
    unfolding eq F_def[symmetric] G_def[symmetric]
    by (rule M.negconv_is_mult) (simp_all add: F_def G_def)
qed


text \<open>Every NTT-domain vector is the transform of some integer polynomial (the transform is onto mod
q). This is what lets a statement about an operand sampled directly in NTT form, like ML-DSA's
\<open>A_hat\<close>, be read as a statement about polynomials. Witness: \<open>INNTT\<close> of the vector scaled by
\<open>256^-1 = 8347681\<close>, then \<open>NNTT_INNTT\<close>.\<close>

theorem ntt_int_surj:
  fixes x :: "nat \<Rightarrow> int"
  shows "\<exists>f :: nat \<Rightarrow> int. \<forall>t<256.
           (\<Sum>j<256. f j * 1753 ^ ((2 * t + 1) * j)) mod 8380417 = x t mod 8380417"
proof -
  interpret M: negacyclic_butterfly 8380417 256 32736 w mu ps 8 by (rule mldsa_model)
  define ys :: "fin8380417 mod_ring list" where "ys = map (\<lambda>t. of_int (8347681 * x t)) [0..<256]"
  define fl where "fl = M.INNTT ys"
  define f where "f j = to_int_mod_ring (fl ! j)" for j
  have nn: "M.NNTT fl = map (\<lambda>c. of_int_mod_ring (int 256) * c) ys"
    unfolding fl_def by (rule M.NNTT_INNTT) (simp add: ys_def)
  have e: "(of_int (to_int_mod_ring c) :: fin8380417 mod_ring) = c" for c
    by (simp add: of_int_of_int_mod_ring)
  have inv: "(of_int (2137006336 * a) :: fin8380417 mod_ring) = of_int a" for a :: int
  proof -
    have "(2137006336 * a) mod Q = (a + Q * (255 * a)) mod Q" by (simp add: algebra_simps)
    also have "\<dots> = a mod Q" by (rule mod_mult_self2)
    finally show ?thesis by (simp add: of_int_of_int_mod_ring omr_modQ[of "2137006336 * a"] omr_modQ[of a])
  qed
  have "(of_int (\<Sum>j<256. f j * 1753 ^ ((2 * t + 1) * j)) :: fin8380417 mod_ring) = of_int (x t)"
    if t: "t < 256" for t
  proof -
    have "(of_int (\<Sum>j<256. f j * 1753 ^ ((2 * t + 1) * j)) :: fin8380417 mod_ring)
            = (\<Sum>j<256. fl ! j * ps ^ ((2 * t + 1) * j))"
      by (simp add: f_def ps_of_int e)
    also have "\<dots> = M.nntt fl t" by (simp add: M.nntt_def atLeast0LessThan)
    also have "\<dots> = M.NNTT fl ! t" using t by (simp add: M.NNTT_def)
    also have "\<dots> = of_int_mod_ring (int 256) * of_int (8347681 * x t)" using t by (simp add: nn ys_def)
    also have "\<dots> = of_int (2137006336 * x t)" by (simp add: of_int_of_int_mod_ring[symmetric])
    also have "\<dots> = of_int (x t)" by (rule inv)
    finally show ?thesis .
  qed
  thus ?thesis by (intro exI[of _ f] allI impI omr_eq_mod) blast
qed

text \<open>The sum form of the ring reading, for a matrix row: an integer coefficient function that agrees
with \<open>\<Sum>i<L. negconv_int (f i) (g i)\<close> mod q is \<open>\<Sum>i<L. f_i * g_i\<close> reduced mod \<open>X^256 + 1\<close>.\<close>

theorem negconv_sum_ring:
  fixes f g :: "nat \<Rightarrow> nat \<Rightarrow> int" and h :: "nat \<Rightarrow> int"
  assumes agree: "\<And>k. k < 256 \<Longrightarrow> h k mod 8380417 = (\<Sum>i<L. negconv_int (f i) (g i) k) mod 8380417"
  shows "Poly (map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256])
       = (\<Sum>i<L. Poly (map (\<lambda>j. of_int (f i j)) [0..<256]) * Poly (map (\<lambda>j. of_int (g i j)) [0..<256]))
           mod (monom 1 256 + 1)"
proof -
  interpret M: negacyclic_butterfly 8380417 256 32736 w mu ps 8 by (rule mldsa_model)
  define F where "F i = (map (\<lambda>j. of_int (f i j)) [0..<256] :: fin8380417 mod_ring list)" for i
  define G where "G i = (map (\<lambda>j. of_int (g i j)) [0..<256] :: fin8380417 mod_ring list)" for i
  let ?D = "monom 1 256 + 1 :: fin8380417 mod_ring poly"
  have nc: "M.negconv (F i) (G i) ! k = (of_int (negconv_int (f i) (g i) k) :: fin8380417 mod_ring)"
    if k: "k < 256" for i k
    using k by (auto simp: M.negconv_nth negconv_int_def F_def G_def intro!: sum.cong)
  have hk: "(of_int (h k) :: fin8380417 mod_ring) = (\<Sum>i<L. M.negconv (F i) (G i) ! k)"
    if k: "k < 256" for k
  proof -
    have "(of_int (h k) :: fin8380417 mod_ring) = of_int_mod_ring (h k mod Q)"
      by (simp add: of_int_of_int_mod_ring omr_modQ[symmetric])
    also have "\<dots> = of_int_mod_ring ((\<Sum>i<L. negconv_int (f i) (g i) k) mod Q)" using agree[OF k] by simp
    also have "\<dots> = of_int (\<Sum>i<L. negconv_int (f i) (g i) k)"
      by (simp add: of_int_of_int_mod_ring omr_modQ[symmetric])
    also have "\<dots> = (\<Sum>i<L. M.negconv (F i) (G i) ! k)" by (simp add: nc[OF k])
    finally show ?thesis .
  qed
  have lhs: "Poly (map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256])
               = (\<Sum>i<L. Poly (M.negconv (F i) (G i)))"
  proof -
    have "Poly (map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256])
            = (\<Sum>k<256. monom (of_int (h k)) k)"
      by (subst M.Poly_as_sum) simp_all
    also have "\<dots> = (\<Sum>k<256. \<Sum>i<L. monom (M.negconv (F i) (G i) ! k) k)"
      by (rule sum.cong[OF refl]) (simp add: hk monom_sum)
    also have "\<dots> = (\<Sum>i<L. \<Sum>k<256. monom (M.negconv (F i) (G i) ! k) k)" by (rule sum.swap)
    also have "\<dots> = (\<Sum>i<L. Poly (M.negconv (F i) (G i)))"
      by (rule sum.cong[OF refl]) (subst M.Poly_as_sum, simp_all)
    finally show ?thesis .
  qed
  have each: "Poly (M.negconv (F i) (G i)) = (Poly (F i) * Poly (G i)) mod ?D" for i
    by (rule M.negconv_is_mult) (simp_all add: F_def G_def)
  have dlt: "degree (Poly (map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256])) < degree ?D"
    using M.degree_Poly_lt[of "map (\<lambda>k. of_int (h k)) [0..<256]"] M.degree_Dn by simp
  have "(\<Sum>i<L. Poly (F i) * Poly (G i)) mod ?D = (\<Sum>i<L. (Poly (F i) * Poly (G i)) mod ?D) mod ?D"
    by (rule mod_sum_eq[symmetric])
  also have "\<dots> = Poly (map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256]) mod ?D"
    by (simp add: lhs each)
  also have "\<dots> = Poly (map (\<lambda>k. of_int (h k) :: fin8380417 mod_ring) [0..<256])"
    by (rule mod_poly_less[OF dlt])
  finally show ?thesis by (simp add: F_def G_def)
qed

end
