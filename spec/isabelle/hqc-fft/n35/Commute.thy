theory Commute
  imports "HQC_FFT_Math.Flatten"
begin

text \<open>The hqc-5 conversion (the C's generic bc_1 path) runs the layers of a node's hi subtree
  before those of its lo subtree, the reverse of layers. The two orders agree: a layer whose L and
  T are multiples of W only adds whole W-blocks to whole W-blocks, so it commutes with any additive
  map applied to every W-block (swap_node).\<close>

definition additive :: "('a :: comm_ring_1 poly \<Rightarrow> 'a poly) \<Rightarrow> bool" where
  "additive h \<longleftrightarrow> (\<forall>x y. h (x + y) = h x + h y)"

lemma additive_zero: "additive h \<Longrightarrow> h 0 = 0"
proof -
  assume "additive h"
  then have "h 0 + h 0 = h 0 + 0" by (metis add.right_neutral additive_def)
  then show ?thesis by simp
qed

lemma blk_add: "blk W j (f + g) = blk W j f + blk W j (g :: 'a :: comm_ring_1 poly)"
  by (rule poly_eqI) (simp add: blk_def coeff_poly_cutoff coeff_poly_shift)

lemma blk_zero: "blk W j 0 = 0"
  by (simp add: blk_def)

lemma bmap_add: "additive h \<Longrightarrow> bmap n W h (f + g) = bmap n W h f + bmap n W h g"
  by (simp add: bmap_def blk_add additive_def sum.distrib distrib_right)

lemma bmap_zero: "additive h \<Longrightarrow> bmap n W h 0 = 0"
  by (simp add: bmap_def blk_zero additive_zero)

lemma bmap_sum: "additive h \<Longrightarrow> bmap n W h (\<Sum>i\<in>S. F i) = (\<Sum>i\<in>S. bmap n W h (F i))"
  by (induction S rule: infinite_finite_induct) (simp_all add: bmap_zero bmap_add)

lemma bmap_mono:
  assumes h: "additive h" and B: "bnd W B" and i: "i < n"
  shows "bmap n W h (B * monom 1 (W * i)) = h B * monom 1 (W * i)"
proof -
  define B' where "B' = (\<lambda>j. if j = i then B else 0)"
  have "(\<Sum>j<n. B' j * monom 1 (W * j)) = (\<Sum>j<n. if j = i then B * monom 1 (W * j) else 0)"
    by (intro sum.cong refl) (simp add: B'_def)
  then have "B * monom 1 (W * i) = (\<Sum>j<n. B' j * monom 1 (W * j))"
    using i by simp
  moreover have "bmap n W h (\<Sum>j<n. B' j * monom 1 (W * j)) = (\<Sum>j<n. h (B' j) * monom 1 (W * j))"
    by (rule bmap_packed) (use B in \<open>simp add: B'_def bnd_def\<close>)
  moreover have "(\<Sum>j<n. h (B' j) * monom 1 (W * j)) = (\<Sum>j<n. if j = i then h B * monom 1 (W * j) else 0)"
    by (intro sum.cong refl) (simp add: B'_def additive_zero[OF h])
  moreover have "(\<Sum>j<n. if j = i then h B * monom 1 (W * j) else 0) = h B * monom 1 (W * i)"
    using i by simp
  ultimately show ?thesis by simp
qed

lemma bmap_shift:
  assumes h: "additive h" and p: "bnd (m * W) p" and sm: "s + m \<le> n"
  shows "bmap n W h (p * monom 1 (W * s)) = bmap m W h p * monom 1 (W * s)"
proof -
  have pe: "p = (\<Sum>j<m. blk W j p * monom 1 (W * j))"
    using bmap_id[OF p] by (simp add: bmap_def)
  have "p * monom 1 (W * s) = (\<Sum>j<m. blk W j p * monom 1 (W * j)) * monom 1 (W * s)"
    by (rule arg_cong[where f="\<lambda>x. x * monom 1 (W * s)", OF pe])
  also have "\<dots> = (\<Sum>j<m. blk W j p * monom 1 (W * (j + s)))"
    by (simp add: sum_distrib_right mult.assoc mult_monom distrib_left)
  finally have ps: "p * monom 1 (W * s) = (\<Sum>j<m. blk W j p * monom 1 (W * (j + s)))" .
  have "bmap n W h (p * monom 1 (W * s)) = (\<Sum>j<m. bmap n W h (blk W j p * monom 1 (W * (j + s))))"
    by (simp only: ps bmap_sum[OF h])
  also have "\<dots> = (\<Sum>j<m. h (blk W j p) * monom 1 (W * (j + s)))"
    by (intro sum.cong refl bmap_mono[OF h bnd_blk]) (use sm in simp)
  also have "\<dots> = bmap m W h p * monom 1 (W * s)"
    by (simp add: bmap_def sum_distrib_right mult.assoc mult_monom distrib_left)
  finally show ?thesis .
qed

lemma bmap_low:
  assumes h: "additive h" and p: "bnd (m * W) p" and sm: "m \<le> n"
  shows "bmap n W h p = bmap m W h p"
  using bmap_shift[OF h p, of 0 n] sm by simp

lemma blk_hi: "bnd (2 * L) g \<Longrightarrow> blk L (Suc 0) g = poly_shift L g"
  by (rule poly_eqI) (auto simp: blk_def coeff_poly_cutoff coeff_poly_shift bnd_def)

lemma bmap_two:
  assumes "bnd (2 * L) g"
  shows "bmap 2 L h g = h (poly_cutoff L g) + h (poly_shift L g) * monom 1 L"
proof -
  have b0: "blk L 0 g = poly_cutoff L g" by (simp add: blk_def)
  have "bmap 2 L h g = h (blk L 0 g) * monom 1 0 + h (blk L (Suc 0) g) * monom 1 L"
    by (simp add: bmap_def numeral_2_eq_2)
  then show ?thesis by (simp only: b0 blk_hi[OF assms]) simp
qed

lemma bnd_cut: "bnd L (poly_cutoff L g)"
  by (rule bnd_cutoff)

lemma bnd_shift2: "bnd (2 * L) g \<Longrightarrow> bnd L (poly_shift L g)"
  by (rule bnd_shift) (simp add: mult_2)

theorem bmap_mulBlock:
  assumes h: "additive h" and hb: "\<And>b. bnd W b \<Longrightarrow> bnd W (h b)"
    and L: "L = a * W" and T: "T = c * W" and ca: "c \<le> a" and g: "bnd (2 * L) g"
  shows "bmap (2 * a) W h (mulBlock L T g) = mulBlock L T (bmap (2 * a) W h g)"
proof -
  define q where "q = poly_shift L g"
  define r where "r = poly_cutoff L g"
  have bq: "bnd (a * W) q" unfolding q_def L[symmetric] by (rule bnd_shift2[OF g])
  have br: "bnd (a * W) r" unfolding r_def L[symmetric] by (rule bnd_cut)
  have lhs: "mulBlock L T g = q * monom 1 (W * a) + q * monom 1 (W * c) + r"
    by (simp add: mulBlock_def q_def r_def L T distrib_left mult.commute)
  have "bmap (2 * a) W h (mulBlock L T g)
      = bmap a W h q * monom 1 (W * a) + bmap a W h q * monom 1 (W * c) + bmap a W h r"
  proof -
    have s1: "bmap (2 * a) W h (q * monom 1 (W * a)) = bmap a W h q * monom 1 (W * a)"
      by (rule bmap_shift[OF h bq]) simp
    have s2: "bmap (2 * a) W h (q * monom 1 (W * c)) = bmap a W h q * monom 1 (W * c)"
      by (rule bmap_shift[OF h bq]) (use ca in simp)
    have s3: "bmap (2 * a) W h r = bmap a W h r"
      by (rule bmap_low[OF h br]) simp
    show ?thesis by (simp only: lhs bmap_add[OF h] s1 s2 s3)
  qed
  moreover have "bmap (2 * a) W h g = bmap a W h r + bmap a W h q * monom 1 L"
  proof -
    have "bmap (2 * a) W h g = bmap 2 L (bmap a W h) g"
      using bmap_bmap[of a W L 2 h g] L by (simp add: mult.commute)
    also have "\<dots> = bmap a W h r + bmap a W h q * monom 1 L"
      by (simp add: bmap_two[OF g] q_def r_def)
    finally show ?thesis .
  qed
  moreover have "mulBlock L T (bmap a W h r + bmap a W h q * monom 1 L)
      = bmap a W h q * (monom 1 L + monom 1 T) + bmap a W h r"
    by (rule mulBlock_split) (simp_all add: L bnd_bmap hb)
  ultimately show ?thesis
  proof -
    assume e1: "bmap (2 * a) W h (mulBlock L T g)
      = bmap a W h q * monom 1 (W * a) + bmap a W h q * monom 1 (W * c) + bmap a W h r"
      and e2: "bmap (2 * a) W h g = bmap a W h r + bmap a W h q * monom 1 L"
      and e3: "mulBlock L T (bmap a W h r + bmap a W h q * monom 1 L)
      = bmap a W h q * (monom 1 L + monom 1 T) + bmap a W h r"
    have mL: "monom 1 L = monom 1 (W * a)" and mT: "monom 1 T = monom 1 (W * c)"
      by (simp_all add: L T mult.commute)
    show ?thesis unfolding e1 e2 e3 by (simp only: mL mT distrib_left)
  qed
qed

definition coarse :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> bool" where
  "coarse N W ls \<longleftrightarrow> (\<forall>x \<in> set ls. case x of (k, L, T) \<Rightarrow> k * (2 * L) = N * W \<and> W dvd L \<and> W dvd T \<and> T \<le> L)"

lemma bmap_lay_comm:
  assumes h: "additive h" and hb: "\<And>b. bnd W b \<Longrightarrow> bnd W (h b)"
    and kL: "k * (2 * L) = N * W" and WL: "W dvd L" and WT: "W dvd T" and TL: "T \<le> L" and W0: "0 < W"
  shows "bmap N W h (lay (k, L, T) f) = lay (k, L, T) (bmap N W h f)"
proof -
  obtain a where a: "L = a * W" using WL by (metis dvd_def mult.commute)
  obtain c where c: "T = c * W" using WT by (metis dvd_def mult.commute)
  have ca: "c \<le> a" using TL W0 by (simp add: a c)
  have N: "N = k * (2 * a)" using kL W0 by (simp add: a)
  have e1: "bmap N W h = bmap k (2 * L) (bmap (2 * a) W h)"
    using bmap_bmap[of "2 * a" W "2 * L" k h] by (auto simp: a N mult.commute)
  have pres1: "\<And>b. bnd (2 * L) b \<Longrightarrow> bnd (2 * L) (mulBlock L T b)" by (simp add: bnd_mulBlock TL)
  have pres2: "\<And>b. bnd (2 * L) b \<Longrightarrow> bnd (2 * L) (bmap (2 * a) W h b)"
    using bnd_bmap[of W h "2 * a"] hb by (simp add: a mult.assoc)
  have "bmap N W h (lay (k, L, T) f) = bmap k (2 * L) (bmap (2 * a) W h) (bmap k (2 * L) (mulBlock L T) f)"
    by (simp add: lay_def e1)
  also have "\<dots> = bmap k (2 * L) (\<lambda>b. bmap (2 * a) W h (mulBlock L T b)) f"
    by (rule bmap_comp[symmetric, OF pres1])
  also have "\<dots> = bmap k (2 * L) (\<lambda>b. mulBlock L T (bmap (2 * a) W h b)) f"
    by (rule bmap_cong) (rule bmap_mulBlock[OF h hb a c ca])
  also have "\<dots> = bmap k (2 * L) (mulBlock L T) (bmap k (2 * L) (bmap (2 * a) W h) f)"
    by (rule bmap_comp[OF pres2])
  also have "\<dots> = lay (k, L, T) (bmap N W h f)"
    by (simp add: lay_def e1)
  finally show ?thesis .
qed

theorem bmap_apl_comm:
  assumes h: "additive h" and hb: "\<And>b. bnd W b \<Longrightarrow> bnd W (h b)" and W0: "0 < W"
    and ok: "coarse N W ls"
  shows "bmap N W h (apl ls f) = apl ls (bmap N W h f)"
  using ok
proof (induction ls arbitrary: f)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  obtain k L T where x: "x = (k, L, T)" by (cases x) auto
  have c: "k * (2 * L) = N * W" "W dvd L" "W dvd T" "T \<le> L" using Cons.prems by (auto simp: coarse_def x)
  have okx: "coarse N W xs" using Cons.prems by (simp add: coarse_def)
  have "bmap N W h (apl (x # xs) f) = apl xs (bmap N W h (lay x f))"
    by (simp add: Cons.IH[OF okx])
  also have "\<dots> = apl (x # xs) (bmap N W h f)"
    by (simp add: x bmap_lay_comm[OF h hb c(1) c(2) c(3) c(4) W0])
  finally show ?case .
qed

lemma mulBlock_add: "mulBlock L T (x + y) = mulBlock L T x + mulBlock L T (y :: 'a :: comm_ring_1 poly)"
proof -
  have s: "poly_shift L (x + y) = poly_shift L x + poly_shift L y"
    by (rule poly_eqI) (simp add: coeff_poly_shift)
  have c: "poly_cutoff L (x + y) = poly_cutoff L x + poly_cutoff L y"
    by (rule poly_eqI) (simp add: coeff_poly_cutoff)
  show ?thesis by (simp add: mulBlock_def s c algebra_simps)
qed

lemma additive_mulBlock: "additive (mulBlock L T :: 'a :: comm_ring_1 poly \<Rightarrow> 'a poly)"
  by (simp add: additive_def mulBlock_add)

lemma additive_bmap: "additive h \<Longrightarrow> additive (bmap n W h)"
  by (simp add: additive_def bmap_add)

lemma additive_apl: "additive (apl ls :: 'a :: comm_ring_1 poly \<Rightarrow> 'a poly)"
proof (induction ls)
  case Nil then show ?case by (simp add: additive_def)
next
  case (Cons x xs)
  obtain k L T where x: "x = (k, L, T)" by (cases x) auto
  have "additive (lay x :: 'a poly \<Rightarrow> 'a poly)"
    unfolding x lay_def by (simp add: additive_bmap additive_mulBlock)
  then show ?case using Cons.IH by (simp add: additive_def)
qed

lemma iradL_dvd: "x \<in> set (iradL M u t) \<Longrightarrow> (case x of (k, L, T) \<Rightarrow> u dvd L \<and> u dvd T)"
  by (induction t arbitrary: x) (auto simp: scale_def split: prod.splits)

lemma layers_dvd: "x \<in> set (layers s v) \<Longrightarrow> (case x of (k, L, T) \<Rightarrow> v dvd L \<and> v dvd T)"
proof (induction s arbitrary: v x)
  case (Lf k) then show ?case by simp
next
  case (Nd j hi lo)
  consider "x \<in> set (map (scale (2 ^ sz hi)) (layers lo v))" | "x \<in> set (layers hi (v * 2 ^ 2 ^ j))"
    | "x \<in> set (iradL (2 ^ j) v (sz hi))"
    using Nd.prems by auto
  then show ?case
  proof cases
    case 1
    then obtain y where y: "y \<in> set (layers lo v)" "x = scale (2 ^ sz hi) y" by auto
    show ?thesis using Nd.IH(2)[OF y(1)] y(2) by (auto simp: scale_def split: prod.splits)
  next
    case 2
    have "v dvd v * 2 ^ 2 ^ j" by simp
    then show ?thesis using Nd.IH(1)[OF 2] by (auto split: prod.splits intro: dvd_trans)
  next
    case 3 then show ?thesis by (rule iradL_dvd)
  qed
qed

theorem swap_node:
  fixes f :: "'a :: char2 poly"
  assumes w: "wf (Nd j hi lo)" and u: "0 < u" and f: "bnd (u * 2 ^ sz (Nd j hi lo)) f"
  shows "apl (layers hi (u * 2 ^ 2 ^ j) @ map (scale (2 ^ sz hi)) (layers lo u)) f
       = apl (map (scale (2 ^ sz hi)) (layers lo u) @ layers hi (u * 2 ^ 2 ^ j)) f"
proof -
  define M where "M = (2::nat) ^ j"
  define K where "K = sz hi"
  define W where "W = u * 2 ^ M"
  have szlo: "sz lo = M" and wh: "wf hi" and wl: "wf lo" using w by (simp_all add: M_def)
  have W0: "0 < W" using u by (simp add: W_def)
  have N: "u * 2 ^ sz (Nd j hi lo) = 2 ^ K * W" by (simp add: M_def K_def W_def power_add algebra_simps)
  have okl: "layok W (layers lo u)" using layok_layers[OF wl, of u] szlo by (simp add: W_def)
  have okh: "layok (2 ^ K * W) (layers hi W)" using layok_layers[OF wh, of W] by (simp add: K_def mult.commute)
  have hb: "\<And>b. bnd W b \<Longrightarrow> bnd W (apl (layers lo u) b)" by (rule bnd_apl[OF okl])
  have co: "coarse (2 ^ K) W (layers hi W)"
    unfolding coarse_def
  proof
    fix x assume x: "x \<in> set (layers hi W)"
    obtain k L T where xe: "x = (k, L, T)" by (cases x) auto
    show "case x of (k, L, T) \<Rightarrow> k * (2 * L) = 2 ^ K * W \<and> W dvd L \<and> W dvd T \<and> T \<le> L"
      using okh x layers_dvd[OF x] by (auto simp: layok_def xe)
  qed
  have f': "bnd (2 ^ K * W) f" using f N by simp
  have fh: "bnd (2 ^ K * W) (apl (layers hi W) f)" by (rule bnd_apl[OF okh f'])
  have "apl (layers hi W @ map (scale (2 ^ K)) (layers lo u)) f = apl (map (scale (2 ^ K)) (layers lo u)) (apl (layers hi W) f)"
    by (simp add: apl_append)
  also have "\<dots> = bmap (2 ^ K) W (apl (layers lo u)) (apl (layers hi W) f)"
    by (rule bmap_apl[symmetric, OF okl fh])
  also have "\<dots> = apl (layers hi W) (bmap (2 ^ K) W (apl (layers lo u)) f)"
    by (rule bmap_apl_comm[OF additive_apl hb W0 co])
  also have "\<dots> = apl (layers hi W) (apl (map (scale (2 ^ K)) (layers lo u)) f)"
    by (simp only: bmap_apl[OF okl f'])
  finally show ?thesis by (simp add: apl_append M_def K_def W_def)
qed

text \<open>The hi-first flattening: the order of the C's recursive cvt (bc_256 on the generic path).\<close>

fun layersR :: "sch \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "layersR (Lf k) u = []"
| "layersR (Nd j hi lo) u =
     layersR hi (u * 2 ^ 2 ^ j) @ map (scale (2 ^ sz hi)) (layersR lo u) @ iradL (2 ^ j) u (sz hi)"

lemma set_layersR: "set (layersR s u) = set (layers s u)"
  by (induction s arbitrary: u) auto

lemma layok_set: "set xs = set ys \<Longrightarrow> layok W xs = layok W ys"
  by (simp add: layok_def)

theorem layersR_layers:
  fixes f :: "'a :: char2 poly"
  assumes "wf s" "0 < u" "bnd (u * 2 ^ sz s) f"
  shows "apl (layersR s u) f = apl (layers s u) f"
  using assms
proof (induction s arbitrary: u f)
  case (Lf k) then show ?case by simp
next
  case (Nd j hi lo)
  define M where "M = (2::nat) ^ j"
  define K where "K = sz hi"
  define W where "W = u * 2 ^ M"
  have szlo: "sz lo = M" and wh: "wf hi" and wl: "wf lo" using Nd.prems(1) by (simp_all add: M_def)
  have W0: "0 < W" using Nd.prems(2) by (simp add: W_def)
  have bf: "bnd (2 ^ K * W) f" and bf': "bnd (W * 2 ^ sz hi) f"
    using Nd.prems(3) by (simp_all add: M_def K_def W_def power_add algebra_simps)
  have okl: "layok W (layers lo u)" using layok_layers[OF wl, of u] szlo by (simp add: W_def)
  have oklR: "layok W (layersR lo u)" using okl layok_set[OF set_layersR] by simp
  have okh: "layok (2 ^ K * W) (layers hi W)" using layok_layers[OF wh, of W] by (simp add: K_def mult.commute)
  have h1: "apl (layersR hi W) f = apl (layers hi W) f" by (rule Nd.IH(1)[OF wh W0 bf'])
  define g where "g = apl (layers hi W) f"
  have bg: "bnd (2 ^ K * W) g" unfolding g_def by (rule bnd_apl[OF okh bf])
  have h2: "apl (map (scale (2 ^ K)) (layersR lo u)) g = apl (map (scale (2 ^ K)) (layers lo u)) g"
  proof -
    have "apl (map (scale (2 ^ K)) (layersR lo u)) g = bmap (2 ^ K) W (apl (layersR lo u)) g"
      by (rule bmap_apl[symmetric, OF oklR bg])
    also have "\<dots> = bmap (2 ^ K) W (apl (layers lo u)) g"
      by (rule bmap_cong) (rule Nd.IH(2)[OF wl Nd.prems(2)], simp add: szlo W_def)
    also have "\<dots> = apl (map (scale (2 ^ K)) (layers lo u)) g"
      by (rule bmap_apl[OF okl bg])
    finally show ?thesis .
  qed
  have "apl (layersR (Nd j hi lo) u) f = apl (iradL M u K) (apl (map (scale (2 ^ K)) (layersR lo u)) (apl (layersR hi W) f))"
    by (simp add: apl_append M_def K_def W_def)
  also have "\<dots> = apl (iradL M u K) (apl (layers hi W @ map (scale (2 ^ K)) (layers lo u)) f)"
    by (simp only: h1 g_def[symmetric] h2) (simp add: apl_append g_def)
  also have "\<dots> = apl (iradL M u K) (apl (map (scale (2 ^ K)) (layers lo u) @ layers hi W) f)"
    using swap_node[OF Nd.prems] by (simp add: M_def K_def W_def)
  also have "\<dots> = apl (layers (Nd j hi lo) u) f"
    by (simp add: apl_append M_def K_def W_def)
  finally show ?case .
qed

end
