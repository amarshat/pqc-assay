theory Flatten
  imports IConv
begin

text \<open>A schedule tree as the flat list of layers the reference C runs. A layer (k, L, T) applies
  mulBlock L T to each of k blocks of 2L coefficients. layers s u lists them for one block of
  u 2^(sz s) coefficients, first applied first. flatten_iconv: on a polynomial of that size,
  iconv s u is the composition of the list.\<close>

definition lay :: "nat \<times> nat \<times> nat \<Rightarrow> 'a :: comm_ring_1 poly \<Rightarrow> 'a poly" where
  "lay x = (case x of (k, L, T) \<Rightarrow> bmap k (2 * L) (mulBlock L T))"

fun apl :: "(nat \<times> nat \<times> nat) list \<Rightarrow> 'a :: comm_ring_1 poly \<Rightarrow> 'a poly" where
  "apl [] f = f"
| "apl (x # xs) f = apl xs (lay x f)"

definition scale :: "nat \<Rightarrow> nat \<times> nat \<times> nat \<Rightarrow> nat \<times> nat \<times> nat" where
  "scale n x = (case x of (k, L, T) \<Rightarrow> (n * k, L, T))"

fun iradL :: "nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "iradL M u 0 = []"
| "iradL M u (Suc t) = map (scale 2) (iradL M u t) @ [(1, u * 2 ^ M * 2 ^ t, u * 2 ^ t)]"

fun layers :: "sch \<Rightarrow> nat \<Rightarrow> (nat \<times> nat \<times> nat) list" where
  "layers (Lf k) u = []"
| "layers (Nd j hi lo) u =
     map (scale (2 ^ sz hi)) (layers lo u) @ layers hi (u * 2 ^ 2 ^ j) @ iradL (2 ^ j) u (sz hi)"

lemma apl_append: "apl (xs @ ys) f = apl ys (apl xs f)"
  by (induction xs arbitrary: f) simp_all

lemma bnd_shift: "bnd (a + b) p \<Longrightarrow> bnd b (poly_shift a p)"
  by (simp add: bnd_def coeff_poly_shift add.commute)

lemma bnd_mulBlock:
  assumes "bnd (2 * L) B" "T \<le> L"
  shows "bnd (2 * L) (mulBlock L T (B :: 'a :: comm_ring_1 poly))"
proof -
  have q: "bnd L (poly_shift L B)" using assms(1) by (intro bnd_shift) (simp add: mult_2)
  have a: "bnd (2 * L) (poly_shift L B * monom 1 L)" by (rule bnd_mult_monom[OF q]) simp
  have b: "bnd (2 * L) (poly_shift L B * monom 1 T)" by (rule bnd_mult_monom[OF q]) (use assms(2) in simp)
  have c: "bnd (2 * L) (poly_cutoff L B)" by (rule bnd_mono[OF bnd_cutoff]) simp
  show ?thesis using a b c by (simp add: mulBlock_def distrib_left bnd_add)
qed

lemma bnd_blk: "bnd W (blk W j f)"
  by (simp add: blk_def bnd_cutoff)

lemma bnd_bmap:
  assumes "\<And>b. bnd W b \<Longrightarrow> bnd W (h b)"
  shows "bnd (n * W) (bmap n W h f)"
  unfolding bmap_def using bnd_packed[of n W "\<lambda>j. h (blk W j f)"] by (simp add: assms bnd_blk mult.commute)

lemma bmap_comp:
  assumes h: "\<And>b. bnd W b \<Longrightarrow> bnd W (h b)"
  shows "bmap n W (\<lambda>b. g (h b)) f = bmap n W g (bmap n W h f)"
proof -
  have "bmap n W g (bmap n W h f) = bmap n W g (\<Sum>j<n. h (blk W j f) * monom 1 (W * j))"
    by (simp add: bmap_def)
  also have "\<dots> = (\<Sum>j<n. g (h (blk W j f)) * monom 1 (W * j))"
    by (rule bmap_packed) (simp add: h bnd_blk)
  finally show ?thesis by (simp add: bmap_def)
qed

lemma blk_blk:
  "i < k \<Longrightarrow> blk W' i (blk (k * W') j f) = blk W' (j * k + i) (f :: 'a :: zero poly)"
proof (rule poly_eqI)
  fix r assume i: "i < k"
  show "coeff (blk W' i (blk (k * W') j f)) r = coeff (blk W' (j * k + i) f) r"
  proof (cases "r < W'")
    case True
    have "r + W' * i < k * W'"
    proof -
      have "r + W' * i < W' + W' * i" using True by simp
      also have "\<dots> = W' * Suc i" by simp
      also have "\<dots> \<le> W' * k" using i by (intro mult_le_mono2) simp
      finally show ?thesis by (simp add: mult.commute)
    qed
    then show ?thesis using True
      by (simp add: blk_def coeff_poly_cutoff coeff_poly_shift algebra_simps)
  qed (simp add: blk_def coeff_poly_cutoff)
qed

lemma bmap_bmap:
  assumes "k * W' = W"
  shows "bmap n W (bmap k W' h) f = bmap (n * k) W' h (f :: 'a :: comm_ring_1 poly)"
proof -
  have "bmap n W (bmap k W' h) f = (\<Sum>j<n. (\<Sum>i<k. h (blk W' (j * k + i) f) * monom 1 (W' * i)) * monom 1 (W * j))"
  proof -
    have Wk: "W = k * W'" using assms by simp
    have inner: "(\<Sum>j<k. h (blk W' j (blk (k * W') x f)) * monom 1 (W' * j))
        = (\<Sum>i<k. h (blk W' (x * k + i) f) * monom 1 (W' * i))" for x
      by (rule sum.cong) (simp_all add: blk_blk)
    show ?thesis unfolding bmap_def Wk by (simp only: inner)
  qed
  also have "\<dots> = (\<Sum>j<n. \<Sum>i<k. h (blk W' (i + k * j) f) * monom 1 (W' * (i + k * j)))"
  proof (intro sum.cong refl)
    fix j :: nat
    have "(\<Sum>i<k. h (blk W' (j * k + i) f) * monom 1 (W' * i)) * monom 1 (W * j)
        = (\<Sum>i<k. h (blk W' (j * k + i) f) * (monom 1 (W' * i) * monom 1 (W * j)))"
      by (simp add: sum_distrib_right mult.assoc)
    also have "\<dots> = (\<Sum>i<k. h (blk W' (i + k * j) f) * monom 1 (W' * (i + k * j)))"
    proof -
      have Wk: "W = k * W'" using assms by simp
      show ?thesis unfolding Wk by (intro sum.cong refl) (simp add: mult_monom algebra_simps)
    qed
    finally show "(\<Sum>i<k. h (blk W' (j * k + i) f) * monom 1 (W' * i)) * monom 1 (W * j)
        = (\<Sum>i<k. h (blk W' (i + k * j) f) * monom 1 (W' * (i + k * j)))" .
  qed
  also have "\<dots> = (\<Sum>m<k * n. h (blk W' m f) * monom 1 (W' * m))"
    by (simp only: sum_lt_mult)
  finally show ?thesis by (simp add: bmap_def mult.commute)
qed

definition layok :: "nat \<Rightarrow> (nat \<times> nat \<times> nat) list \<Rightarrow> bool" where
  "layok W ls \<longleftrightarrow> (\<forall>x \<in> set ls. case x of (k, L, T) \<Rightarrow> k * (2 * L) = W \<and> T \<le> L)"

lemma layok_append [simp]: "layok W (xs @ ys) \<longleftrightarrow> layok W xs \<and> layok W ys"
  by (simp add: layok_def ball_Un)

lemma layok_scale: "layok W ls \<Longrightarrow> layok (n * W) (map (scale n) ls)"
  by (auto simp: layok_def scale_def split: prod.splits)

lemma bnd_lay:
  assumes "k * (2 * L) = W" "T \<le> L"
  shows "bnd W (lay (k, L, T) (f :: 'a :: comm_ring_1 poly))"
proof -
  have "bnd (k * (2 * L)) (bmap k (2 * L) (mulBlock L T) f)"
    by (rule bnd_bmap) (simp add: bnd_mulBlock assms(2))
  then show ?thesis using assms(1) by (simp add: lay_def)
qed

lemma bnd_apl: "layok W ls \<Longrightarrow> bnd W f \<Longrightarrow> bnd W (apl ls (f :: 'a :: comm_ring_1 poly))"
proof (induction ls arbitrary: f)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  obtain k L T where x: "x = (k, L, T)" by (cases x) auto
  have "k * (2 * L) = W" "T \<le> L" using Cons.prems(1) by (auto simp: layok_def x)
  then have "bnd W (lay x f)" by (simp add: x bnd_lay)
  moreover have "layok W xs" using Cons.prems(1) by (simp add: layok_def)
  ultimately show ?case by (simp add: Cons.IH)
qed

lemma bmap_id: "bnd (n * W) f \<Longrightarrow> bmap n W (\<lambda>b. b) f = (f :: 'a :: comm_ring_1 poly)"
proof (rule poly_eqI)
  fix i assume b: "bnd (n * W) f"
  show "coeff (bmap n W (\<lambda>b. b) f) i = coeff f i"
  proof (cases "W = 0")
    case True
    then have "f = 0" using b by (simp add: bnd_def poly_eq_iff)
    then show ?thesis by (simp add: bmap_def blk_def)
  next
    case False
    then have W0: "0 < W" by simp
    have "coeff (bmap n W (\<lambda>b. b) f) i = coeff (\<Sum>j<n. blk W j f * monom 1 (W * j)) (W * (i div W) + i mod W)"
      by (simp add: bmap_def mult.commute[of W])
    also have "\<dots> = (if i div W < n then coeff (blk W (i div W) f) (i mod W) else 0)"
      by (rule coeff_packed) (simp_all add: bnd_blk W0)
    also have "\<dots> = coeff f i"
    proof (cases "i div W < n")
      case True then show ?thesis using W0
        by (simp add: blk_def coeff_poly_cutoff coeff_poly_shift add.commute[of "i mod W"] mult.commute)
    next
      case False
      then have "n * W \<le> i" using W0 by (metis div_less_iff_less_mult not_less)
      then show ?thesis using False b by (simp add: bnd_def)
    qed
    finally show ?thesis .
  qed
qed

lemma bmap_cong: "(\<And>b. bnd W b \<Longrightarrow> h b = h' b) \<Longrightarrow> bmap n W h f = bmap n W h' f"
  unfolding bmap_def by (intro sum.cong refl) (simp add: bnd_blk)

lemma bmap_lay:
  assumes "k * (2 * L) = W"
  shows "bmap n W (lay (k, L, T)) f = lay (scale n (k, L, T)) (f :: 'a :: comm_ring_1 poly)"
  unfolding lay_def scale_def using bmap_bmap[OF assms, of n "mulBlock L T" f] by simp

theorem bmap_apl:
  "layok W ls \<Longrightarrow> bnd (n * W) f \<Longrightarrow> bmap n W (apl ls) f = apl (map (scale n) ls) (f :: 'a :: comm_ring_1 poly)"
proof (induction ls arbitrary: f)
  case Nil
  have "apl [] = (\<lambda>b. b)" by (rule ext) simp
  then show ?case using Nil.prems(2) by (simp add: bmap_id)
next
  case (Cons x xs)
  obtain k L T where x: "x = (k, L, T)" by (cases x) auto
  have kL: "k * (2 * L) = W" "T \<le> L" using Cons.prems(1) by (auto simp: layok_def x)
  have ok: "layok W xs" using Cons.prems(1) by (simp add: layok_def)
  have pres: "\<And>b. bnd W b \<Longrightarrow> bnd W (lay x b)" by (simp add: x bnd_lay kL)
  have e: "apl (x # xs) = (\<lambda>b. apl xs (lay x b))" by (rule ext) simp
  have "bmap n W (apl (x # xs)) f = bmap n W (\<lambda>b. apl xs (lay x b)) f" by (simp only: e)
  also have "\<dots> = bmap n W (apl xs) (bmap n W (lay x) f)" by (rule bmap_comp[OF pres])
  also have "\<dots> = apl (map (scale n) xs) (bmap n W (lay x) f)"
    by (rule Cons.IH[OF ok]) (rule bnd_bmap[OF pres])
  also have "bmap n W (lay x) f = lay (scale n x) f" by (simp add: x bmap_lay kL(1))
  finally show ?case by simp
qed

lemma lay_one: "bnd (2 * L) g \<Longrightarrow> lay (1, L, T) g = mulBlock L T (g :: 'a :: comm_ring_1 poly)"
  by (simp add: lay_def bmap_def blk_def bnd_cutoff_id)

lemma layok_iradL: "layok (u * 2 ^ M * 2 ^ t) (iradL M u t)"
proof (induction t)
  case 0 then show ?case by (simp add: layok_def)
next
  case (Suc t)
  have "layok (2 * (u * 2 ^ M * 2 ^ t)) (map (scale 2) (iradL M u t))" by (rule layok_scale[OF Suc.IH])
  moreover have "u * 2 ^ t \<le> u * 2 ^ M * 2 ^ t" by simp
  ultimately show ?case by (simp add: layok_def algebra_simps)
qed

theorem irad_flat: "bnd (u * 2 ^ M * 2 ^ t) f \<Longrightarrow> irad M u t f = apl (iradL M u t) (f :: 'a :: comm_ring_1 poly)"
proof (induction t arbitrary: f)
  case 0 then show ?case by simp
next
  case (Suc t)
  define W where "W = u * 2 ^ M * 2 ^ t"
  have bf: "bnd (2 * W) f" using Suc.prems by (simp add: W_def algebra_simps)
  have "bmap 2 W (irad M u t) f = bmap 2 W (apl (iradL M u t)) f"
    by (rule bmap_cong) (simp add: Suc.IH W_def)
  also have "\<dots> = apl (map (scale 2) (iradL M u t)) f"
    by (rule bmap_apl) (simp_all add: W_def layok_iradL bf[unfolded W_def])
  finally have b2: "bmap 2 W (irad M u t) f = apl (map (scale 2) (iradL M u t)) f" .
  have bg: "bnd (2 * W) (apl (map (scale 2) (iradL M u t)) f)"
    using bnd_apl[OF layok_scale[OF layok_iradL[of u M t]] bf[unfolded W_def]] by (simp add: W_def)
  have "irad M u (Suc t) f = mulBlock W (u * 2 ^ t) (bmap 2 W (irad M u t) f)" by (simp add: W_def)
  also have "\<dots> = lay (1, W, u * 2 ^ t) (apl (map (scale 2) (iradL M u t)) f)"
    by (simp only: b2 lay_one[OF bg])
  finally show ?case by (simp add: apl_append W_def)
qed

lemma layok_layers: "wf s \<Longrightarrow> layok (u * 2 ^ sz s) (layers s u)"
proof (induction s arbitrary: u)
  case (Lf k) then show ?case by (simp add: layok_def)
next
  case (Nd j hi lo)
  define M where "M = (2::nat) ^ j"
  define K where "K = sz hi"
  have szlo: "sz lo = M" and wh: "wf hi" and wl: "wf lo" using Nd.prems by (simp_all add: M_def)
  have e1: "u * 2 ^ sz (Nd j hi lo) = 2 ^ K * (u * 2 ^ M)" by (simp add: M_def K_def power_add algebra_simps)
  have e2: "u * 2 ^ sz (Nd j hi lo) = u * 2 ^ M * 2 ^ K" by (simp add: M_def K_def power_add algebra_simps)
  have a: "layok (2 ^ K * (u * 2 ^ M)) (map (scale (2 ^ K)) (layers lo u))"
    by (rule layok_scale) (use Nd.IH(2)[OF wl, of u] szlo in simp)
  have b: "layok (u * 2 ^ M * 2 ^ K) (layers hi (u * 2 ^ M))" using Nd.IH(1)[OF wh, of "u * 2 ^ M"] by (simp add: K_def)
  have c: "layok (u * 2 ^ M * 2 ^ K) (iradL M u K)" by (rule layok_iradL)
  have L: "layers (Nd j hi lo) u = map (scale (2 ^ K)) (layers lo u) @ layers hi (u * 2 ^ M) @ iradL M u K"
    by (simp add: M_def K_def)
  have a': "layok (u * 2 ^ sz (Nd j hi lo)) (map (scale (2 ^ K)) (layers lo u))" by (simp only: e1 a)
  have b': "layok (u * 2 ^ sz (Nd j hi lo)) (layers hi (u * 2 ^ M))" by (simp only: e2 b)
  have c': "layok (u * 2 ^ sz (Nd j hi lo)) (iradL M u K)" by (simp only: e2 c)
  show ?case by (simp only: L layok_append a' b' c' simp_thms)
qed

theorem iconv_flat:
  "wf s \<Longrightarrow> bnd (u * 2 ^ sz s) f \<Longrightarrow> iconv s u f = apl (layers s u) (f :: 'a :: char2 poly)"
proof (induction s arbitrary: u f)
  case (Lf k) then show ?case by simp
next
  case (Nd j hi lo)
  define M where "M = (2::nat) ^ j"
  define K where "K = sz hi"
  have szlo: "sz lo = M" and wh: "wf hi" and wl: "wf lo" using Nd.prems(1) by (simp_all add: M_def)
  have bf1: "bnd (2 ^ K * (u * 2 ^ M)) f" and bf2: "bnd (u * 2 ^ M * 2 ^ K) f"
    using Nd.prems(2) by (simp_all add: M_def K_def power_add algebra_simps)
  have okl: "layok (u * 2 ^ M) (layers lo u)" using layok_layers[OF wl, of u] szlo by simp
  define g1 where "g1 = apl (map (scale (2 ^ K)) (layers lo u)) f"
  have s1: "bmap (2 ^ K) (u * 2 ^ M) (iconv lo u) f = g1"
  proof -
    have "bmap (2 ^ K) (u * 2 ^ M) (iconv lo u) f = bmap (2 ^ K) (u * 2 ^ M) (apl (layers lo u)) f"
      by (rule bmap_cong) (use Nd.IH(2)[OF wl] szlo in simp)
    also have "\<dots> = g1" unfolding g1_def by (rule bmap_apl[OF okl bf1])
    finally show ?thesis .
  qed
  have bg1: "bnd (u * 2 ^ M * 2 ^ K) g1"
    using bnd_apl[OF layok_scale[OF okl] bf1] by (simp add: g1_def algebra_simps)
  define g2 where "g2 = apl (layers hi (u * 2 ^ M)) g1"
  have s2: "iconv hi (u * 2 ^ M) g1 = g2"
    unfolding g2_def by (rule Nd.IH(1)[OF wh]) (use bg1 in \<open>simp add: K_def\<close>)
  have okh: "layok (u * 2 ^ M * 2 ^ K) (layers hi (u * 2 ^ M))"
    using layok_layers[OF wh, of "u * 2 ^ M"] by (simp add: K_def)
  have bg2: "bnd (u * 2 ^ M * 2 ^ K) g2" unfolding g2_def by (rule bnd_apl[OF okh bg1])
  have "iconv (Nd j hi lo) u f = irad M u K (iconv hi (u * 2 ^ M) (bmap (2 ^ K) (u * 2 ^ M) (iconv lo u) f))"
    by (simp add: M_def K_def)
  also have "\<dots> = apl (iradL M u K) g2" by (simp only: s1 s2 irad_flat[OF bg2])
  finally show ?case by (simp add: g2_def g1_def apl_append M_def K_def)
qed

end
