theory AVX_Toom5
  imports AVX_Toom Toom5
begin

text \<open>Toom-Cook 3 at 256-bit granularity, as the hqc-5 toom_3_mult does it: the same interpolation
  as \<open>AVX_Toom\<close> with y = x^256 (one block of four words). Division by y drops a block; division by
  1 + y is a prefix XOR of blocks. \<open>toom5_correct\<close>: over a correct product of the padded thirds,
  toom5 is the product.\<close>

abbreviation X256 :: "gf2 poly" where "X256 \<equiv> monom 1 256"

text \<open>Runs of zero words behind a constant, so that simp does not expand \<open>replicate 1248 0\<close>.\<close>

definition zeros :: "nat \<Rightarrow> 64 word list" where "zeros n = replicate n 0"

lemma length_zeros[simp]: "length (zeros n) = n"
  by (simp add: zeros_def)

lemma Pl_zeros[simp]: "Pl (zeros n) = 0"
  by (simp add: zeros_def)

lemma Pl_zeros_shift: "Pl (zeros n @ xs) = monom 1 (64 * n) * Pl xs"
  by (simp add: zeros_def Pl_append)

lemma Pl_append_zeros[simp]: "Pl (xs @ zeros n) = Pl xs"
  by (simp add: Pl_append)

lemma take_zeros: "take k (zeros n) = zeros (min k n)"
  by (simp add: zeros_def)

lemma set_zeros: "x \<in> set (zeros n) \<Longrightarrow> x = 0"
  by (simp add: zeros_def)

lemma Pl_drop4:
  assumes "Pl ws = X256 * Q" and "4 \<le> length ws"
  shows "Pl (drop 4 ws) = Q"
proof -
  have split: "Pl ws = Pl (take 4 ws) + X256 * Pl (drop 4 ws)" using Pl_take_drop[OF assms(2)] by simp
  have "Pl (take 4 ws) = 0"
  proof (rule poly_eqI)
    fix j show "coeff (Pl (take 4 ws)) j = coeff 0 j"
    proof (cases "j < 256")
      case True
      have "coeff (Pl ws) j = coeff (Pl (take 4 ws)) j" unfolding split using True by (simp add: coeff_monom_mult)
      with True assms(1) show ?thesis by (simp add: coeff_monom_mult)
    next
      case False then show ?thesis using assms(2) by (simp add: coeff_Pl_ge)
    qed
  qed
  with split assms(1) have "X256 * Pl (drop 4 ws) = X256 * Q" by simp
  then show ?thesis by simp
qed

text \<open>Prefix XOR over blocks of four words, on lists.\<close>

lemma length_foldl_xor4: "length z = 4 \<Longrightarrow> \<forall>b \<in> set bs. length b = 4 \<Longrightarrow> length (foldl (map2 (XOR)) z bs) = 4"
  by (induction bs arbitrary: z) simp_all

lemma Pl_scanl_blocks:
  assumes "length z = 4" "\<forall>b \<in> set bs. length b = 4"
  shows "Pl (concat (tl (scanl_list (map2 (XOR)) z bs))) * (1 + X256)
         = Pl z + Pl (concat bs) + X256 ^ length bs * Pl (foldl (map2 (XOR)) z bs)"
  using assms
proof (induction bs arbitrary: z)
  case Nil then show ?case by simp
next
  case (Cons b bs)
  let ?z' = "map2 (XOR) z b"
  have lb: "length b = 4" using Cons.prems by simp
  have lz': "length ?z' = 4" using Cons.prems by simp
  have 1: "Pl (concat (tl (scanl_list (map2 (XOR)) z (b # bs)))) = Pl ?z' + X256 * Pl (concat (tl (scanl_list (map2 (XOR)) ?z' bs)))"
    by (simp, subst scanl_list_cons_tl, simp add: Pl_append lz' lb Cons.prems(1))
  have IH: "Pl (concat (tl (scanl_list (map2 (XOR)) ?z' bs))) * (1 + X256)
            = Pl ?z' + Pl (concat bs) + X256 ^ length bs * Pl (foldl (map2 (XOR)) ?z' bs)"
    using Cons.IH[OF lz'] Cons.prems by simp
  have pz: "Pl ?z' = Pl z + Pl b" using Cons.prems by (simp add: Pl_xor)
  have "Pl (concat (tl (scanl_list (map2 (XOR)) z (b # bs)))) * (1 + X256)
        = Pl ?z' * (1 + X256) + X256 * (Pl (concat (tl (scanl_list (map2 (XOR)) ?z' bs))) * (1 + X256))"
    unfolding 1 by (simp add: algebra_simps)
  also have "\<dots> = Pl ?z' * (1 + X256) + X256 * (Pl ?z' + Pl (concat bs) + X256 ^ length bs * Pl (foldl (map2 (XOR)) ?z' bs))"
    unfolding IH ..
  also have "\<dots> = Pl z + Pl (concat (b # bs)) + X256 ^ length (b # bs) * Pl (foldl (map2 (XOR)) z (b # bs))"
    using Cons.prems by (simp add: pz Pl_append algebra_simps)
  finally show ?case .
qed

lemma dvd_X256_pow_cancel: "(1 + X256) dvd X256 ^ n * c \<Longrightarrow> (1 + X256) dvd c"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "X256 ^ n * c = (1 + X256) * (X256 ^ n * c) + X256 ^ Suc n * c"
    by (simp add: algebra_simps)
  with Suc.prems have "(1 + X256) dvd X256 ^ n * c" by (metis dvd_add dvd_triv_left)
  then show ?case by (rule Suc.IH)
qed

lemma degree_1_X256: "degree (1 + X256) = 256"
  by (subst degree_add_eq_right) (simp_all add: degree_monom_eq)

lemma one_X256_nonzero: "1 + X256 \<noteq> 0"
  using degree_1_X256 by auto

lemma Pl4_dvd_1_X256: "(1 + X256) dvd Pl c \<Longrightarrow> length c = 4 \<Longrightarrow> Pl c = 0"
proof (rule ccontr)
  assume d: "(1 + X256) dvd Pl c" and l: "length c = 4" and nz: "Pl c \<noteq> 0"
  have "degree (Pl c) \<le> 255" by (rule degree_le) (simp add: l coeff_Pl_ge)
  with dvd_imp_degree_le[OF d nz] degree_1_X256 show False by simp
qed

lemma Pl_pxb:
  assumes bs: "\<forall>b \<in> set bs. length b = 4" and q: "Pl (concat bs) = Q * (1 + X256)"
  shows "Pl (concat (tl (scanl_list (map2 (XOR)) (zeros 4) bs))) = Q"
proof -
  define c where "c = Pl (foldl (map2 (XOR)) (zeros 4) bs)"
  have lc: "length (foldl (map2 (XOR)) (zeros 4) bs) = 4" by (rule length_foldl_xor4[OF _ bs]) simp
  have e: "Pl (concat (tl (scanl_list (map2 (XOR)) (zeros 4) bs))) * (1 + X256) = Q * (1 + X256) + X256 ^ length bs * c"
    using Pl_scanl_blocks[OF _ bs, of "zeros 4"] q by (simp add: c_def)
  have h: "(Pl (concat (tl (scanl_list (map2 (XOR)) (zeros 4) bs))) + Q) * (1 + X256) = X256 ^ length bs * c"
    unfolding distrib_right e by (simp add: add_ac)
  then have "(1 + X256) dvd X256 ^ length bs * c" by (metis dvd_triv_right)
  then have "(1 + X256) dvd c" by (rule dvd_X256_pow_cancel)
  then have "c = 0" unfolding c_def by (rule Pl4_dvd_1_X256) (rule lc)
  with h have "(Pl (concat (tl (scanl_list (map2 (XOR)) (zeros 4) bs))) + Q) * (1 + X256) = 0" by simp
  then have "Pl (concat (tl (scanl_list (map2 (XOR)) (zeros 4) bs))) + Q = 0" using one_X256_nonzero by simp
  then show ?thesis by (metis gf2_poly_add_self_left add.commute add_0_right)
qed

text \<open>Bridges from the lifted model: a sequence of blocks as a list of word lists.\<close>

lemma blocks_len4: "\<forall>b \<in> set (map L (xs :: (4, (64, bool) seq) seq list)). length b = 4"
  by auto

lemma L_scanl_blocks:
  "map L (scanl_list (logic_class.xor) z ys) = scanl_list (map2 (XOR)) (L z) (map L (ys :: (4, (64, bool) seq) seq list))"
  by (induction ys arbitrary: z) (simp_all del: xor_logic_seq add: L_xor)

context includes cryptol_syntax begin

lemma L_zeros: "L (0 :: ('n, (64, bool) seq) seq) = zeros LEN('n)"
  by (simp add: L_zero zeros_def)

lemma L_join: "L (join'`{'n,4,[64]} s) = concat (map L (seq_to_list s))"
  by (simp add: L_def[abs_def] seq_to_list.join' map_concat o_def)

lemma Pl_pxorv:
  assumes n: "1 \<le> LEN('n)" and q: "Pl (L t) = Q * (1 + X256)"
  shows "Pl (L (pxorv`{'n} (t :: [4 * 'n][64]))) = Q"
  unfolding pxorv_def using n
  apply (simp del: xor_logic_seq replicate_numeral add: L_coerce L_join seq_to_list.drop' seq_to_list.scanl_seq L_scanl_blocks L_zeros drop_Suc drop_map map_tl)
  apply (rule Pl_pxb[OF blocks_len4])
  apply (subst L_join[symmetric])
  using q by (simp del: replicate_numeral add: cryptol_prim_defs L_coerce)

lemma len_norm: "8 * LEN('q) = x \<Longrightarrow> LEN(8 * 'q) = x" "4 * LEN('q) = x \<Longrightarrow> LEN(4 * 'q) = x"
  by simp_all

end

context includes cryptol_syntax begin

text \<open>One lemma per step of the lifted model (hqc-5 sizes: thirds of 312 words padded to 320,
  products of 640, output 1872).\<close>

lemma mm1: "monom 1 a * (monom 1 b * (P :: gf2 poly)) = monom 1 (a + b) * P"
  by (simp flip: mult.assoc add: mult_monom)

lemma Pl_L_xor: "Pl (L (logic_class.xor x y)) = Pl (L x) + Pl (L (y :: ('n, (64, bool) seq) seq))"
  by (simp del: xor_logic_seq add: L_xor Pl_xor)

lemma L_vU:
  "L (vU0 a) = take 312 (L a) @ zeros 8"
  "L (vU1 a) = take 312 (drop 312 (L a)) @ zeros 8"
  "L (vU2 a) = drop 624 (L a) @ zeros 8"
  by (simp_all add: vU0_def vU1_def vU2_def L_append L_take L_drop L_zeros L_coerce)

lemma Pl_vS: "Pl (L (vS a)) = Pl (take 312 (L a)) + Pl (take 312 (drop 312 (L a))) + Pl (drop 624 (L a))"
  by (simp del: xor_logic_seq add: vS_def Pl_L_xor L_vU)

lemma Pl_vY: "Pl (L (vY a)) = X256 * Pl (take 312 (drop 312 (L a))) + monom 1 512 * Pl (drop 624 (L a))"
  unfolding vY_def
  by (simp del: xor_logic_seq add: Pl_L_xor L_take L_append L_zeros L_vU take_zeros Pl_zeros_shift Pl_append mm1)

lemma Pl_vQ1: "Pl (L (vQ1 w1 p0)) = Pl (L w1) + Pl (take 624 (L p0))"
  by (simp del: xor_logic_seq add: vQ1_def Pl_L_xor L_take L_append L_zeros L_coerce)

lemma Pl_vQ2:
  assumes "Pl (L p2) + Pl (L p0) = X256 * Q"
  shows "Pl (L (vQ2 p0 p2)) = Q"
proof -
  have h: "Pl (L (logic_class.xor p2 p0)) = X256 * Q" by (simp del: xor_logic_seq add: Pl_L_xor assms)
  have d: "Pl (drop 4 (L (logic_class.xor p2 p0))) = Q" by (rule Pl_drop4[OF h]) simp
  show ?thesis
    unfolding vQ2_def by (simp del: xor_logic_seq add: L_append L_drop L_zeros L_coerce d)
qed

lemma Pl_vD2:
  assumes q: "Pl (L (vQ2 p0 p2)) + Pl (L p3) + Pl (L p2) + Pl (L p4) + monom 1 768 * Pl (take 624 (L p4)) = Q * (1 + X256)"
  shows "Pl (L (vD2 p0 p2 p3 p4)) = Q"
  unfolding vD2_def
  apply (simp del: xor_logic_seq add: L_coerce)
  apply (rule Pl_pxorv)
   apply simp
  apply (simp del: xor_logic_seq add: Pl_L_xor L_append L_take L_zeros L_coerce Pl_zeros_shift)
  using q by (simp add: algebra_simps)

lemma Pl_vD3:
  assumes q: "Pl (L p3) + Pl (L p2) + Pl (L (vQ1 w1 p0)) = X256 * (Q * (1 + X256))"
  shows "Pl (L (vD3 w1 p0 p2 p3)) = Q"
proof -
  have h: "Pl (L (logic_class.xor (logic_class.xor p3 p2) (vQ1 w1 p0))) = X256 * (Q * (1 + X256))"
    by (simp del: xor_logic_seq add: Pl_L_xor q)
  have d: "Pl (drop 4 (L (logic_class.xor (logic_class.xor p3 p2) (vQ1 w1 p0)))) = Q * (1 + X256)"
    by (rule Pl_drop4[OF h]) simp
  show ?thesis
    unfolding vD3_def
    apply (simp del: xor_logic_seq add: L_coerce)
    apply (rule Pl_pxorv)
     apply simp
    by (simp del: xor_logic_seq add: L_append L_drop L_zeros L_coerce d)
qed

lemma Pl_vE:
  "Pl (L (vE1 w1 p0 p2 p3 p4)) = Pl (L (vQ1 w1 p0)) + Pl (L (vD2 p0 p2 p3 p4)) + Pl (L p4)"
  "Pl (L (vE2 w1 p0 p2 p3 p4)) = Pl (L (vD2 p0 p2 p3 p4)) + Pl (L (vD3 w1 p0 p2 p3))"
  by (simp_all del: xor_logic_seq add: vE1_def vE2_def Pl_L_xor)

lemma Pl_vR:
  "Pl (L (vR w0 w1 w2 w3 w4))
     = Pl (take 624 (L w0)) + monom 1 19968 * Pl (take 624 (L w1)) + monom 1 39936 * Pl (L w2)
     + monom 1 59904 * Pl (L w3) + monom 1 79872 * Pl (take 624 (L w4))"
  unfolding vR_def Let_def
  by (simp del: xor_logic_seq add: Pl_L_xor L_take L_append L_zeros L_coerce Pl_append Pl_zeros_shift)

lemma Pl_split3_936:
  fixes a :: "[936][64]"
  shows "Pl (L a) = Pl (take 312 (L a)) + monom 1 19968 * Pl (take 312 (drop 312 (L a))) + monom 1 19968 * monom 1 19968 * Pl (drop 624 (L a))"
proof -
  have 1: "Pl (L a) = Pl (take 312 (L a)) + monom 1 19968 * Pl (drop 312 (L a))"
    using Pl_take_drop[of 312 "L a"] by simp
  have 2: "Pl (drop 312 (L a)) = Pl (take 312 (drop 312 (L a))) + monom 1 19968 * Pl (drop 624 (L a))"
    using Pl_take_drop[of 312 "drop 312 (L a)"] by (simp add: drop_drop)
  show ?thesis unfolding 1 2 by (simp add: distrib_left mult.assoc)
qed

lemma toom5_correct:
  assumes m: "\<And>x y. Pl (L (m x y)) = Pl (L x) * Pl (L y)"
  shows "Pl (L (toom5 m a b)) = Pl (L a) * Pl (L b)"
proof -
  let ?Y = "monom 1 19968 :: gf2 poly"
  define U0 U1 U2 V0 V1 V2 where
    "U0 = Pl (take 312 (L a))" "U1 = Pl (take 312 (drop 312 (L a)))" "U2 = Pl (drop 624 (L a))"
    "V0 = Pl (take 312 (L b))" "V1 = Pl (take 312 (drop 312 (L b)))" "V2 = Pl (drop 624 (L b))"
  have cU: "\<And>i. 19968 \<le> i \<Longrightarrow> coeff U0 i = 0" "\<And>i. 19968 \<le> i \<Longrightarrow> coeff U1 i = 0" "\<And>i. 19968 \<le> i \<Longrightarrow> coeff U2 i = 0"
    and cV: "\<And>i. 19968 \<le> i \<Longrightarrow> coeff V0 i = 0" "\<And>i. 19968 \<le> i \<Longrightarrow> coeff V1 i = 0" "\<And>i. 19968 \<le> i \<Longrightarrow> coeff V2 i = 0"
    unfolding U0_U1_U2_V0_V1_V2_def by (rule coeff_Pl_ge; simp)+
  have A: "Pl (L a) = U0 + ?Y * U1 + ?Y * ?Y * U2" and B: "Pl (L b) = V0 + ?Y * V1 + ?Y * ?Y * V2"
    unfolding U0_U1_U2_V0_V1_V2_def by (rule Pl_split3_936)+
  define w1 p3 p2 p4 p0 where
    "w1 = m (vS b) (vS a)"
    "p3 = m (logic_class.xor (vS a) (vY a)) (logic_class.xor (vS b) (vY b))"
    "p2 = m (logic_class.xor (vY a) (vU0 a)) (logic_class.xor (vY b) (vU0 b))"
    "p4 = m (vU2 a) (vU2 b)"
    "p0 = m (vU0 a) (vU0 b)"
  have unf: "toom5 m a b = vR p0 (vE1 w1 p0 p2 p3 p4) (vE2 w1 p0 p2 p3 p4) (vD3 w1 p0 p2 p3) p4"
    unfolding toom5_def Let_def w1_p3_p2_p4_p0_def by simp
  have Pu: "Pl (L (vU0 a)) = U0" "Pl (L (vU2 a)) = U2" "Pl (L (vU0 b)) = V0" "Pl (L (vU2 b)) = V2"
    and PS: "Pl (L (vS a)) = U0 + U1 + U2" "Pl (L (vS b)) = V0 + V1 + V2"
    and PY: "Pl (L (vY a)) = X256 * U1 + monom 1 512 * U2" "Pl (L (vY b)) = X256 * V1 + monom 1 512 * V2"
    by (simp_all add: L_vU Pl_vS Pl_vY U0_U1_U2_V0_V1_V2_def)
  define W0 W1 W2 W3 W4 where
    "W0 = U0 * V0" "W1 = U0 * V1 + U1 * V0" "W2 = U0 * V2 + U1 * V1 + U2 * V0" "W3 = U1 * V2 + U2 * V1" "W4 = U2 * V2"
  have cW: "\<And>i. 39936 \<le> i + 1 \<Longrightarrow> coeff W0 i = 0" "\<And>i. 39936 \<le> i + 1 \<Longrightarrow> coeff W1 i = 0"
           "\<And>i. 39936 \<le> i + 1 \<Longrightarrow> coeff W2 i = 0" "\<And>i. 39936 \<le> i + 1 \<Longrightarrow> coeff W3 i = 0"
           "\<And>i. 39936 \<le> i + 1 \<Longrightarrow> coeff W4 i = 0"
    unfolding W0_W1_W2_W3_W4_def
    by (simp_all add: coeff_mult_bound[OF cU(1) cV(1)] coeff_mult_bound[OF cU(1) cV(2)] coeff_mult_bound[OF cU(2) cV(1)]
        coeff_mult_bound[OF cU(1) cV(3)] coeff_mult_bound[OF cU(2) cV(2)] coeff_mult_bound[OF cU(3) cV(1)]
        coeff_mult_bound[OF cU(2) cV(3)] coeff_mult_bound[OF cU(3) cV(2)] coeff_mult_bound[OF cU(3) cV(3)])
  have P1: "Pl (L w1) = W0 + W1 + W2 + W3 + W4"
    unfolding w1_p3_p2_p4_p0_def m PS W0_W1_W2_W3_W4_def by (simp add: algebra_simps)
  have P0: "Pl (L p0) = W0" and P4: "Pl (L p4) = W4"
    unfolding w1_p3_p2_p4_p0_def m Pu W0_W1_W2_W3_W4_def by simp_all
  have X2: "monom 1 512 = X256 * (X256 :: gf2 poly)" and X3: "monom 1 768 = X256 * X256 * (X256 :: gf2 poly)"
    by (simp_all add: mult_monom)
  have P2: "Pl (L p2) = W0 + X256 * W1 + X256 ^ 2 * W2 + X256 ^ 3 * W3 + X256 ^ 4 * W4"
    unfolding w1_p3_p2_p4_p0_def m W0_W1_W2_W3_W4_def
    by (simp del: xor_logic_seq add: Pl_L_xor PY Pu X2 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have P3: "Pl (L p3) = W0 + W1 + W2 + W3 + W4 + X256 * (W1 + W3) + X256 ^ 2 * (W2 + W3) + X256 ^ 3 * W3 + X256 ^ 4 * W4"
    unfolding w1_p3_p2_p4_p0_def m W0_W1_W2_W3_W4_def
    by (simp del: xor_logic_seq add: Pl_L_xor PS PY X2 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have tk0: "Pl (take 624 (L p0)) = W0"
    unfolding P0[symmetric]
  proof (rule Pl_take_eq)
    show "624 \<le> length (L p0)" by simp
    fix j :: nat assume j: "64 * 624 \<le> j"
    show "coeff (Pl (L p0)) j = 0" unfolding P0 by (rule cW(1)) (use j in linarith)
  qed
  have tk4: "Pl (take 624 (L p4)) = W4"
    unfolding P4[symmetric]
  proof (rule Pl_take_eq)
    show "624 \<le> length (L p4)" by simp
    fix j :: nat assume j: "64 * 624 \<le> j"
    show "coeff (Pl (L p4)) j = 0" unfolding P4 by (rule cW(5)) (use j in linarith)
  qed
  note tk = tk0 tk4
  have Q1: "Pl (L (vQ1 w1 p0)) = W0 + W1 + W2 + W3 + W4 + W0"
    by (simp add: Pl_vQ1 P1 tk)
  have Q2: "Pl (L (vQ2 p0 p2)) = W1 + X256 * W2 + X256 ^ 2 * W3 + X256 ^ 3 * W4"
    by (rule Pl_vQ2) (simp add: P2 P0 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have D2: "Pl (L (vD2 p0 p2 p3 p4)) = W2 + W3"
    by (rule Pl_vD2) (simp add: Q2 P3 P2 P4 tk X3 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have D3: "Pl (L (vD3 w1 p0 p2 p3)) = W3"
    by (rule Pl_vD3) (simp add: P3 P2 Q1 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have E1: "Pl (L (vE1 w1 p0 p2 p3 p4)) = W1" and E2: "Pl (L (vE2 w1 p0 p2 p3 p4)) = W2"
    by (simp_all add: Pl_vE Q1 D2 D3 P4 algebra_simps)
  have tk1: "Pl (take 624 (L (vE1 w1 p0 p2 p3 p4))) = W1"
    unfolding E1[symmetric]
  proof (rule Pl_take_eq)
    show "624 \<le> length (L (vE1 w1 p0 p2 p3 p4))" by simp
    fix j :: nat assume j: "64 * 624 \<le> j"
    show "coeff (Pl (L (vE1 w1 p0 p2 p3 p4))) j = 0" unfolding E1 by (rule cW(2)) (use j in linarith)
  qed
  have Y2: "monom 1 39936 = ?Y * ?Y" and Y3: "monom 1 59904 = ?Y * ?Y * ?Y" and Y4: "monom 1 79872 = ?Y * ?Y * ?Y * ?Y"
    by (simp_all add: mult_monom)
  show ?thesis
    unfolding unf Pl_vR tk tk1 E2 D3 A B W0_W1_W2_W3_W4_def Y2 Y3 Y4
    by (simp add: algebra_simps)
qed

end

end
