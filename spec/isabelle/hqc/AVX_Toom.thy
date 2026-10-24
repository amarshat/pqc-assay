theory AVX_Toom
  imports AVX_Seq Toom
begin

text \<open>Toom-Cook 3 interpolation over GF(2)[x] as toom_3_mult does it (hqc-1 and hqc-3): the
  evaluation points are 0, 1, y, 1 + y and infinity with y = x^64, and the interpolation divides
  exactly by x^64 (dropping a word) and by 1 + x^64 (a prefix XOR of words). \<open>toom3_correct\<close>:
  over a correct product of the padded thirds, toom3 is the product.\<close>

abbreviation X64 :: "gf2 poly" where "X64 \<equiv> monom 1 64"

lemma coeff_Pl_ge: "64 * length ws \<le> j \<Longrightarrow> coeff (Pl ws) j = 0"
  using div_le_mono[of "64 * length ws" j 64] by (auto simp: coeff_Pl bitsof_def)

lemma Pl_drop_coeff: "k \<le> length ws \<Longrightarrow> coeff (Pl (drop k ws)) j = coeff (Pl ws) (64 * k + j)"
  by (auto simp: coeff_Pl bitsof_def add.commute less_diff_conv)

lemma gf2_poly_add_self_left[simp]: "(p :: gf2 poly) + (p + q) = q"
  by (metis add.assoc gf2_poly_add_self add_0_left)

lemma drop1_tl: "drop 1 xs = tl xs"
  by (cases xs) simp_all

lemma Pl_take_eq:
  assumes "k \<le> length ws" and "\<And>j. 64 * k \<le> j \<Longrightarrow> coeff (Pl ws) j = 0"
  shows "Pl (take k ws) = Pl ws"
proof -
  have "Pl (drop k ws) = 0"
    by (simp add: poly_eq_iff Pl_drop_coeff[OF assms(1)] assms(2))
  then show ?thesis using Pl_take_drop[OF assms(1)] by simp
qed

lemma Pl_append0[simp]: "Pl (ws @ replicate n 0) = Pl ws"
  by (simp add: Pl_append)

lemma pw_degree: "coeff (pw (w :: 64 word)) j = 0" if "64 \<le> j"
  using that by (auto simp: coeff_pw dest: bit_imp_le_length)

lemma Pl_tl:
  assumes "Pl ws = X64 * Q" and "ws \<noteq> []"
  shows "Pl (tl ws) = Q"
proof -
  obtain w ws' where ws: "ws = w # ws'" using assms(2) by (cases ws) auto
  have "pw w = 0"
  proof (rule poly_eqI)
    fix j
    show "coeff (pw w) j = coeff 0 j"
    proof (cases "j < 64")
      case True
      then have "coeff (Pl ws) j = coeff (pw w) j" using ws by (simp add: coeff_monom_mult)
      with True assms(1) show ?thesis by (simp add: coeff_monom_mult)
    next
      case False then show ?thesis by (simp add: pw_degree)
    qed
  qed
  with ws assms(1) have "X64 * Pl ws' = X64 * Q" by simp
  then show ?thesis using ws by simp
qed

lemma Pl_drop1:
  "Pl ws = X64 * Q \<Longrightarrow> 0 < length ws \<Longrightarrow> Pl (drop 1 ws) = Q"
  using Pl_tl[of ws Q] by (cases ws) simp_all

lemma Pl_drop_Suc0:
  "Pl ws = X64 * Q \<Longrightarrow> 0 < length ws \<Longrightarrow> Pl (drop (Suc 0) ws) = Q"
  using Pl_tl[of ws Q] by (cases ws) simp_all

definition pxl :: "64 word list \<Rightarrow> 64 word list" where
  "pxl xs = tl (scanl_list (XOR) 0 xs)"

lemma length_pxl[simp]: "length (pxl xs) = length xs"
  by (simp add: pxl_def)

lemma scanl_list_cons_tl: "scanl_list f b xs = b # tl (scanl_list f b xs)"
  by (cases xs) simp_all

lemma Pl_scanl_tl:
  "Pl (tl (scanl_list (XOR) z xs)) * (1 + X64) = pw z + Pl xs + X64 ^ length xs * pw (foldl (XOR) z xs)"
proof (induction xs arbitrary: z)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  let ?P = "Pl (tl (scanl_list (XOR) (z XOR x) xs))"
  have 1: "Pl (tl (scanl_list (XOR) z (x # xs))) = pw (z XOR x) + X64 * ?P"
    by (simp, subst scanl_list_cons_tl, simp)
  have "Pl (tl (scanl_list (XOR) z (x # xs))) * (1 + X64) = pw (z XOR x) * (1 + X64) + X64 * (?P * (1 + X64))"
    unfolding 1 by (simp add: algebra_simps)
  also have "\<dots> = pw (z XOR x) * (1 + X64) + X64 * (pw (z XOR x) + Pl xs + X64 ^ length xs * pw (foldl (XOR) (z XOR x) xs))"
    unfolding Cons.IH ..
  also have "\<dots> = pw z + Pl (x # xs) + X64 ^ length (x # xs) * pw (foldl (XOR) z (x # xs))"
    by (simp add: pw_xor algebra_simps)
  finally show ?case .
qed

lemma dvd_X64_pow_cancel: "(1 + X64) dvd X64 ^ n * c \<Longrightarrow> (1 + X64) dvd c"
proof (induction n)
  case 0 then show ?case by simp
next
  case (Suc n)
  have "X64 ^ n * c = (1 + X64) * (X64 ^ n * c) + X64 ^ Suc n * c"
    by (simp add: algebra_simps)
  with Suc.prems have "(1 + X64) dvd X64 ^ n * c" by (metis dvd_add dvd_triv_left)
  then show ?case by (rule Suc.IH)
qed

lemma degree_1_X64: "degree (1 + X64) = 64"
  by (subst degree_add_eq_right) (simp_all add: degree_monom_eq)

lemma one_X64_nonzero: "1 + X64 \<noteq> 0"
  using degree_1_X64 by auto

lemma pw_dvd_1_X64: "(1 + X64) dvd pw (w :: 64 word) \<Longrightarrow> pw w = 0"
proof (rule ccontr)
  assume d: "(1 + X64) dvd pw w" and nz: "pw w \<noteq> 0"
  have "degree (pw w) \<le> 63" by (rule degree_le) (simp add: pw_degree)
  with dvd_imp_degree_le[OF d nz] degree_1_X64 show False by simp
qed

lemma Pl_pxl:
  assumes "Pl xs = Q * (1 + X64)"
  shows "Pl (pxl xs) = Q"
proof -
  define c where "c = pw (foldl (XOR) 0 xs)"
  have e: "Pl (pxl xs) * (1 + X64) = Q * (1 + X64) + X64 ^ length xs * c"
    using Pl_scanl_tl[of 0 xs] assms by (simp add: pxl_def c_def)
  have h: "(Pl (pxl xs) + Q) * (1 + X64) = X64 ^ length xs * c"
    unfolding distrib_right e by (simp add: add_ac)
  then have "(1 + X64) dvd X64 ^ length xs * c" by (metis dvd_triv_right)
  then have "c = 0" unfolding c_def by (rule pw_dvd_1_X64[OF dvd_X64_pow_cancel])
  with h have "(Pl (pxl xs) + Q) * (1 + X64) = 0" by simp
  then have "Pl (pxl xs) + Q = 0" using one_X64_nonzero by simp
  then show ?thesis by (metis gf2_poly_add_self_left add.commute add_0_right)
qed

lemma Pl_take_Suc_cons: "Pl (take (Suc n) (0 # ws)) = X64 * Pl (take n ws)"
  by simp

lemma coeff_mult_bound:
  assumes P: "\<And>i. n \<le> i \<Longrightarrow> coeff (P :: gf2 poly) i = 0" and Q: "\<And>i. k \<le> i \<Longrightarrow> coeff Q i = 0"
    and j: "n + k \<le> j + 1"
  shows "coeff (P * Q) j = 0"
proof (cases "P = 0 \<or> Q = 0")
  case True then show ?thesis by auto
next
  case False
  have "n \<noteq> 0" using P False by (cases n) (auto simp: poly_eq_iff)
  moreover have "k \<noteq> 0" using Q False by (cases k) (auto simp: poly_eq_iff)
  ultimately have "n \<noteq> 0" "k \<noteq> 0" .
  have "degree P \<le> n - 1" by (rule degree_le) (use P in auto)
  moreover have "degree Q \<le> k - 1" by (rule degree_le) (use Q in auto)
  ultimately have "degree (P * Q) < j" using degree_mult_le[of P Q] j \<open>n \<noteq> 0\<close> \<open>k \<noteq> 0\<close> by linarith
  then show ?thesis by (rule coeff_eq_0)
qed

lemma Pl_take_shift1: "k = length xs + 2 \<Longrightarrow> Pl (take k (0 # xs @ replicate 2 0)) = X64 * Pl xs"
  by (simp add: take_Cons' take_append numeral_2_eq_2 Pl_append)

lemma Pl_take_shift2: "k = length xs + 2 \<Longrightarrow> Pl (take k (0 # 0 # xs @ replicate 2 0)) = X64 * X64 * Pl xs"
  by (simp add: take_Cons' take_append numeral_2_eq_2 Pl_append algebra_simps)

lemma Pl_take_shift3: "k = n + 3 \<Longrightarrow> Pl (take k (0 # 0 # 0 # xs)) = X64 * X64 * X64 * Pl (take n xs)"
  by (simp add: take_Cons' algebra_simps)

lemma Pl_replicate_shift: "Pl (replicate n 0 @ xs) = monom 1 (64 * n) * Pl xs"
  by (simp add: Pl_append)

text \<open>Bridges from the lifted model.\<close>

lemma s2w_scanl:
  "map seq_to_word (scanl_list (logic_class.xor) z ys) = scanl_list (XOR) (seq_to_word z) (map seq_to_word (ys :: (64, bool) seq list))"
  by (induction ys arbitrary: z) (simp_all add: seq_to_word.xor split_def s2w_xor)

context includes cryptol_syntax begin

lemma L_pxor: "1 \<le> LEN('n) \<Longrightarrow> L (Toom.pxor`{'n} (t :: ['n][64])) = pxl (L t)"
  unfolding pxor_def pxl_def
  by (simp del: xor_logic_seq add: L_def seq_to_list.drop' seq_to_list.scanl_seq s2w_scanl seq_to_word.zero drop_Suc drop_map map_tl)

lemma L_lit1: "L (list_to_seq [0 :: w64] :: [1][64]) = [0]"
  and L_lit2: "L (list_to_seq [0 :: w64, 0] :: [2][64]) = [0, 0]"
  and L_lit3: "L (list_to_seq [0 :: w64, 0, 0] :: [3][64]) = [0, 0, 0]"
  by (simp_all add: L_def seq_to_word.zero)

end

context includes cryptol_syntax begin

text \<open>One lemma per step of the lifted model.\<close>

lemma L_tU:
  "L (tU0`{'p} a) = take LEN('p) (L a) @ replicate 2 0"
  "L (tU1`{'p} a) = take LEN('p) (drop LEN('p) (L a)) @ replicate 2 0"
  "L (tU2`{'p} a) = drop (LEN('p) + LEN('p)) (L a) @ replicate 2 0"
  by (simp_all add: tU0_def tU1_def tU2_def L_append L_take L_drop L_zero L_coerce mult_2)

lemma Pl_tS: "Pl (L (tS`{'p} a)) = Pl (take LEN('p) (L a)) + Pl (take LEN('p) (drop LEN('p) (L a))) + Pl (drop (LEN('p) + LEN('p)) (L a))"
  by (simp del: xor_logic_seq add: tS_def L_xor Pl_xor Pl_append L_tU)

lemma Pl_tY: "Pl (L (tY`{'p} a)) = X64 * Pl (take LEN('p) (drop LEN('p) (L a))) + X64 * X64 * Pl (drop (LEN('p) + LEN('p)) (L a))"
  if "1 \<le> LEN('p)"
  using that by (simp del: xor_logic_seq add: tY_def L_xor Pl_xor Pl_append L_take L_append L_lit1 L_lit2 L_tU Pl_take_shift1 Pl_take_shift2 algebra_simps)

lemma Pl_tQ2:
  assumes "Pl (L p2) + Pl (L p0) = X64 * Q"
  shows "Pl (L (tQ2`{'p} p0 (p2 :: [4 + (2 * 'p)][64]))) = Q"
proof -
  have "Pl (map2 (XOR) (L p2) (L p0)) = X64 * Q" by (simp add: Pl_xor assms)
  then show ?thesis
    unfolding tQ2_def by (simp del: xor_logic_seq add: L_append L_xor L_drop L_lit1 L_coerce Pl_append Pl_drop_Suc0)
qed

lemma Pl_tD2:
  assumes p: "1 \<le> LEN('p)"
    and q: "Pl (L (tQ2`{'p} p0 p2)) + Pl (L p3) + Pl (L p2) + Pl (L p4) + X64 * X64 * X64 * Pl (L p4) = Q * (1 + X64)"
    and cQ: "\<And>j. 64 * (LEN('p) + LEN('p)) \<le> j \<Longrightarrow> coeff Q j = 0"
    and c4: "\<And>j. 64 * (2 * LEN('p) + 1) \<le> j \<Longrightarrow> coeff (Pl (L p4)) j = 0"
  shows "Pl (L (tD2`{'p} p0 p2 p3 (p4 :: [4 + (2 * 'p)][64]))) = Q"
proof -
  let ?T = "LEN('p)"
  have "Pl (take (2 * ?T + 1) (L p4)) = Pl (L p4)" by (rule Pl_take_eq) (simp, rule c4, simp)
  then have sh: "Pl (take (4 + 2 * ?T) (0 # 0 # 0 # L p4)) = X64 * X64 * X64 * Pl (L p4)"
    by (subst Pl_take_shift3[of _ "2 * ?T + 1"]) simp_all
  have t: "Pl (map2 (XOR) (map2 (XOR) (map2 (XOR) (map2 (XOR) (L (tQ2`{'p} p0 p2)) (L p3)) (L p2)) (L p4))
              (take (4 + 2 * ?T) (0 # 0 # 0 # L p4))) = Q * (1 + X64)"
    by (simp add: Pl_xor sh q)
  have fin: "Pl (take (2 * ?T) (pxl (map2 (XOR) (map2 (XOR) (map2 (XOR) (map2 (XOR) (L (tQ2`{'p} p0 p2)) (L p3)) (L p2)) (L p4))
              (take (4 + 2 * ?T) (0 # 0 # 0 # L p4))))) = Q"
    by (subst Pl_take_eq) (simp_all add: Pl_pxl[OF t] cQ)
  show ?thesis
    unfolding tD2_def using p by (simp del: xor_logic_seq add: L_append L_xor L_take L_zero L_lit3 L_coerce L_pxor Pl_append fin)
qed

lemma Pl_tD3:
  assumes p: "1 \<le> LEN('p)"
    and q: "Pl (L p3) + Pl (L p2) + Pl (L w1) + Pl (L p0) = X64 * (Q * (1 + X64))"
    and cQ: "\<And>j. 64 * (LEN('p) + LEN('p)) \<le> j \<Longrightarrow> coeff Q j = 0"
  shows "Pl (L (tD3`{'p} w1 p0 p2 (p3 :: [4 + (2 * 'p)][64]))) = Q"
proof -
  let ?T = "LEN('p)"
  have "Pl (map2 (XOR) (map2 (XOR) (map2 (XOR) (L p3) (L p2)) (L w1)) (L p0)) = X64 * (Q * (1 + X64))"
    by (simp add: Pl_xor q)
  then have t: "Pl (drop (Suc 0) (map2 (XOR) (map2 (XOR) (map2 (XOR) (L p3) (L p2)) (L w1)) (L p0)) @ [0]) = Q * (1 + X64)"
    by (simp add: Pl_append Pl_drop_Suc0)
  have fin: "Pl (take (2 * ?T) (pxl (drop (Suc 0) (map2 (XOR) (map2 (XOR) (map2 (XOR) (L p3) (L p2)) (L w1)) (L p0)) @ [0]))) = Q"
    by (subst Pl_take_eq) (simp_all add: Pl_pxl[OF t] cQ)
  show ?thesis
    unfolding tD3_def using p by (simp del: xor_logic_seq add: L_append L_xor L_drop L_take L_zero L_lit1 L_coerce L_pxor Pl_append fin)
qed

lemma Pl_tE:
  "1 \<le> LEN('p) \<Longrightarrow> Pl (L (tE1`{'p} w1 p0 p2 p3 (p4 :: [4 + (2 * 'p)][64]))) = Pl (L w1) + Pl (L p0) + Pl (L (tD2`{'p} p0 p2 p3 p4)) + Pl (L p4)"
  "1 \<le> LEN('p) \<Longrightarrow> Pl (L (tE2`{'p} w1 p0 p2 p3 p4)) = Pl (L (tD2`{'p} p0 p2 p3 p4)) + Pl (L (tD3`{'p} w1 p0 p2 p3))"
  by (simp_all del: xor_logic_seq add: tE1_def tE2_def L_xor Pl_xor)

lemma coeff_tR_term:
  assumes "e \<le> 256 * LEN('p)" "64 * (4 + 6 * LEN('p)) \<le> j"
  shows "coeff (monom 1 e * Pl (L (w :: [4 + (2 * 'p)][64]))) j = 0"
proof -
  have "64 * length (L w) \<le> j - e" using assms by (simp; linarith)
  then show ?thesis by (simp add: coeff_monom_mult coeff_Pl_ge)
qed

lemma coeff_tR_term0:
  assumes "64 * (4 + 6 * LEN('p)) \<le> j"
  shows "coeff (Pl (L (w :: [4 + (2 * 'p)][64]))) j = 0"
  using assms by (intro coeff_Pl_ge) (simp; linarith)

lemma Pl_tR:
  "Pl (L (tR`{'p} w0 w1 w2 w3 (w4 :: [4 + (2 * 'p)][64]))) = Pl (L w0) + monom 1 (64 * LEN('p)) * Pl (L w1)
     + monom 1 (64 * LEN('p)) ^ 2 * Pl (L w2) + monom 1 (64 * LEN('p)) ^ 3 * Pl (L w3) + monom 1 (64 * LEN('p)) ^ 4 * Pl (L w4)"
  unfolding tR_def Let_def
  apply (simp del: xor_logic_seq add: L_take L_xor L_append L_zero L_coerce)
  apply (subst Pl_take_eq)
    apply simp
   apply (simp add: Pl_xor Pl_append Pl_replicate_shift coeff_add coeff_tR_term coeff_tR_term0)
  apply (simp add: Pl_xor Pl_append Pl_replicate_shift X_pow algebra_simps)
  done

lemma toom3_correct:
  assumes p: "4 \<le> LEN('p)"
    and m: "\<And>x y. Pl (L (m x y)) = Pl (L x) * Pl (L y)"
  shows "Pl (L (toom3`{'p} m a b)) = Pl (L a) * Pl (L b)"
proof -
  let ?T = "LEN('p)"
  let ?Y = "monom 1 (64 * LEN('p)) :: gf2 poly"
  have p1: "1 \<le> ?T" using p by simp
  define U0 U1 U2 V0 V1 V2 where
    "U0 = Pl (take ?T (L a))" "U1 = Pl (take ?T (drop ?T (L a)))" "U2 = Pl (drop (?T + ?T) (L a))"
    "V0 = Pl (take ?T (L b))" "V1 = Pl (take ?T (drop ?T (L b)))" "V2 = Pl (drop (?T + ?T) (L b))"
  have cU: "\<And>i. 64 * ?T \<le> i \<Longrightarrow> coeff U0 i = 0" "\<And>i. 64 * ?T \<le> i \<Longrightarrow> coeff U1 i = 0" "\<And>i. 64 * ?T \<le> i \<Longrightarrow> coeff U2 i = 0"
    and cV: "\<And>i. 64 * ?T \<le> i \<Longrightarrow> coeff V0 i = 0" "\<And>i. 64 * ?T \<le> i \<Longrightarrow> coeff V1 i = 0" "\<And>i. 64 * ?T \<le> i \<Longrightarrow> coeff V2 i = 0"
    unfolding U0_U1_U2_V0_V1_V2_def by (rule coeff_Pl_ge; simp)+
  have A: "Pl (L a) = U0 + ?Y * U1 + ?Y * ?Y * U2" and B: "Pl (L b) = V0 + ?Y * V1 + ?Y * ?Y * V2"
    unfolding U0_U1_U2_V0_V1_V2_def
    by (subst Pl_take_drop[of ?T], simp, subst Pl_take_drop[of ?T "drop ?T _"], simp,
        simp add: drop_drop mult_monom algebra_simps)+
  define w1 p3 p2 p4 p0 where
    "w1 = m (tS`{'p} b) (tS`{'p} a)"
    "p3 = m (logic_class.xor (tS`{'p} a) (tY`{'p} a)) (logic_class.xor (tS`{'p} b) (tY`{'p} b))"
    "p2 = m (logic_class.xor (tY`{'p} a) (tU0`{'p} a)) (logic_class.xor (tY`{'p} b) (tU0`{'p} b))"
    "p4 = m (tU2`{'p} a) (tU2`{'p} b)"
    "p0 = m (tU0`{'p} a) (tU0`{'p} b)"
  have unf: "toom3`{'p} m a b = tR`{'p} p0 (tE1`{'p} w1 p0 p2 p3 p4) (tE2`{'p} w1 p0 p2 p3 p4) (tD3`{'p} w1 p0 p2 p3) p4"
    using p unfolding toom3_def Let_def w1_p3_p2_p4_p0_def by simp
  have Pu: "Pl (L (tU0`{'p} a)) = U0" "Pl (L (tU2`{'p} a)) = U2" "Pl (L (tU0`{'p} b)) = V0" "Pl (L (tU2`{'p} b)) = V2"
    and PS: "Pl (L (tS`{'p} a)) = U0 + U1 + U2" "Pl (L (tS`{'p} b)) = V0 + V1 + V2"
    and PY: "Pl (L (tY`{'p} a)) = X64 * U1 + X64 * X64 * U2" "Pl (L (tY`{'p} b)) = X64 * V1 + X64 * X64 * V2"
    by (simp_all add: L_tU Pl_tS Pl_tY[OF p1] Pl_append U0_U1_U2_V0_V1_V2_def)
  define W0 W1 W2 W3 W4 where
    "W0 = U0 * V0" "W1 = U0 * V1 + U1 * V0" "W2 = U0 * V2 + U1 * V1 + U2 * V0" "W3 = U1 * V2 + U2 * V1" "W4 = U2 * V2"
  have cW: "\<And>i. 64 * (?T + ?T) \<le> i + 1 \<Longrightarrow> coeff W2 i = 0" "\<And>i. 64 * (?T + ?T) \<le> i + 1 \<Longrightarrow> coeff W3 i = 0" "\<And>i. 64 * (?T + ?T) \<le> i + 1 \<Longrightarrow> coeff W4 i = 0"
    unfolding W0_W1_W2_W3_W4_def by (simp_all add: coeff_mult_bound[OF cU(1) cV(3)] coeff_mult_bound[OF cU(2) cV(2)] coeff_mult_bound[OF cU(3) cV(1)]
        coeff_mult_bound[OF cU(2) cV(3)] coeff_mult_bound[OF cU(3) cV(2)] coeff_mult_bound[OF cU(3) cV(3)])
  have P1: "Pl (L w1) = W0 + W1 + W2 + W3 + W4"
    unfolding w1_p3_p2_p4_p0_def m PS W0_W1_W2_W3_W4_def by (simp add: algebra_simps)
  have P0: "Pl (L p0) = W0" and P4: "Pl (L p4) = W4"
    unfolding w1_p3_p2_p4_p0_def m Pu W0_W1_W2_W3_W4_def by simp_all
  have P2: "Pl (L p2) = W0 + X64 * W1 + X64 ^ 2 * W2 + X64 ^ 3 * W3 + X64 ^ 4 * W4"
    unfolding w1_p3_p2_p4_p0_def m W0_W1_W2_W3_W4_def
    by (simp del: xor_logic_seq add: L_xor Pl_xor PY Pu algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have P3: "Pl (L p3) = W0 + W1 + W2 + W3 + W4 + X64 * (W1 + W3) + X64 ^ 2 * (W2 + W3) + X64 ^ 3 * W3 + X64 ^ 4 * W4"
    unfolding w1_p3_p2_p4_p0_def m W0_W1_W2_W3_W4_def
    by (simp del: xor_logic_seq add: L_xor Pl_xor PS PY algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have Q2: "Pl (L (tQ2`{'p} p0 p2)) = W1 + X64 * W2 + X64 ^ 2 * W3 + X64 ^ 3 * W4"
    by (rule Pl_tQ2) (simp add: P2 P0 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
  have D2: "Pl (L (tD2`{'p} p0 p2 p3 p4)) = W2 + W3"
    apply (rule Pl_tD2[OF p1])
      apply (simp add: Q2 P3 P2 P4 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
     apply (simp add: cW)
    apply (simp add: P4 cW)
    done
  have D3: "Pl (L (tD3`{'p} w1 p0 p2 p3)) = W3"
    apply (rule Pl_tD3[OF p1])
     apply (simp add: P3 P2 P1 P0 algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
    apply (simp add: cW)
    done
  have E1: "Pl (L (tE1`{'p} w1 p0 p2 p3 p4)) = W1" and E2: "Pl (L (tE2`{'p} w1 p0 p2 p3 p4)) = W2"
    by (simp_all add: Pl_tE[OF p1] P1 P0 D2 D3 P4 algebra_simps)
  show ?thesis
    unfolding unf Pl_tR P0 E1 E2 D3 P4 A B W0_W1_W2_W3_W4_def
    by (simp add: algebra_simps power2_eq_square power3_eq_cube power4_eq_xxxx)
qed

end

end
