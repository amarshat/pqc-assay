theory GFBridge
  imports WordPoly HQC.HQC_Seq HQC.FFTRef
begin

text \<open>The lifted gf264 is multiplication in GF(2^64): the carry-less product (clmul1) folded twice
  with x^64 = x^4 + x^3 + x + 1.\<close>

lemma clmul1_words:
  fixes a b :: w64 and R :: "128 word"
  defines "R \<equiv> foldl (clw_step (seq_to_word a) (seq_to_word b)) 0 [0..<64]"
  shows "seq_to_word (nth_seq (clmul1 a b) 0) = ucast (take_bit 64 (ucast R :: (64 + 64) word))"
    and "seq_to_word (nth_seq (clmul1 a b) (Suc 0)) = ucast (drop_bit 64 (ucast R :: (64 + 64) word))"
  by (simp_all add: clmul1_def Let_def list_to_seq.rep_eq nth_seq.rep_eq seq_to_word.drop' seq_to_word.take'
                  foldl_seq.rep_eq seq_to_list.fromTo seq_to_word.coerce_seq_len fold_bridge seq_to_word.zero R_def)

lemma clmul1_poly:
  fixes a b :: w64
  shows
  "pw (seq_to_word (nth_seq (clmul1 a b) 0)) + monom 1 64 * pw (seq_to_word (nth_seq (clmul1 a b) (Suc 0)))
     = pw (seq_to_word a) * pw (seq_to_word b)"
proof -
  define R where "R = foldl (clw_step (seq_to_word a) (seq_to_word b)) 0 [0..<64]"
  have "pw (ucast R :: (64 + 64) word) = pw (seq_to_word a) * pw (seq_to_word b)"
    by (simp add: pw_ucast_same R_def clw_correct)
  then show ?thesis
    using pw_split[of "ucast R :: (64 + 64) word"] by (simp add: clmul1_words R_def)
qed

lemma left_shift_word: "left_shift (w :: 'a :: len word) (int k) = push_bit k w"
  by (simp add: left_shift_def2 shiftl_def)

lemma left_shift_num [simp]:
  "left_shift (w :: 'a :: len word) 1 = push_bit 1 w"
  "left_shift (w :: 'a :: len word) (numeral n) = push_bit (numeral n) w"
  using left_shift_word[of w 1] left_shift_word[of w "numeral n"] by simp_all

lemma gf2_poly_plus_eq: "(p :: gf2 poly) + q = r \<longleftrightarrow> p = q + r"
proof
  assume e: "p + q = r"
  have "p = p + (q + q)" by simp
  also have "\<dots> = (p + q) + q" by (simp only: add.assoc)
  also have "\<dots> = q + r" using e by (simp add: add.commute)
  finally show "p = q + r" .
next
  assume "p = q + r"
  then have "p + q = q + r + q" by simp
  then show "p + q = r" by (simp only: add.commute[of q r] add.assoc gf2_poly_add_self add_0_right)
qed

lemma split_at:
  "monom 1 k * poly_cutoff (64 - k) H = monom 1 k * H + monom 1 64 * poly_shift (64 - k) (H :: gf2 poly)" if "k \<le> 64"
proof -
  have "H = poly_cutoff (64 - k) H + monom 1 (64 - k) * poly_shift (64 - k) H" by (rule cutoff_shift)
  then have "monom 1 k * H = monom 1 k * poly_cutoff (64 - k) H + monom 1 k * monom 1 (64 - k) * poly_shift (64 - k) H"
    by (metis distrib_left mult.assoc)
  also have "monom 1 k * monom 1 (64 - k) = (monom 1 64 :: gf2 poly)" using that by (simp add: mult_monom)
  finally show ?thesis by (simp add: gf2_poly_plus_eq add.commute)
qed

lemma red_poly_eq:
  fixes Lo Hi :: "gf2 poly"
  defines "Sx \<equiv> poly_shift 63 (Hi :: gf2 poly) + poly_shift 61 Hi + poly_shift 60 Hi"
  assumes lo: "\<And>j. j \<ge> 64 \<Longrightarrow> coeff (Lo :: gf2 poly) j = 0" and hi: "\<And>j. j \<ge> 64 \<Longrightarrow> coeff Hi j = 0"
  shows "Lo + (Hi + monom 1 (Suc 0) * poly_cutoff 63 Hi + monom 1 3 * poly_cutoff 61 Hi + monom 1 4 * poly_cutoff 60 Hi)
           + (Sx + monom 1 (Suc 0) * Sx + monom 1 3 * Sx + monom 1 4 * Sx)
         = (Lo + monom 1 64 * Hi) mod PG"
proof -
  define E where "E = Lo + (Hi + monom 1 (Suc 0) * poly_cutoff 63 Hi + monom 1 3 * poly_cutoff 61 Hi + monom 1 4 * poly_cutoff 60 Hi)
           + (Sx + monom 1 (Suc 0) * Sx + monom 1 3 * Sx + monom 1 4 * Sx)"
  define r where "r = (1 + monom 1 1 + monom 1 3 + monom 1 4 :: gf2 poly)"
  have PGr: "PG = monom 1 64 + r" by (simp add: PG_def r_def ac_simps)
  have s1: "monom 1 (Suc 0) * poly_cutoff 63 Hi = monom 1 1 * Hi + monom 1 64 * poly_shift 63 Hi"
    using split_at[of 1 Hi] by simp
  have s3: "monom 1 3 * poly_cutoff 61 Hi = monom 1 3 * Hi + monom 1 64 * poly_shift 61 Hi"
    using split_at[of 3 Hi] by simp
  have s4: "monom 1 4 * poly_cutoff 60 Hi = monom 1 4 * Hi + monom 1 64 * poly_shift 60 Hi"
    using split_at[of 4 Hi] by simp
  have "E = Lo + r * Hi + monom 1 64 * Sx + r * Sx"
    by (simp add: E_def s1 s3 s4 Sx_def r_def algebra_simps)
  also have "\<dots> = (Lo + monom 1 64 * Hi) + PG * (Hi + Sx)"
    by (simp add: PGr algebra_simps)
  finally have e: "E = (Lo + monom 1 64 * Hi) + PG * (Hi + Sx)" .
  have deg: "coeff E j = 0" if j: "j \<ge> 64" for j
  proof -
    have sh: "coeff (poly_shift k Hi) i = 0" if "k \<ge> 60" "i \<ge> 4" for k i
      using hi[of "i + k"] that by (simp add: coeff_poly_shift)
    show "coeff E j = 0"
      using j lo[OF j] hi[OF j] sh
      by (auto simp: E_def Sx_def coeff_monom_mult coeff_poly_cutoff coeff_poly_shift)
  qed
  have "E mod PG = (Lo + monom 1 64 * Hi) mod PG"
    by (simp add: e mod_PG_add)
  moreover have "E mod PG = E"
  proof (rule red_small)
    show "degree E < 64 \<or> E = 0"
    proof (cases "E = 0")
      case False
      then have "coeff E (degree E) \<noteq> 0" by simp
      then show ?thesis using deg[of "degree E"] by (metis not_less)
    qed simp
  qed
  ultimately show ?thesis by (simp add: E_def)
qed

theorem gf264_poly:
  fixes a b :: w64
  shows "pw (seq_to_word (gf264 a b)) = (pw (seq_to_word a) * pw (seq_to_word b)) mod PG"
proof -
  have "pw (seq_to_word (gf264 a b))
      = (pw (seq_to_word (nth_seq (clmul1 a b) 0)) + monom 1 64 * pw (seq_to_word (nth_seq (clmul1 a b) (Suc 0)))) mod PG"
    by (simp add: gf264_def red128_def fold64_def mull64_def Let_def word_seq_convs seq_to_word.take'
        seq_to_word.drop' seq_to_word.left_shift pw_xor pw_ucast pw_push_bit pw_drop_bit pw_take_bit pw_word_cat
        red_poly_eq[symmetric] coeff_pw_ge)
  then show ?thesis by (simp only: clmul1_poly)
qed

theorem gf264_gf:
  fixes a b :: w64
  shows "gfw (seq_to_word (gf264 a b)) = gfw (seq_to_word a) * gfw (seq_to_word b)"
  by (rule gfw_eqI) (simp add: gf264_poly Rep_gfw)

end
