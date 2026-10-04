(* v4, matrix-vector step: one row of A*y.

   ML-DSA computes NTT^-1(A_hat o NTT(y)) in key generation (FIPS 204 Alg 6, with s1) and signing
   (Alg 7, with y), where A_hat is sampled directly in NTT form. The reference does one row as
     polyvecl_pointwise_acc_montgomery   (acc: four pointwise products summed with poly_add)
     poly_reduce                         (preduce: reduce32 on every coefficient)
     poly_invntt_tomont                  (invntt)
   ntt_mult_correct needs both operands to be ntt outputs, which A_hat is not. The theorem here takes
   an arbitrary NTT-domain operand, so it is stated in the FIPS form: 256 times the output equals
   the unnormalised inverse transform of sum_i A_hat_i o y_hat_i, mod q. The ring reading, for an
   operand that is the transform of a polynomial, is the corollary acc_mult_ring.

   Bounds are derived: each pointwise output is below q, four of them sum below 4q (no int32 wrap in
   poly_add), that is inside reduce32's precondition, and reduce32's output window is inside the
   |coeff| < q that invntt_signed_correct needs. *)
theory Acc_Bridge
  imports "Tier2_Conv.Conv_Bridge"
begin

context includes cryptol_translation_syntax begin

lemma nth_seq_padd:
  assumes k: "k < 256"
  shows "nth_seq (padd x y) k = nth_seq x k + nth_seq y k"
  using k by (simp add: padd_def)

lemma nth_seq_preduce:
  assumes k: "k < 256"
  shows "nth_seq (preduce x) k = reduce32 (nth_seq x k)"
  using k by (simp add: preduce_def)

lemma acc_unfold:
  "acc u v = padd (padd (padd (pointwise (nth_seq u 0) (nth_seq v 0))
                              (pointwise (nth_seq u 1) (nth_seq v 1)))
                        (pointwise (nth_seq u 2) (nth_seq v 2)))
                  (pointwise (nth_seq u 3) (nth_seq v 3))"
  by (simp add: acc_def)

end

context includes cryptol_syntax begin

declare [[coercion_enabled = false]]

abbreviation (input) pw :: "[4][256][32] \<Rightarrow> [4][256][32] \<Rightarrow> nat \<Rightarrow> [256][32]" where
  "pw u v i \<equiv> pointwise (nth_seq u i) (nth_seq v i)"

lemma pw_bound:
  assumes bu: "ntt_bounded 75423752 (nth_seq u i)" and bv: "ntt_bounded 75423752 (nth_seq v i)"
    and m: "m < 256"
  shows "- 8380416 \<le> sf (pw u v i) m \<and> sf (pw u v i) m \<le> 8380416"
proof -
  have "- 8380417 < sf (pw u v i) m \<and> sf (pw u v i) m < 8380417"
    using mont_butterfly_bound[OF pointwise_ok[OF bu bv, of m]]
    by (simp add: nth_seq_pointwise[OF m] sf_def)
  thus ?thesis by linarith
qed

lemma pw_cong:
  assumes bu: "ntt_bounded 75423752 (nth_seq u i)" and bv: "ntt_bounded 75423752 (nth_seq v i)"
    and m: "m < 256"
  shows "[4294967296 * sf (pw u v i) m = sf (nth_seq u i) m * sf (nth_seq v i) m] (mod 8380417)"
  using pointwise_bridge[OF m pointwise_ok[OF bu bv]] unfolding cong_def sf_def by simp

text \<open>The accumulator is the exact integer sum of the four products: no partial sum wraps.\<close>

lemma acc_exact:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and bv: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq v i)"
    and m: "m < 256"
  shows "sf (acc u v) m = (\<Sum>i<4. sf (pw u v i) m)"
proof -
  have b0: "- 8380416 \<le> sf (pw u v 0) m \<and> sf (pw u v 0) m \<le> 8380416" by (rule pw_bound[OF bu bv m]) simp_all
  have b1: "- 8380416 \<le> sf (pw u v 1) m \<and> sf (pw u v 1) m \<le> 8380416" by (rule pw_bound[OF bu bv m]) simp_all
  have b2: "- 8380416 \<le> sf (pw u v 2) m \<and> sf (pw u v 2) m \<le> 8380416" by (rule pw_bound[OF bu bv m]) simp_all
  have b3: "- 8380416 \<le> sf (pw u v 3) m \<and> sf (pw u v 3) m \<le> 8380416" by (rule pw_bound[OF bu bv m]) simp_all
  have s01: "sint_seq (nth_seq (pw u v 0) m + nth_seq (pw u v 1) m)
               = sf (pw u v 0) m + sf (pw u v 1) m"
    using b0 b1 unfolding sf_def by (intro sint_seq_add_eq) linarith+
  have s012: "sint_seq (nth_seq (pw u v 0) m + nth_seq (pw u v 1) m + nth_seq (pw u v 2) m)
               = sf (pw u v 0) m + sf (pw u v 1) m + sf (pw u v 2) m"
    using b0 b1 b2 s01 unfolding sf_def by (subst sint_seq_add_eq) linarith+
  have s0123: "sint_seq (nth_seq (pw u v 0) m + nth_seq (pw u v 1) m + nth_seq (pw u v 2) m
                         + nth_seq (pw u v 3) m)
               = sf (pw u v 0) m + sf (pw u v 1) m + sf (pw u v 2) m + sf (pw u v 3) m"
    using b0 b1 b2 b3 s012 unfolding sf_def by (subst sint_seq_add_eq) linarith+
  show ?thesis
    using s0123 m by (simp add: acc_unfold nth_seq_padd sf_def eval_nat_numeral)
qed

lemma acc_bound:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and bv: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq v i)"
    and m: "m < 256"
  shows "\<bar>sf (acc u v) m\<bar> \<le> 33521664"
proof -
  have "\<bar>sf (pw u v i) m\<bar> \<le> 8380416" if i: "i < 4" for i
    using pw_bound[OF bu[OF i] bv[OF i] m] by (simp add: abs_le_iff)
  hence "\<bar>\<Sum>i<4. sf (pw u v i) m\<bar> \<le> (\<Sum>i<(4::nat). 8380416)"
    by (intro order.trans[OF sum_abs] sum_mono) simp
  thus ?thesis by (simp add: acc_exact[OF bu bv m])
qed

text \<open>After \<open>poly_reduce\<close>: congruent to the accumulator, and inside \<open>|coeff| < q\<close>.\<close>

lemma preduce_acc:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and bv: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq v i)"
    and m: "m < 256"
  shows "sf (preduce (acc u v)) m mod 8380417 = sf (acc u v) m mod 8380417"
    and "- 6283009 \<le> sf (preduce (acc u v)) m" "sf (preduce (acc u v)) m \<le> 6283008"
proof -
  have ok: "reduce32_input_ok (sint_seq (nth_seq (acc u v) m))"
    using acc_bound[OF bu bv m] unfolding reduce32_input_ok_def sf_def by (simp add: abs_le_iff)
  have r: "is_reduce32 (sint_seq (nth_seq (acc u v) m)) (sint_seq (reduce32 (nth_seq (acc u v) m)))"
    by (rule reduce32_correct[OF ok])
  show "sf (preduce (acc u v)) m mod 8380417 = sf (acc u v) m mod 8380417"
       "- 6283009 \<le> sf (preduce (acc u v)) m" "sf (preduce (acc u v)) m \<le> 6283008"
    using r unfolding is_reduce32_def MLDSA_NTT_Spec.q_def sf_def
    by (simp_all add: nth_seq_preduce[OF m])
qed

lemma preduce_acc_bounded:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and bv: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq v i)"
  shows "ntt_bounded 8380416 (preduce (acc u v))"
  unfolding ntt_bounded_def
proof (intro allI)
  fix n
  have out: "- 8380416 \<le> sint_seq (nth_seq (preduce (acc u v)) m)
             \<and> sint_seq (nth_seq (preduce (acc u v)) m) \<le> 8380416" if m: "m < 256" for m
    using preduce_acc(2,3)[OF bu bv m] unfolding sf_def by linarith
  show "- 8380416 \<le> sint_seq (nth_seq (preduce (acc u v)) n)
        \<and> sint_seq (nth_seq (preduce (acc u v)) n) \<le> 8380416"
  proof (cases "n < 256")
    case True thus ?thesis using out by blast
  next
    case False hence ge: "256 \<le> n" by simp
    show ?thesis using out[of 255] oob255[OF ge, of "preduce (acc u v)"] by simp
  qed
qed

subsection \<open>The row theorem, FIPS form\<close>

theorem acc_mult_fips:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and bv: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq v i)"
    and k: "k < 256"
  shows "(256 * sint_seq (nth_seq (invntt (preduce (acc u v))) k)) mod 8380417
       = (\<Sum>i<4. \<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m
                           * zpw (- (2 * int (brv 8 m) + 1) * int k)) mod 8380417"
proof -
  let ?P = "preduce (acc u v)"
  let ?C = "invntt ?P"
  define z where "z m = zpw (- (2 * int (brv 8 m) + 1) * int k)" for m
  define S where "S = (\<Sum>i<4. \<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m * z m)"
  have bP: "ntt_bounded 8380416 ?P" by (rule preduce_acc_bounded[OF bu bv])
  have iv: "[4294967296 * sf ?C k = 41978 * (\<Sum>m<256. sf ?P m * z m)] (mod 8380417)"
    using invntt_signed_correct[OF bP k] unfolding cong_def sf_def z_def invf_val by simp
  \<comment> \<open>per position: 2^32 * P_m == sum_i u_i,m * v_i,m\<close>
  have pm: "[4294967296 * sf ?P m = (\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m)] (mod 8380417)"
    if m: "m < 256" for m
  proof -
    have "[sf ?P m = sf (acc u v) m] (mod 8380417)"
      using preduce_acc(1)[OF bu bv m] unfolding cong_def .
    hence "[4294967296 * sf ?P m = 4294967296 * sf (acc u v) m] (mod 8380417)"
      by (rule cong_scalar_left)
    also have "4294967296 * sf (acc u v) m = (\<Sum>i<4. 4294967296 * sf (pw u v i) m)"
      by (simp add: acc_exact[OF bu bv m] sum_distrib_left)
    also have "[\<dots> = (\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m)] (mod 8380417)"
      by (rule cong_sum) (rule pw_cong[OF bu bv m]; simp)+
    finally show ?thesis .
  qed
  have s1: "[4294967296 * (\<Sum>m<256. sf ?P m * z m) = S] (mod 8380417)"
  proof -
    have "4294967296 * (\<Sum>m<256. sf ?P m * z m) = (\<Sum>m<256. (4294967296 * sf ?P m) * z m)"
      by (simp add: sum_distrib_left mult.assoc)
    also have "[\<dots> = (\<Sum>m<256. (\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m) * z m)] (mod 8380417)"
      by (rule cong_sum) (rule cong_mult[OF pm cong_refl]; simp)
    also have "(\<Sum>m<256. (\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m) * z m) = S"
      unfolding S_def by (simp add: sum_distrib_right sum.swap[of _ "{..<4::nat}"])
    finally show ?thesis .
  qed
  \<comment> \<open>2^64 * (256 * C_k) == 256 * 41978 * (2^32 * sum P z) == 2^64 * S\<close>
  have "[18446744073709551616 * (256 * sf ?C k)
          = 256 * (4294967296 * (4294967296 * sf ?C k))] (mod 8380417)"
    by simp
  also have "[256 * (4294967296 * (4294967296 * sf ?C k))
               = 256 * (4294967296 * (41978 * (\<Sum>m<256. sf ?P m * z m)))] (mod 8380417)"
    by (intro cong_scalar_left iv)
  also have "256 * (4294967296 * (41978 * (\<Sum>m<256. sf ?P m * z m)))
               = (41978 * 256) * (4294967296 * (\<Sum>m<256. sf ?P m * z m))"
    by (simp only: mult_ac)
  also have "[(41978 * 256) * (4294967296 * (\<Sum>m<256. sf ?P m * z m))
               = 18446744073709551616 * S] (mod 8380417)"
    by (rule cong_mult[OF invf_256 s1])
  finally have big: "[18446744073709551616 * (256 * sf ?C k) = 18446744073709551616 * S] (mod 8380417)" .
  have "[256 * sf ?C k = (7593442 * 18446744073709551616) * (256 * sf ?C k)] (mod 8380417)"
    using cong_mult[OF cong_sym[OF inv_2_64] cong_refl, of "256 * sf ?C k"] by simp
  also have "(7593442 * 18446744073709551616) * (256 * sf ?C k)
               = 7593442 * (18446744073709551616 * (256 * sf ?C k))" by (simp only: mult.assoc)
  also have "[\<dots> = 7593442 * (18446744073709551616 * S)] (mod 8380417)"
    by (rule cong_scalar_left[OF big])
  also have "7593442 * (18446744073709551616 * S) = (7593442 * 18446744073709551616) * S"
    by (simp only: mult.assoc)
  also have "[\<dots> = S] (mod 8380417)"
    using cong_mult[OF inv_2_64 cong_refl, of S] by simp
  finally show ?thesis unfolding cong_def S_def z_def sf_def .
qed


subsection \<open>The row theorem, ring form\<close>

lemma inv_256: "[8347681 * 256 = (1::int)] (mod 8380417)"
  by (simp add: cong_def)

text \<open>If row \<open>i\<close> of the NTT-domain operand is the transform of an integer polynomial \<open>f i\<close>, and the
other operand is \<open>ntt\<close> of \<open>y_i\<close>, then each output coefficient is \<open>\<Sum>i<4. negconv (f i) y_i\<close> mod q.\<close>

theorem acc_mult_coeff:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and hv: "\<And>i. i < 4 \<Longrightarrow> nth_seq v i = ntt (nth_seq y i)"
    and by': "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 8380416 (nth_seq y i)"
    and tf: "\<And>i m. i < 4 \<Longrightarrow> m < 256 \<Longrightarrow>
               sf (nth_seq u i) m mod 8380417 = (\<Sum>j<256. f i j * 1753 ^ ((2 * brv 8 m + 1) * j)) mod 8380417"
    and k: "k < 256"
  shows "sint_seq (nth_seq (invntt (preduce (acc u v))) k) mod 8380417
       = (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k) mod 8380417"
proof -
  let ?C = "invntt (preduce (acc u v))"
  define F where "F i t = (\<Sum>j<256. f i j * 1753 ^ ((2 * t + 1) * j))" for i t
  define Y where "Y i t = (\<Sum>j<256. sf (nth_seq y i) j * 1753 ^ ((2 * t + 1) * j))" for i t
  define z where "z t = zpw (- (2 * int t + 1) * int k)" for t
  have bu9: "ntt_bounded 75423752 (nth_seq u i)" if "i < 4" for i
    by (rule bu[OF that])
  have bv9: "ntt_bounded 75423752 (nth_seq v i)" if "i < 4" for i
    using ntt_out_bounded[OF by'[OF that]] by (simp add: hv[OF that])
  have main: "[256 * sf ?C k = (\<Sum>i<4. \<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m * z (brv 8 m))]
                (mod 8380417)"
    using acc_mult_fips[OF bu9 bv9 k] unfolding cong_def z_def sf_def by simp
  have step: "[(\<Sum>i<4. \<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m * z (brv 8 m))
               = (\<Sum>i<4. \<Sum>m<256. F i (brv 8 m) * Y i (brv 8 m) * z (brv 8 m))] (mod 8380417)"
  proof (rule cong_sum, rule cong_sum)
    fix i m assume i: "i \<in> {..<4::nat}" and m: "m \<in> {..<256::nat}"
    hence i': "i < 4" and m': "m < 256" by auto
    have cu: "[sf (nth_seq u i) m = F i (brv 8 m)] (mod 8380417)"
      using tf[OF i' m'] unfolding cong_def F_def .
    have cv: "[sf (nth_seq v i) m = Y i (brv 8 m)] (mod 8380417)"
      using ntt_signed_correct[OF by'[OF i'] m'] unfolding cong_def Y_def sf_def by (simp add: hv[OF i'])
    show "[sf (nth_seq u i) m * sf (nth_seq v i) m * z (brv 8 m) = F i (brv 8 m) * Y i (brv 8 m) * z (brv 8 m)]
            (mod 8380417)"
      by (intro cong_mult cu cv cong_refl)
  qed
  have reidx: "(\<Sum>m<256. F i (brv 8 m) * Y i (brv 8 m) * z (brv 8 m)) = (\<Sum>t<256. F i t * Y i t * z t)" for i
  proof -
    have bij: "bij_betw (brv 8) {..<256} {..<256}"
      using brv_bij[of 8] by (simp add: atLeast0LessThan)
    show ?thesis by (rule sum.reindex_bij_betw[OF bij, where g = "\<lambda>t. F i t * Y i t * z t"])
  qed
  have cv: "[(\<Sum>i<4. \<Sum>t<256. F i t * Y i t * z t)
             = (\<Sum>i<4. 256 * negconv_int (f i) (sf (nth_seq y i)) k)] (mod 8380417)"
  proof (rule cong_sum)
    fix i
    show "[(\<Sum>t<256. F i t * Y i t * z t) = 256 * negconv_int (f i) (sf (nth_seq y i)) k] (mod 8380417)"
      using conv_int[OF k, of "f i" "sf (nth_seq y i)"] unfolding cong_def F_def Y_def z_def zpw_def by simp
  qed
  have big: "[256 * sf ?C k = 256 * (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k)] (mod 8380417)"
  proof -
    have "[256 * sf ?C k = (\<Sum>i<4. \<Sum>t<256. F i t * Y i t * z t)] (mod 8380417)"
      using cong_trans[OF main step] by (simp add: reidx)
    also have "[(\<Sum>i<4. \<Sum>t<256. F i t * Y i t * z t)
                 = (\<Sum>i<4. 256 * negconv_int (f i) (sf (nth_seq y i)) k)] (mod 8380417)" by (rule cv)
    finally show ?thesis by (simp add: sum_distrib_left)
  qed
  have "[sf ?C k = (8347681 * 256) * sf ?C k] (mod 8380417)"
    using cong_mult[OF cong_sym[OF inv_256] cong_refl, of "sf ?C k"] by simp
  also have "(8347681 * 256) * sf ?C k = 8347681 * (256 * sf ?C k)" by (simp only: mult.assoc)
  also have "[\<dots> = 8347681 * (256 * (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k))] (mod 8380417)"
    by (rule cong_scalar_left[OF big])
  also have "8347681 * (256 * (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k))
               = (8347681 * 256) * (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k)"
    by (simp only: mult.assoc)
  also have "[\<dots> = (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k)] (mod 8380417)"
    using cong_mult[OF inv_256 cong_refl, of "\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k"] by simp
  finally show ?thesis unfolding cong_def sf_def .
qed

text \<open>The row in \<open>R_q\<close>, universal form. For NTT-domain rows \<open>u\<close> within \<open>9q\<close> (\<open>poly_uniform\<close>
stores 23-bit values, so \<open>|A coeff| < 2^23 < 9q\<close>), every \<open>y\<close> with \<open>|coeff| < q\<close>, and EVERY choice of
integer polynomials \<open>f i\<close> whose transforms are the rows of \<open>u\<close> mod q, the C model's output is
\<open>\<Sum>i<4. f_i * y_i\<close> mod \<open>X^256 + 1\<close>. This is FIPS 204's \<open>NTT^-1(A_hat o NTT(y))\<close> for one row, read
as polynomials. \<open>acc_mult_ring_ex\<close> below shows such \<open>f\<close> always exist.\<close>

theorem acc_mult_ring:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and hv: "\<And>i. i < 4 \<Longrightarrow> nth_seq v i = ntt (nth_seq y i)"
    and by': "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 8380416 (nth_seq y i)"
    and tf: "\<And>i m. i < 4 \<Longrightarrow> m < 256 \<Longrightarrow>
               sf (nth_seq u i) m mod 8380417 = (\<Sum>j<256. f i j * 1753 ^ ((2 * brv 8 m + 1) * j)) mod 8380417"
  shows "Poly (map (\<lambda>k. of_int (sf (invntt (preduce (acc u v))) k) :: fin8380417 mod_ring) [0..<256])
       = (\<Sum>i<4. Poly (map (\<lambda>j. of_int (f i j)) [0..<256])
                 * Poly (map (\<lambda>j. of_int (sf (nth_seq y i) j)) [0..<256])) mod (monom 1 256 + 1)"
proof (rule negconv_sum_ring)
  fix k :: nat assume k: "k < 256"
  show "sf (invntt (preduce (acc u v))) k mod 8380417
          = (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k) mod 8380417"
    using acc_mult_coeff[OF bu hv by' tf k] by (simp only: sf_def)
qed

text \<open>Such \<open>f\<close> exist for every row (the transform is onto mod q, \<open>ntt_int_surj\<close>), so the hypothesis
\<open>tf\<close> of \<open>acc_mult_ring\<close> can always be met.\<close>

theorem acc_mult_ring_ex:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and hv: "\<And>i. i < 4 \<Longrightarrow> nth_seq v i = ntt (nth_seq y i)"
    and by': "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 8380416 (nth_seq y i)"
  shows "\<exists>f :: nat \<Rightarrow> nat \<Rightarrow> int.
           (\<forall>i<4. \<forall>m<256. sf (nth_seq u i) m mod 8380417
                             = (\<Sum>j<256. f i j * 1753 ^ ((2 * brv 8 m + 1) * j)) mod 8380417)
         \<and> Poly (map (\<lambda>k. of_int (sf (invntt (preduce (acc u v))) k) :: fin8380417 mod_ring) [0..<256])
           = (\<Sum>i<4. Poly (map (\<lambda>j. of_int (f i j)) [0..<256])
                     * Poly (map (\<lambda>j. of_int (sf (nth_seq y i) j)) [0..<256])) mod (monom 1 256 + 1)"
proof -
  have ex: "\<exists>fi. \<forall>t<256. (\<Sum>j<256. fi j * 1753 ^ ((2 * t + 1) * j)) mod 8380417
                             = sf (nth_seq u i) (brv 8 t) mod 8380417" for i
    by (rule ntt_int_surj)
  hence "\<forall>i. \<exists>fi. \<forall>t<256. (\<Sum>j<256. fi j * 1753 ^ ((2 * t + 1) * j)) mod 8380417
                             = sf (nth_seq u i) (brv 8 t) mod 8380417" by blast
  from choice[OF this] obtain f where fsp0: "\<forall>i. \<forall>t<256. (\<Sum>j<256. f i j * 1753 ^ ((2 * t + 1) * j)) mod 8380417
                             = sf (nth_seq u i) (brv 8 t) mod 8380417" by blast
  have fsp: "(\<Sum>j<256. f i j * 1753 ^ ((2 * t + 1) * j)) mod 8380417
               = sf (nth_seq u i) (brv 8 t) mod 8380417" if "t < 256" for i t
    using fsp0 that by blast
  have tf: "sf (nth_seq u i) m mod 8380417 = (\<Sum>j<256. f i j * 1753 ^ ((2 * brv 8 m + 1) * j)) mod 8380417"
    if "i < 4" "m < 256" for i m
  proof -
    have b: "brv 8 m < 256" using brv_lt[of 8 m] by simp
    have "brv 8 (brv 8 m) = m" using brv_brv[of m 8] that by simp
    thus ?thesis using fsp[OF b, of i] by simp
  qed
  have ring: "Poly (map (\<lambda>k. of_int (sf (invntt (preduce (acc u v))) k) :: fin8380417 mod_ring) [0..<256])
           = (\<Sum>i<4. Poly (map (\<lambda>j. of_int (f i j)) [0..<256])
                     * Poly (map (\<lambda>j. of_int (sf (nth_seq y i) j)) [0..<256])) mod (monom 1 256 + 1)"
  proof (rule negconv_sum_ring)
    fix k :: nat assume k: "k < 256"
    show "sf (invntt (preduce (acc u v))) k mod 8380417
            = (\<Sum>i<4. negconv_int (f i) (sf (nth_seq y i)) k) mod 8380417"
      using acc_mult_coeff[OF bu hv by' tf k] by (simp only: sf_def)
  qed
  show ?thesis using tf ring by blast
qed

end


subsection \<open>Oracle gate\<close>

text \<open>Checked by the kernel at build time, so the docs' oracle statements cannot drift. The headline
theorems depend on exactly one oracle, the code generator's \<open>holds_by_evaluation\<close>, inherited from
the twiddle-table facts behind the transform bridges, and on no proof hole. The ring-side and
accumulator lemmas depend on no oracle at all.\<close>

ML \<open>
  let
    fun names th = sort_strings (map (fn ((n, _), _) => n) (Thm_Deps.all_oracles [th]))
    fun no_skip nm th =
      if Thm_Deps.has_skip_proof [th] then error ("ORACLE GATE: " ^ nm ^ " depends on a proof hole") else ()
    fun exactly nm want th =
      (no_skip nm th;
       if names th = want then ()
       else error ("ORACLE GATE: " ^ nm ^ " depends on [" ^ commas (names th) ^ "], expected [" ^
                   commas want ^ "]"))
    val ev = ["Code_Generator.holds_by_evaluation"]
    val _ = exactly "acc_mult_ring" ev @{thm acc_mult_ring}
    val _ = exactly "acc_mult_fips" ev @{thm acc_mult_fips}
    val _ = exactly "ntt_mult_ring" ev @{thm ntt_mult_ring}
    val _ = exactly "ntt_mult_correct" ev @{thm ntt_mult_correct}
    val _ = exactly "acc_exact" [] @{thm acc_exact}
    val _ = exactly "ntt_int_surj" [] @{thm ntt_int_surj}
    val _ = exactly "negconv_sum_ring" [] @{thm negconv_sum_ring}
    val _ = exactly "negconv_int_ring" [] @{thm negconv_int_ring}
    val _ = exactly "conv_int" [] @{thm conv_int}
    val _ = exactly "negconv_is_mult" [] @{thm negacyclic_butterfly.negconv_is_mult}
  in () end
\<close>

end
