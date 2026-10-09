(* v4, verification: one row of w1 = NTT^-1(A_hat o NTT(z) - NTT(c) o NTT(t1 * 2^d)).

   FIPS 204 Alg 8 computes this; the reference does a row as
     polyvec_matrix_pointwise_montgomery   (acc: A_hat row times z_hat)
     polyveck_shiftl, polyveck_ntt          (t1 << 13, then its transform)
     polyveck_pointwise_poly_montgomery     (c_hat times that, output aliasing the vector operand)
     polyveck_sub                           (psub, output aliasing the first operand)
     polyveck_reduce, polyveck_invntt_tomont
   Each of those is SAW-proven equal to its model (proof/saw/mldsa_ntt.saw), including the aliasing
   forms. This theory is about the models.

   Bounds are derived: the accumulator is below 4q, the c*t1 product below q, so the difference is
   below 5q (no int32 wrap in poly_sub) and inside reduce32's precondition. t1's coefficients are
   10-bit, so t1 << 13 is at most 1023 * 8192 = q - 1: the shift does not overflow and its output is
   inside the forward transform's |coeff| < q window. *)
theory Ver_Bridge
  imports "Tier2_Acc.Acc_Bridge"
begin

context includes cryptol_translation_syntax begin

lemma nth_seq_psub:
  assumes k: "k < 256"
  shows "nth_seq (psub x y) k = nth_seq x k - nth_seq y k"
  using k by (simp add: psub_def)

lemma nth_seq_pshiftl:
  assumes k: "k < 256"
  shows "nth_seq (pshiftl x) k = (nth_seq x k) <<`{32,Integer,Bit} (13 :: Integer)"
  using k by (simp add: pshiftl_def)

lemma sint_shl13:
  fixes x :: "[32]"
  assumes lo: "0 \<le> sint_seq x" and hi: "sint_seq x \<le> 1023"
  shows "sint_seq (x <<`{32,Integer,Bit} (13 :: Integer)) = 8192 * sint_seq x"
proof -
  have w: "seq_to_word (x <<`{32,Integer,Bit} (13 :: Integer)) = seq_to_word x * 8192"
    by (simp add: word_seq_convs seq_to_word left_shift_def right_shift_def shiftl_def push_bit_eq_mult)
  have "sint (seq_to_word x * 8192) = sint (word_of_int (sint (seq_to_word x) * 8192) :: 32 word)"
    by (metis of_int_mult of_int_sint of_int_numeral)
  also have "\<dots> = sint (seq_to_word x) * 8192"
    by (rule sint_of_int_eq) (use lo hi in \<open>simp_all add: probe_sint_seq\<close>)
  finally have v: "sint (seq_to_word x * 8192) = sint (seq_to_word x) * 8192" .
  show ?thesis unfolding probe_sint_seq w v by simp
qed

end

context includes cryptol_syntax begin

declare [[coercion_enabled = false]]

text \<open>The shared tail: reduce32 on every coefficient, then the inverse transform. If each coefficient
of \<open>X\<close> is a valid reduce32 input and \<open>2^32 X_m == E m\<close>, then 256 times the output is the unnormalised
FIPS inverse transform of \<open>E\<close>, mod q.\<close>

lemma preduce_bounded:
  assumes ok: "\<And>m. m < 256 \<Longrightarrow> reduce32_input_ok (sf X m)"
  shows "ntt_bounded 8380416 (preduce X)"
  unfolding ntt_bounded_def
proof (intro allI)
  fix n
  have out: "- 8380416 \<le> sint_seq (nth_seq (preduce X) m) \<and> sint_seq (nth_seq (preduce X) m) \<le> 8380416"
    if m: "m < 256" for m
  proof -
    have "is_reduce32 (sint_seq (nth_seq X m)) (sint_seq (reduce32 (nth_seq X m)))"
      using reduce32_correct ok[OF m] unfolding sf_def by blast
    thus ?thesis unfolding is_reduce32_def by (simp add: nth_seq_preduce[OF m])
  qed
  show "- 8380416 \<le> sint_seq (nth_seq (preduce X) n) \<and> sint_seq (nth_seq (preduce X) n) \<le> 8380416"
  proof (cases "n < 256")
    case True thus ?thesis using out by blast
  next
    case False hence ge: "256 \<le> n" by simp
    show ?thesis using out[of 255] oob255[OF ge, of "preduce X"] by simp
  qed
qed

lemma invntt_preduce_cong:
  assumes ok: "\<And>m. m < 256 \<Longrightarrow> reduce32_input_ok (sf X m)"
    and e: "\<And>m. m < 256 \<Longrightarrow> [4294967296 * sf X m = E m] (mod 8380417)"
    and k: "k < 256"
  shows "[256 * sf (invntt (preduce X)) k
          = (\<Sum>m<256. E m * zpw (- (2 * int (brv 8 m) + 1) * int k))] (mod 8380417)"
proof -
  let ?P = "preduce X"
  let ?C = "invntt ?P"
  define z where "z m = zpw (- (2 * int (brv 8 m) + 1) * int k)" for m
  define S where "S = (\<Sum>m<256. E m * z m)"
  have bP: "ntt_bounded 8380416 ?P" by (rule preduce_bounded[OF ok])
  have iv: "[4294967296 * sf ?C k = 41978 * (\<Sum>m<256. sf ?P m * z m)] (mod 8380417)"
    using invntt_signed_correct[OF bP k] unfolding cong_def sf_def z_def invf_val by simp
  have pm: "[4294967296 * sf ?P m = E m] (mod 8380417)" if m: "m < 256" for m
  proof -
    have "is_reduce32 (sint_seq (nth_seq X m)) (sint_seq (reduce32 (nth_seq X m)))"
      using reduce32_correct ok[OF m] unfolding sf_def by blast
    hence "[sf ?P m = sf X m] (mod 8380417)"
      unfolding is_reduce32_def MLDSA_NTT_Spec.q_def cong_def sf_def by (simp add: nth_seq_preduce[OF m])
    hence "[4294967296 * sf ?P m = 4294967296 * sf X m] (mod 8380417)" by (rule cong_scalar_left)
    thus ?thesis using e[OF m] by (rule cong_trans)
  qed
  have s1: "[4294967296 * (\<Sum>m<256. sf ?P m * z m) = S] (mod 8380417)"
  proof -
    have "4294967296 * (\<Sum>m<256. sf ?P m * z m) = (\<Sum>m<256. (4294967296 * sf ?P m) * z m)"
      by (simp add: sum_distrib_left mult.assoc)
    also have "[\<dots> = (\<Sum>m<256. E m * z m)] (mod 8380417)"
      by (rule cong_sum) (rule cong_mult[OF pm cong_refl]; simp)
    finally show ?thesis unfolding S_def .
  qed
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
  also have "[7593442 * (18446744073709551616 * (256 * sf ?C k))
               = 7593442 * (18446744073709551616 * S)] (mod 8380417)"
    by (rule cong_scalar_left[OF big])
  also have "7593442 * (18446744073709551616 * S) = (7593442 * 18446744073709551616) * S"
    by (simp only: mult.assoc)
  also have "[(7593442 * 18446744073709551616) * S = S] (mod 8380417)"
    using cong_mult[OF inv_2_64 cong_refl, of S] by simp
  finally show ?thesis unfolding S_def z_def .
qed

subsection \<open>The verification row, FIPS form\<close>

theorem ver_row_fips:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and bv: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq v i)"
    and bc: "ntt_bounded 75423752 ch" and bt: "ntt_bounded 75423752 th"
    and k: "k < 256"
  shows "[256 * sf (invntt (preduce (psub (acc u v) (pointwise ch th)))) k
          = (\<Sum>m<256. ((\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m) - sf ch m * sf th m)
                      * zpw (- (2 * int (brv 8 m) + 1) * int k))] (mod 8380417)"
proof (rule invntt_preduce_cong)
  fix m :: nat assume m: "m < 256"
  have aw: "\<bar>sf (acc u v) m\<bar> \<le> 33521664" by (rule acc_bound[OF bu bv m])
  have pv: "- 8380417 < sf (pointwise ch th) m \<and> sf (pointwise ch th) m < 8380417"
    using mont_butterfly_bound[OF pointwise_ok[OF bc bt, of m]]
    by (simp add: nth_seq_pointwise[OF m] sf_def)
  have d: "sf (psub (acc u v) (pointwise ch th)) m = sf (acc u v) m - sf (pointwise ch th) m"
    unfolding sf_def nth_seq_psub[OF m]
    by (rule sint_seq_sub_eq) (use aw pv in \<open>simp_all add: sf_def abs_le_iff\<close>)
  show "reduce32_input_ok (sf (psub (acc u v) (pointwise ch th)) m)"
    unfolding reduce32_input_ok_def d using aw pv by (simp add: abs_le_iff)
  have cw: "[4294967296 * sf (acc u v) m = (\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m)] (mod 8380417)"
  proof -
    have "4294967296 * sf (acc u v) m = (\<Sum>i<4. 4294967296 * sf (pw u v i) m)"
      by (simp add: acc_exact[OF bu bv m] sum_distrib_left)
    also have "[\<dots> = (\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m)] (mod 8380417)"
      by (rule cong_sum) (rule pw_cong[OF bu bv m]; simp)+
    finally show ?thesis .
  qed
  have cp: "[4294967296 * sf (pointwise ch th) m = sf ch m * sf th m] (mod 8380417)"
    using pointwise_bridge[OF m pointwise_ok[OF bc bt]] unfolding cong_def sf_def by simp
  show "[4294967296 * sf (psub (acc u v) (pointwise ch th)) m
         = (\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m) - sf ch m * sf th m] (mod 8380417)"
    unfolding d right_diff_distrib by (rule cong_diff[OF cw cp])
qed (rule k)


subsection \<open>The verification row, ring form\<close>

text \<open>One product term: if \<open>x\<close> is the transform of \<open>f\<close> (mod q, position \<open>m\<close> at frequency
\<open>brv 8 m\<close>) and the other operand is \<open>ntt g\<close>, its contribution is \<open>256 * negconv f g\<close>.\<close>

lemma row_term:
  assumes tfx: "\<And>m. m < 256 \<Longrightarrow>
                 sf x m mod 8380417 = (\<Sum>j<256. f j * 1753 ^ ((2 * brv 8 m + 1) * j)) mod 8380417"
    and bg: "ntt_bounded 8380416 g" and k: "k < 256"
  shows "[(\<Sum>m<256. sf x m * sf (ntt g) m * zpw (- (2 * int (brv 8 m) + 1) * int k))
          = 256 * negconv_int f (sf g) k] (mod 8380417)"
proof -
  define F where "F t = (\<Sum>j<256. f j * 1753 ^ ((2 * t + 1) * j))" for t
  define G where "G t = (\<Sum>j<256. sf g j * 1753 ^ ((2 * t + 1) * j))" for t
  define z where "z t = zpw (- (2 * int t + 1) * int k)" for t
  have "[(\<Sum>m<256. sf x m * sf (ntt g) m * z (brv 8 m))
         = (\<Sum>m<256. F (brv 8 m) * G (brv 8 m) * z (brv 8 m))] (mod 8380417)"
  proof (rule cong_sum)
    fix m assume "m \<in> {..<256::nat}" hence m: "m < 256" by simp
    have cx: "[sf x m = F (brv 8 m)] (mod 8380417)" using tfx[OF m] unfolding cong_def F_def .
    have cg: "[sf (ntt g) m = G (brv 8 m)] (mod 8380417)"
      using ntt_signed_correct[OF bg m] unfolding cong_def G_def sf_def .
    show "[sf x m * sf (ntt g) m * z (brv 8 m) = F (brv 8 m) * G (brv 8 m) * z (brv 8 m)] (mod 8380417)"
      by (intro cong_mult cx cg cong_refl)
  qed
  also have "(\<Sum>m<256. F (brv 8 m) * G (brv 8 m) * z (brv 8 m)) = (\<Sum>t<256. F t * G t * z t)"
  proof -
    have bij: "bij_betw (brv 8) {..<256} {..<256}" using brv_bij[of 8] by (simp add: atLeast0LessThan)
    show ?thesis by (rule sum.reindex_bij_betw[OF bij, where g = "\<lambda>t. F t * G t * z t"])
  qed
  also have "[(\<Sum>t<256. F t * G t * z t) = 256 * negconv_int f (sf g) k] (mod 8380417)"
    using conv_int[OF k, of f "sf g"] unfolding cong_def F_def G_def z_def zpw_def by simp
  finally show ?thesis unfolding z_def .
qed

lemma pshiftl_val:
  assumes t: "\<And>n. 0 \<le> sint_seq (nth_seq t1 n) \<and> sint_seq (nth_seq t1 n) \<le> 1023" and j: "j < 256"
  shows "sf (pshiftl t1) j = 8192 * sf t1 j"
  using sint_shl13[of "nth_seq t1 j"] t[of j] unfolding sf_def by (simp add: nth_seq_pshiftl[OF j])

lemma pshiftl_bounded:
  assumes t: "\<And>n. 0 \<le> sint_seq (nth_seq t1 n) \<and> sint_seq (nth_seq t1 n) \<le> 1023"
  shows "ntt_bounded 8380416 (pshiftl t1)"
  unfolding ntt_bounded_def
proof (intro allI)
  fix n
  have out: "- 8380416 \<le> sint_seq (nth_seq (pshiftl t1) j) \<and> sint_seq (nth_seq (pshiftl t1) j) \<le> 8380416"
    if j: "j < 256" for j
    using pshiftl_val[OF t j] t[of j] unfolding sf_def by simp
  show "- 8380416 \<le> sint_seq (nth_seq (pshiftl t1) n) \<and> sint_seq (nth_seq (pshiftl t1) n) \<le> 8380416"
  proof (cases "n < 256")
    case True thus ?thesis using out by blast
  next
    case False hence ge: "256 \<le> n" by simp
    show ?thesis using out[of 255] oob255[OF ge, of "pshiftl t1"] by simp
  qed
qed

lemma sum_lt5: "(\<Sum>i<(5::nat). H i) = (\<Sum>i<4. H i) + (H 4 :: 'a :: comm_monoid_add)"
proof -
  have "{..<(5::nat)} = insert 4 {..<4}" by auto
  thus ?thesis by (simp add: add.commute)
qed

lemma negconv_int_neg: "negconv_int (\<lambda>j. - f j) g k = - negconv_int f g k"
  unfolding negconv_int_def by (simp add: sum_negf[symmetric] if_distrib cong: if_cong)

lemma negconv_int_cong_right:
  assumes "\<And>j. j < 256 \<Longrightarrow> g j = h j" and k: "k < 256"
  shows "negconv_int f g k = negconv_int f h k"
  unfolding negconv_int_def using assms by (intro sum.cong) auto

lemma Poly_of_int_neg:
  "Poly (map (\<lambda>j. - (of_int (h j))) [0..<n]) = - Poly (map (\<lambda>j. of_int (h j) :: 'a :: comm_ring_1) [0..<n])"
  by (rule poly_eqI) (simp add: coeff_Poly nth_default_def)

text \<open>The row in \<open>R_q\<close>: for every choice of polynomials \<open>f i\<close> whose transforms are the rows of
\<open>u\<close>, with \<open>v_i = ntt z_i\<close>, \<open>ch = ntt c\<close> and \<open>th = ntt (t1 << 13)\<close>, the output is
\<open>\<Sum>i<4. f_i * z_i - c * (2^13 t1)\<close> mod \<open>X^256 + 1\<close>.\<close>

theorem ver_row_ring:
  assumes bu: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 75423752 (nth_seq u i)"
    and hv: "\<And>i. i < 4 \<Longrightarrow> nth_seq v i = ntt (nth_seq z i)"
    and bz: "\<And>i. i < 4 \<Longrightarrow> ntt_bounded 8380416 (nth_seq z i)"
    and hc: "ch = ntt c" and bc: "ntt_bounded 8380416 c"
    and ht: "th = ntt (pshiftl t1)"
    and bt1: "\<And>n. 0 \<le> sint_seq (nth_seq t1 n) \<and> sint_seq (nth_seq t1 n) \<le> 1023"
    and tf: "\<And>i m. i < 4 \<Longrightarrow> m < 256 \<Longrightarrow>
               sf (nth_seq u i) m mod 8380417 = (\<Sum>j<256. f i j * 1753 ^ ((2 * brv 8 m + 1) * j)) mod 8380417"
  shows "Poly (map (\<lambda>k. of_int (sf (invntt (preduce (psub (acc u v) (pointwise ch th)))) k)
                         :: fin8380417 mod_ring) [0..<256])
       = ((\<Sum>i<4. Poly (map (\<lambda>j. of_int (f i j)) [0..<256])
                  * Poly (map (\<lambda>j. of_int (sf (nth_seq z i) j)) [0..<256]))
          - Poly (map (\<lambda>j. of_int (sf c j)) [0..<256])
            * Poly (map (\<lambda>j. of_int (8192 * sf t1 j)) [0..<256])) mod (monom 1 256 + 1)"
proof -
  let ?OUT = "invntt (preduce (psub (acc u v) (pointwise ch th)))"
  let ?sh = "pshiftl t1"
  define z' where "z' m k = zpw (- (2 * int (brv 8 m) + 1) * int k)" for m k
  have bsh: "ntt_bounded 8380416 ?sh" by (rule pshiftl_bounded[OF bt1])
  have bv9: "ntt_bounded 75423752 (nth_seq v i)" if "i < 4" for i
    using ntt_out_bounded[OF bz[OF that]] by (simp add: hv[OF that])
  have bc9: "ntt_bounded 75423752 ch" using ntt_out_bounded[OF bc] by (simp add: hc)
  have bt9: "ntt_bounded 75423752 th" using ntt_out_bounded[OF bsh] by (simp add: ht)
  define N where "N k = (\<Sum>i<4. negconv_int (f i) (sf (nth_seq z i)) k) - negconv_int (sf c) (sf ?sh) k" for k
  have coeff: "sf ?OUT k mod 8380417 = N k mod 8380417" if k: "k < 256" for k
  proof -
    have main: "[256 * sf ?OUT k
                 = (\<Sum>m<256. ((\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m) - sf ch m * sf th m) * z' m k)]
                 (mod 8380417)"
      using ver_row_fips[OF bu bv9 bc9 bt9 k] unfolding z'_def .
    have split: "(\<Sum>m<256. ((\<Sum>i<4. sf (nth_seq u i) m * sf (nth_seq v i) m) - sf ch m * sf th m) * z' m k)
                 = (\<Sum>i<4. \<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m * z' m k)
                   - (\<Sum>m<256. sf ch m * sf th m * z' m k)"
      by (simp add: left_diff_distrib sum_subtractf sum_distrib_right sum.swap[of _ "{..<4::nat}"])
    have ti: "[(\<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m * z' m k)
               = 256 * negconv_int (f i) (sf (nth_seq z i)) k] (mod 8380417)" if i: "i < 4" for i
      using row_term[OF tf[OF i] bz[OF i] k] unfolding z'_def by (simp add: hv[OF i])
    have tc: "[(\<Sum>m<256. sf ch m * sf th m * z' m k) = 256 * negconv_int (sf c) (sf ?sh) k] (mod 8380417)"
    proof -
      have tfc: "sf (ntt c) m mod 8380417 = (\<Sum>j<256. sf c j * 1753 ^ ((2 * brv 8 m + 1) * j)) mod 8380417"
        if m: "m < 256" for m
        using ntt_signed_correct[OF bc m] unfolding sf_def .
      show ?thesis using row_term[OF tfc bsh k] unfolding z'_def by (simp add: hc ht)
    qed
    have "[256 * sf ?OUT k = 256 * N k] (mod 8380417)"
    proof -
      have "[(\<Sum>i<4. \<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m * z' m k)
             = (\<Sum>i<4. 256 * negconv_int (f i) (sf (nth_seq z i)) k)] (mod 8380417)"
        by (rule cong_sum) (rule ti; simp)
      hence "[(\<Sum>i<4. \<Sum>m<256. sf (nth_seq u i) m * sf (nth_seq v i) m * z' m k)
               - (\<Sum>m<256. sf ch m * sf th m * z' m k)
             = (\<Sum>i<4. 256 * negconv_int (f i) (sf (nth_seq z i)) k)
               - 256 * negconv_int (sf c) (sf ?sh) k] (mod 8380417)"
        by (rule cong_diff[OF _ tc])
      thus ?thesis using cong_trans[OF main[unfolded split]]
        by (simp add: N_def right_diff_distrib sum_distrib_left)
    qed
    hence "[(8347681 * 256) * sf ?OUT k = (8347681 * 256) * N k] (mod 8380417)"
      by (metis cong_scalar_left mult.assoc)
    moreover have "[(8347681 * 256) * sf ?OUT k = sf ?OUT k] (mod 8380417)"
      using cong_mult[OF inv_256 cong_refl, of "sf ?OUT k"] by simp
    moreover have "[(8347681 * 256) * N k = N k] (mod 8380417)"
      using cong_mult[OF inv_256 cong_refl, of "N k"] by simp
    ultimately have "[sf ?OUT k = N k] (mod 8380417)"
      by (meson cong_sym cong_trans)
    thus ?thesis unfolding cong_def .
  qed
  define F where "F i = (if i < 4 then f i else (\<lambda>j. - sf c j))" for i
  define G where "G i = (if i < 4 then sf (nth_seq z i) else (\<lambda>j. 8192 * sf t1 j))" for i
  have NF: "N k = (\<Sum>i<5. negconv_int (F i) (G i) k)" if k: "k < 256" for k
  proof -
    have "negconv_int (sf c) (sf ?sh) k = negconv_int (sf c) (\<lambda>j. 8192 * sf t1 j) k"
      by (rule negconv_int_cong_right[OF _ k]) (rule pshiftl_val[OF bt1])
    moreover have "(\<Sum>i<4. negconv_int (F i) (G i) k) = (\<Sum>i<4. negconv_int (f i) (sf (nth_seq z i)) k)"
      by (rule sum.cong) (simp_all add: F_def G_def)
    ultimately show ?thesis
      by (simp add: N_def sum_lt5 F_def G_def negconv_int_neg)
  qed
  have ring: "Poly (map (\<lambda>k. of_int (sf ?OUT k) :: fin8380417 mod_ring) [0..<256])
          = (\<Sum>i<5. Poly (map (\<lambda>j. of_int (F i j)) [0..<256])
                    * Poly (map (\<lambda>j. of_int (G i j)) [0..<256])) mod (monom 1 256 + 1)"
    by (rule negconv_sum_ring) (simp add: coeff NF[symmetric])
  have "(\<Sum>i<5. Poly (map (\<lambda>j. of_int (F i j) :: fin8380417 mod_ring) [0..<256])
                * Poly (map (\<lambda>j. of_int (G i j)) [0..<256]))
        = (\<Sum>i<4. Poly (map (\<lambda>j. of_int (f i j)) [0..<256])
                  * Poly (map (\<lambda>j. of_int (sf (nth_seq z i) j)) [0..<256]))
          - Poly (map (\<lambda>j. of_int (sf c j)) [0..<256])
            * Poly (map (\<lambda>j. of_int (8192 * sf t1 j)) [0..<256])"
  proof -
    have "(\<Sum>i<4. Poly (map (\<lambda>j. of_int (F i j) :: fin8380417 mod_ring) [0..<256])
                  * Poly (map (\<lambda>j. of_int (G i j)) [0..<256]))
          = (\<Sum>i<4. Poly (map (\<lambda>j. of_int (f i j)) [0..<256])
                  * Poly (map (\<lambda>j. of_int (sf (nth_seq z i) j)) [0..<256]))"
      by (rule sum.cong) (simp_all add: F_def G_def)
    thus ?thesis by (simp add: sum_lt5 F_def G_def Poly_of_int_neg)
  qed
  with ring show ?thesis by simp
qed

end


subsection \<open>Oracle gate\<close>

text \<open>As in \<open>Acc_Bridge\<close>: the build fails unless the verification theorems depend on exactly the
code generator's \<open>holds_by_evaluation\<close> (from the twiddle tables, through the transform bridges) and
on no proof hole, and the new arithmetic lemmas on no oracle.\<close>

ML \<open>
  let
    fun names th = sort_strings (map (fn ((n, _), _) => n) (Thm_Deps.all_oracles [th]))
    fun exactly nm want th =
      (if Thm_Deps.has_skip_proof [th] then error ("ORACLE GATE: " ^ nm ^ " depends on a proof hole") else ();
       if names th = want then ()
       else error ("ORACLE GATE: " ^ nm ^ " depends on [" ^ commas (names th) ^ "], expected [" ^
                   commas want ^ "]"))
    val ev = ["Code_Generator.holds_by_evaluation"]
    val _ = exactly "ver_row_ring" ev @{thm ver_row_ring}
    val _ = exactly "ver_row_fips" ev @{thm ver_row_fips}
    val _ = exactly "invntt_preduce_cong" ev @{thm invntt_preduce_cong}
    val _ = exactly "sint_shl13" [] @{thm sint_shl13}
    val _ = exactly "negconv_int_neg" [] @{thm negconv_int_neg}
    val _ = exactly "Poly_of_int_neg" [] @{thm Poly_of_int_neg}
  in () end
\<close>

end
