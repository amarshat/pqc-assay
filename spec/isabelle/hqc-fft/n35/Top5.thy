theory Top5
  imports Btfy35 Ibc35 Enc35 "HQC_FFT.Assemble" HQC.FFTTop5 HQC.AVX_Toom
begin

text \<open>The hqc-5 model (polymul_input_transform / polymul_output at 1024 words, FFTTop5.cry) multiplies:
  mulT5 (inputT5 a) (inputT5 b) is the 2048-word product of the 1024-word operands a and b. The
  hypotheses are the model lemmas encode5 == encodeIdx5 and decode5 == decodeIdx5 that
  make hqc-fft-lemmas proves with abc. The steps are those of the hqc-1 proof (Forward, Backward)
  at the sizes 65536 / 131072 bits, 2048 points, coset base 2^43.\<close>

lemma s2w_sc43: "seq_to_word (left_shift (1 :: w64) 43) = 2 ^ 43"
  by (simp add: seq_to_word.left_shift word_seq_convs shiftl_def push_bit_eq_mult)

lemma bnd_Pl: "bnd (64 * length ws) (Pl ws)"
  by (simp add: bnd_def coeff_Pl_ge)

lemma pw_sum_monom16: "pw (seq_to_word (C :: (65536, bool) seq)) = (\<Sum>d<2 ^ 16. monom (of_bool (bit (seq_to_word C) d)) d)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_sum sum.delta bit_s2w)

lemma pw_sum_monom17: "pw (seq_to_word (C :: (131072, bool) seq)) = (\<Sum>d<2 ^ 17. monom (of_bool (bit (seq_to_word C) d)) d)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_sum sum.delta bit_s2w)

lemma bc1_65536wc_bits:
  fixes v :: "(2048, (32, bool) seq) seq"
  shows "FFTBC.flat32 TY(2048) (FFTBC.bc1_65536wc v)
       = coerce_seq_len (FFTBC.bc1of256 TY(256) (coerce_seq_len (FFTBC.bc256of65536 (FFTBC.repr65536 (coerce_seq_len (FFTBC.flat32 TY(2048) v))))))"
  by (simp add: FFTBC.bc1_65536wc_def FFTBC.bc1of256of64W_def FFTBC.bc256of64W_def FFTBC.repr64W_def flat32_unflat32)

lemma ibc1_131072w_bits:
  fixes v :: "(4096, (32, bool) seq) seq"
  shows "FFTBC.flat32 TY(4096) (FFTBC.ibc1_131072w v)
       = coerce_seq_len (FFTBC.irepr131072 (coerce_seq_len (FFTBC.ibc1of256 TY(512) (coerce_seq_len (FFTBC.icvt131072 (coerce_seq_len (FFTBC.flat32 TY(4096) v)))))))"
  by (simp add: FFTBC.ibc1_131072w_def FFTBC.irepr128W_def FFTBC.ibc1of256of128W_def FFTBC.icvt128W_def flat32_unflat32)

theorem forward_coords5:
  fixes a :: "(1024, w64) seq"
  defines "x \<equiv> (coerce_seq_len (FFTTop.as32 TY(1024) a) :: (2048, (32, bool) seq) seq)"
  defines "C \<equiv> FFTBC.bc1_65536 (coerce_seq_len (FFTBC.flat32 TY(2048) x))"
  shows "Pl (L a) = (\<Sum>d<2 ^ 16. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
proof -
  have "pw (seq_to_word (FFTBC.ibc1_65536 C)) = iconv T16 1 (pw (seq_to_word C))" by (rule ibc1_65536_iconv)
  also have "\<dots> = iconv T16 1 (\<Sum>d<2 ^ sz T16. monom (of_bool (bit (seq_to_word C) d)) d)"
    by (simp add: pw_sum_monom16 T16_sz)
  also have "\<dots> = (\<Sum>d<2 ^ sz T16. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
    by (rule iconv_novel[OF T16_wf])
  finally have i: "pw (seq_to_word (FFTBC.ibc1_65536 C)) = (\<Sum>d<2 ^ 16. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
    by (simp add: T16_sz)
  have "pw (seq_to_word (FFTBC.ibc1_65536 C)) = pw (seq_to_word (FFTBC.flat32 TY(2048) x))"
    by (simp add: C_def ibc_bc_65536 pw_coerce)
  also have "\<dots> = PL (concat (map seq_to_list (rev (seq_to_list a))))"
  proof -
    have "seq_to_list (FFTBC.flat32 TY(2048) x) = seq_to_list (FFTBC.flat32 TY(2 \<times> 1024) (FFTTop.as32 TY(1024) a))"
      by (simp add: flat32_list x_def stl_coerce)
    then show ?thesis by (simp add: pw_PL flat32_as32)
  qed
  also have "\<dots> = Pl (L a)" by (simp add: L_def Pl_PL)
  finally show ?thesis using i by simp
qed

theorem forward_eval5:
  fixes a :: "(1024, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode5 fx = FFTEnc.encodeIdx5 fx" and u: "u < 2048"
  shows "FV (FFTTop5.inputT5 a) u = poly (map_poly emb (Pl (L a))) (Cantor.cantor beta (2 ^ 43 + u))"
proof -
  define x where "x = (coerce_seq_len (FFTTop.as32 TY(1024) a) :: (2048, (32, bool) seq) seq)"
  define C where "C = FFTBC.bc1_65536 (coerce_seq_len (FFTBC.flat32 TY(2048) x))"
  define fx where "fx = FFTTop.as64 TY(1024) (coerce_seq_len (FFTBC.bc1_65536wc x))"
  define c where "c = (\<lambda>d. bit (seq_to_word C) d)"
  define om where "om = Cantor.cantor beta (2 ^ 43 + u)"
  have inp: "FFTTop5.inputT5 a = FFTRef.btfy11 (left_shift 1 43) (FFTEnc.encodeIdx5 fx)"
    by (simp add: FFTTop5.inputT5_def enc fx_def x_def)
  have bits: "bit (seq_to_word (FFTEnc.flat5 fx)) d = c d" for d
  proof -
    have b1: "seq_to_list (FFTBC.flat32 TY(2048) (FFTBC.bc1_65536wc x)) = seq_to_list C"
      by (simp add: bc1_65536wc_bits stl_coerce C_def FFTBC.bc1_65536_def)
    have "seq_to_list (FFTEnc.flat5 fx) = seq_to_list (FFTBC.flat32 TY(2048) (FFTBC.bc1_65536wc x))"
      by (simp add: fx_def flat5_as64 flat32_list stl_coerce)
    then have "seq_to_list (FFTEnc.flat5 fx) = seq_to_list C" using b1 by simp
    then show ?thesis unfolding c_def by (rule bit_eq_list)
  qed
  define f where "f = (\<lambda>e. \<Sum>j<32. if c (2048 * j + e) then X j (beta 32) else 0)"
  have ef: "EqOn 2048 (FV (FFTEnc.encodeIdx5 fx)) f"
    unfolding EqOn_def by (auto simp: FV_nth encodeIdx5_gf bits f_def)
  have "FV (FFTTop5.inputT5 a) u = chain beta (2 ^ 43) 11 f u"
    using btfy11_chain[OF s2w_sc43 ef] u by (simp add: inp EqOn_def)
  also have "\<dots> = fft beta 11 (2 ^ 43) f u" by (rule net_fft) (simp_all add: u)
  also have "\<dots> = evalN 11 f om" unfolding om_def by (rule fft_eval[OF cb64]) (simp_all add: u)
  also have "\<dots> = (\<Sum>d<2 ^ 11 * 32. (if c d then 1 else 0) * X d om)"
  proof -
    have "evalN 11 (\<lambda>a. \<Sum>b<32. (if c (a + 2 ^ 11 * b) then 1 else 0) * X b (Cantor.cantor beta (2 ^ 43 div 2 ^ 11))) om
        = (\<Sum>d<2 ^ 11 * 32. (if c d then 1 else 0) * X d om)"
      unfolding om_def by (rule eval_partial[OF cb64, symmetric]) (simp_all add: u)
    moreover have "Cantor.cantor beta (2 ^ 43 div 2 ^ 11) = beta 32" using beta32 by simp
    moreover have "(\<lambda>a. \<Sum>b<32. (if c (a + 2 ^ 11 * b) then 1 else 0) * X b (beta 32)) = f"
      by (rule ext) (simp add: f_def add.commute if_one_mult)
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = poly (map_poly emb (Pl (L a))) om"
  proof -
    have "Pl (L a) = (\<Sum>d<2 ^ 16. smult (of_bool (c d)) (XP d))"
      unfolding c_def C_def x_def by (rule forward_coords5)
    then have "poly (map_poly emb (Pl (L a))) om = (\<Sum>d<2 ^ 16. emb (of_bool (c d)) * X d om)"
      by (rule eval_novel_emb)
    then show ?thesis by (simp add: emb_of_bool)
  qed
  finally show ?thesis by (simp add: om_def)
qed

lemma gf264v_FV_gen:
  fixes x y :: "('n::len, w64) seq"
  assumes i: "i < LENGTH('n)"
  shows "FV (FFTRef.gf264v TY('n) x y) i = FV x i * FV y i"
proof -
  have "seq_to_list (FFTRef.gf264v TY('n) x y) = map (\<lambda>(p, q). FFTRef.gf264 p q) (zip (seq_to_list x) (seq_to_list y))"
    by (simp add: FFTRef.gf264v_def seq_to_list split_def comp_def)
  then show ?thesis using i by (simp add: FV_def gv_def gf264_gf)
qed

theorem ibtfy_words5:
  fixes a b :: "(1024, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode5 fx = FFTEnc.encodeIdx5 fx"
  defines "P \<equiv> Pl (L a) * Pl (L b)"
  defines "pv \<equiv> word_to_seq (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<131072])) :: 131072 word)"
  defines "n \<equiv> FFTBC.bc1_131072 pv"
  assumes e: "e < 2048"
  shows "seq_to_word (nth_seq (FFTRef.ibtfy11 (left_shift 1 43) (FFTRef.gf264v TY(2048) (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))) e)
       = encword (\<lambda>j. bit (seq_to_word n) (e + 2048 * j))"
proof -
  have bA: "bnd 65536 (Pl (L a))" and bB: "bnd 65536 (Pl (L b))"
    using bnd_Pl[of "L a"] bnd_Pl[of "L b"] by (simp_all add: L_def)
  have bP: "bnd 131072 P" unfolding P_def by (rule bnd_mult[OF bA bB]) simp
  have pvP: "pw (seq_to_word pv) = P" unfolding pv_def using bit_poly_word[where 'n=131072, of P] bP by simp
  have coords: "P = (\<Sum>d<2 ^ 17. smult (of_bool (bit (seq_to_word n) d)) (XP d))"
  proof -
    have "P = pw (seq_to_word (FFTBC.ibc1_131072 n))" by (simp add: n_def ibc_bc_131072 pvP)
    also have "\<dots> = iconv T17 1 (pw (seq_to_word n))" by (rule ibc1_131072_iconv)
    also have "\<dots> = iconv T17 1 (\<Sum>d<2 ^ sz T17. monom (of_bool (bit (seq_to_word n) d)) d)"
      by (simp only: pw_sum_monom17 T17_sz)
    also have "\<dots> = (\<Sum>d<2 ^ sz T17. smult (of_bool (bit (seq_to_word n) d)) (XP d))"
      by (rule iconv_novel[OF T17_wf])
    finally show ?thesis by (simp add: T17_sz)
  qed
  define g where "g = (\<lambda>a'. gfw (encword (\<lambda>j. bit (seq_to_word n) (a' + 2048 * j))))"
  have gform: "g = (\<lambda>a'. \<Sum>b'<64. (if bit (seq_to_word n) (a' + 2 ^ 11 * b') then 1 else 0) * X b' (Cantor.cantor beta (2 ^ 43 div 2 ^ 11)))"
    using beta32 by (simp add: g_def gfw_encword if_one_mult fun_eq_iff)
  have prod: "EqOn 2048 (FV (FFTRef.gf264v TY(2048) (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))) (chain beta (2 ^ 43) 11 g)"
    unfolding EqOn_def
  proof (intro allI impI)
    fix u :: nat assume u: "u < 2048"
    define om where "om = Cantor.cantor beta (2 ^ 43 + u)"
    have "chain beta (2 ^ 43) 11 g u = fft beta 11 (2 ^ 43) g u" by (rule net_fft) (simp_all add: u)
    also have "\<dots> = evalN 11 g om" unfolding om_def by (rule fft_eval[OF cb64]) (simp_all add: u)
    also have "\<dots> = (\<Sum>d<2 ^ 11 * 64. (if bit (seq_to_word n) d then 1 else 0) * X d om)"
      unfolding gform om_def by (rule eval_partial[OF cb64, symmetric]) (simp_all add: u)
    also have "\<dots> = poly (map_poly emb P) om"
      using eval_novel_emb[OF coords, of om] by (simp add: emb_of_bool)
    also have "\<dots> = FV (FFTTop5.inputT5 a) u * FV (FFTTop5.inputT5 b) u"
      by (simp add: P_def emb_poly.hom_mult forward_eval5[OF enc u] om_def)
    finally show "FV (FFTRef.gf264v TY(2048) (FFTTop5.inputT5 a) (FFTTop5.inputT5 b)) u = chain beta (2 ^ 43) 11 g u"
      using u by (simp add: gf264v_FV_gen)
  qed
  have "EqOn 2048 (FV (FFTRef.ibtfy11 (left_shift 1 43) (FFTRef.gf264v TY(2048) (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))))
      (ichain beta (2 ^ 43) 11 (chain beta (2 ^ 43) 11 g))"
    by (rule ibtfy11_ichain[OF s2w_sc43 prod])
  then have "FV (FFTRef.ibtfy11 (left_shift 1 43) (FFTRef.gf264v TY(2048) (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))) e = g e"
    using e by (simp add: EqOn_def ichain_chain)
  then have "gfw (seq_to_word (nth_seq (FFTRef.ibtfy11 (left_shift 1 43) (FFTRef.gf264v TY(2048) (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))) e))
      = gfw (encword (\<lambda>j. bit (seq_to_word n) (e + 2048 * j)))"
    using e by (simp add: FV_nth g_def)
  then show ?thesis by (rule gfw_inj)
qed

theorem mulT5_correct:
  fixes a b :: "(1024, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode5 fx = FFTEnc.encodeIdx5 fx"
    and dec: "\<And>fx. FFTEnc.decode5 fx = FFTEnc.decodeIdx5 fx"
  shows "Pl (L (FFTTop5.mulT5 (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))) = Pl (L a) * Pl (L b)"
proof -
  define P where "P = Pl (L a) * Pl (L b)"
  define pv where "pv = (word_to_seq (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<131072])) :: 131072 word) :: (131072, bool) seq)"
  define n where "n = FFTBC.bc1_131072 pv"
  define Y where "Y = FFTRef.ibtfy11 (left_shift 1 43) (FFTRef.gf264v TY(2048) (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))"
  define D where "D = FFTEnc.decodeIdx5 Y"
  have bA: "bnd 65536 (Pl (L a))" and bB: "bnd 65536 (Pl (L b))"
    using bnd_Pl[of "L a"] bnd_Pl[of "L b"] by (simp_all add: L_def)
  have bP: "bnd 131072 P" unfolding P_def by (rule bnd_mult[OF bA bB]) simp
  have pvP: "pw (seq_to_word pv) = P" unfolding pv_def using bit_poly_word[where 'n=131072, of P] bP by simp
  have Yw: "seq_to_word (nth_seq Y e) = encword (\<lambda>j. bit (seq_to_word n) (e + 2048 * j))" if "e < 2048" for e
    unfolding Y_def n_def pv_def P_def by (rule ibtfy_words5[OF enc that])
  have Dbits: "bitsof (L D) p = bit (seq_to_word n) p" if p: "p < 131072" for p
  proof -
    have "bitsof (L D) p = bit (linw decw (seq_to_word (nth_seq Y (p mod 2048)))) (p div 2048)"
      unfolding D_def by (simp add: decodeIdx5_bit[OF p] linmap_dec)
    also have "\<dots> = bit (seq_to_word n) (p mod 2048 + 2048 * (p div 2048))"
    proof -
      have pd: "p div 2048 < 64" using p by simp
      have pm: "p mod 2048 < 2048" by simp
      show ?thesis by (simp only: Yw[OF pm] decode_encword[OF pd])
    qed
    also have "p mod 2048 + 2048 * (p div 2048) = p" by (rule mod_mult_div_eq)
    finally show ?thesis .
  qed
  have DPl: "Pl (L D) = pw (seq_to_word n)"
  proof (rule poly_eqI)
    fix p
    show "coeff (Pl (L D)) p = coeff (pw (seq_to_word n)) p"
    proof (cases "p < 131072")
      case True then show ?thesis by (simp add: coeff_Pl coeff_pw Dbits)
    next
      case False
      then have "\<not> p div 64 < 2048" by (simp add: div_less_iff_less_mult)
      then have "\<not> bitsof (L D) p" by (simp add: bitsof_def L_def)
      then show ?thesis using False by (simp add: coeff_Pl coeff_pw bit_s2w)
    qed
  qed
  have flatD: "seq_to_list (coerce_seq_len (FFTBC.flat32 TY(4096) (coerce_seq_len (FFTTop.as32 TY(2048) D) :: (4096, (32, bool) seq) seq)) :: (131072, bool) seq) = seq_to_list n"
  proof (rule PL_inj)
    show "length (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(4096) (coerce_seq_len (FFTTop.as32 TY(2048) D) :: (4096, (32, bool) seq) seq)) :: (131072, bool) seq)) = length (seq_to_list n)"
      by simp
    have "seq_to_list (FFTBC.flat32 TY(4096) (coerce_seq_len (FFTTop.as32 TY(2048) D) :: (4096, (32, bool) seq) seq)) = seq_to_list (FFTBC.flat32 TY(2 \<times> 2048) (FFTTop.as32 TY(2048) D))"
      by (simp add: flat32_list stl_coerce)
    then have "PL (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(4096) (coerce_seq_len (FFTTop.as32 TY(2048) D) :: (4096, (32, bool) seq) seq)) :: (131072, bool) seq)) = Pl (L D)"
      by (simp add: stl_coerce flat32_as32 Pl_PL L_def)
    then show "PL (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(4096) (coerce_seq_len (FFTTop.as32 TY(2048) D) :: (4096, (32, bool) seq) seq)) :: (131072, bool) seq)) = PL (seq_to_list n)"
      by (simp add: DPl pw_PL)
  qed
  have cn: "(coerce_seq_len (FFTBC.flat32 TY(4096) (coerce_seq_len (FFTTop.as32 TY(2048) D) :: (4096, (32, bool) seq) seq)) :: (131072, bool) seq) = n"
    by (metis flatD seq_preserved)
  define Z where "Z = FFTBC.ibc1_131072w (coerce_seq_len (FFTTop.as32 TY(2048) D) :: (4096, (32, bool) seq) seq)"
  have "seq_to_list (FFTBC.flat32 TY(4096) Z) = seq_to_list (FFTBC.ibc1_131072 n)"
    by (simp add: Z_def ibc1_131072w_bits stl_coerce cn[symmetric] FFTBC.ibc1_131072_def)
  then have z: "seq_to_list (FFTBC.flat32 TY(4096) Z) = seq_to_list pv"
    by (simp add: n_def ibc_bc_131072)
  have "Pl (L (FFTTop.as64 TY(2048) (coerce_seq_len Z :: (2 \<times> 2048, (32, bool) seq) seq))) = PL (seq_to_list (FFTBC.flat32 TY(4096) Z))"
    by (simp add: L_def Pl_PL flat_as64_gen flat32_list stl_coerce)
  then have "Pl (L (FFTTop.as64 TY(2048) (coerce_seq_len Z :: (2 \<times> 2048, (32, bool) seq) seq))) = pw (seq_to_word pv)"
    by (simp add: z pw_PL)
  then show ?thesis by (simp add: FFTTop5.mulT5_def dec D_def[symmetric] Y_def[symmetric] Z_def pvP P_def)
qed

end
