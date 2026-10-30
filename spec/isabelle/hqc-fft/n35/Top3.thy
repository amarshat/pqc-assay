theory Top3
  imports Top5 HQC.FFTTop3
begin

text \<open>The hqc-3 model (polymul_576U64_input / polymul_576U64_mul, FFTTop3.cry) multiplies:
  mulT3 a b (inputT3 a) (inputT3 b) is the 1152-word product of the 576-word operands. The FFT
  handles the low 512 words (32768 bits, 1024 points, coset base 2^42); karat_mult_4096 (km64)
  the cross terms with the 64 words above. Hypotheses: the abc lemmas encode3 == encodeIdx3 and
  decode3 == decodeIdx3.\<close>

lemma s2w_sc42: "seq_to_word (left_shift (1 :: w64) 42) = 2 ^ 42"
  by (simp add: seq_to_word.left_shift word_seq_convs shiftl_def push_bit_eq_mult)

lemma bc1_32768wc_bits:
  fixes v :: "(1024, (32, bool) seq) seq"
  shows "FFTBC.flat32 TY(1024) (FFTBC.bc1_32768wc v)
       = coerce_seq_len (FFTBC.bc1of256 TY(128) (coerce_seq_len (FFTBC.bc256of32768 (FFTBC.repr32768 (coerce_seq_len (FFTBC.flat32 TY(1024) v))))))"
  by (simp add: FFTBC.bc1_32768wc_def FFTBC.bc1of256of32W_def FFTBC.bc256of32W_def FFTBC.repr32W_def flat32_unflat32)

lemma ibc1_65536w_bits:
  fixes v :: "(2048, (32, bool) seq) seq"
  shows "FFTBC.flat32 TY(2048) (FFTBC.ibc1_65536w v)
       = coerce_seq_len (FFTBC.irepr65536 (FFTBC.ibc256of65536 (coerce_seq_len (FFTBC.ibc1of256 TY(256) (coerce_seq_len (FFTBC.flat32 TY(2048) v))))))"
  by (simp add: FFTBC.ibc1_65536w_def FFTBC.irepr64W_def FFTBC.ibc256of64W_def FFTBC.ibc1of256of64W_def flat32_unflat32)

theorem forward_coords3:
  fixes a :: "(576, w64) seq"
  defines "w \<equiv> take' TY(512) TY(64) TY(w64) (coerce_seq_len a)"
  defines "x \<equiv> (coerce_seq_len (FFTTop.as32 TY(512) w) :: (1024, (32, bool) seq) seq)"
  defines "C \<equiv> FFTBC.bc1_32768 (coerce_seq_len (FFTBC.flat32 TY(1024) x))"
  shows "Pl (take 512 (L a)) = (\<Sum>d<2 ^ 15. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
proof -
  have "pw (seq_to_word (FFTBC.ibc1_32768 C)) = iconv T15 1 (pw (seq_to_word C))" by (rule ibc1_32768_iconv)
  also have "\<dots> = iconv T15 1 (\<Sum>d<2 ^ sz T15. monom (of_bool (bit (seq_to_word C) d)) d)"
    by (simp add: pw_sum_monom15 T15_sz)
  also have "\<dots> = (\<Sum>d<2 ^ sz T15. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
    by (rule iconv_novel[OF T15_wf])
  finally have i: "pw (seq_to_word (FFTBC.ibc1_32768 C)) = (\<Sum>d<2 ^ 15. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
    by (simp add: T15_sz)
  have "pw (seq_to_word (FFTBC.ibc1_32768 C)) = pw (seq_to_word (FFTBC.flat32 TY(1024) x))"
    by (simp add: C_def ibc_bc_32768 pw_coerce)
  also have "\<dots> = PL (concat (map seq_to_list (rev (seq_to_list w))))"
  proof -
    have "seq_to_list (FFTBC.flat32 TY(1024) x) = seq_to_list (FFTBC.flat32 TY(2 \<times> 512) (FFTTop.as32 TY(512) w))"
      by (simp add: flat32_list x_def stl_coerce)
    then show ?thesis by (simp add: pw_PL flat32_as32)
  qed
  also have "\<dots> = Pl (L w)" by (simp add: L_def Pl_PL)
  also have "L w = take 512 (L a)" by (simp add: w_def L_take L_coerce)
  finally show ?thesis using i by simp
qed

theorem forward_eval3:
  fixes a :: "(576, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode3 fx = FFTEnc.encodeIdx3 fx" and u: "u < 1024"
  shows "FV (FFTTop3.inputT3 a) u = poly (map_poly emb (Pl (take 512 (L a)))) (Cantor.cantor beta (2 ^ 42 + u))"
proof -
  define w where "w = take' TY(512) TY(64) TY(w64) (coerce_seq_len a)"
  define x where "x = (coerce_seq_len (FFTTop.as32 TY(512) w) :: (1024, (32, bool) seq) seq)"
  define C where "C = FFTBC.bc1_32768 (coerce_seq_len (FFTBC.flat32 TY(1024) x))"
  define fx where "fx = FFTTop.as64 TY(512) (coerce_seq_len (FFTBC.bc1_32768wc x))"
  define c where "c = (\<lambda>d. bit (seq_to_word C) d)"
  define om where "om = Cantor.cantor beta (2 ^ 42 + u)"
  have inp: "FFTTop3.inputT3 a = FFTRef.btfy10 (left_shift 1 42) (FFTEnc.encodeIdx3 fx)"
    by (simp add: FFTTop3.inputT3_def enc fx_def x_def w_def)
  have bits: "bit (seq_to_word (FFTEnc.flat3 fx)) d = c d" for d
  proof -
    have b1: "seq_to_list (FFTBC.flat32 TY(1024) (FFTBC.bc1_32768wc x)) = seq_to_list C"
      by (simp add: bc1_32768wc_bits stl_coerce C_def FFTBC.bc1_32768_def)
    have "seq_to_list (FFTEnc.flat3 fx) = seq_to_list (FFTBC.flat32 TY(1024) (FFTBC.bc1_32768wc x))"
      by (simp add: fx_def flat3_as64 flat32_list stl_coerce)
    then have "seq_to_list (FFTEnc.flat3 fx) = seq_to_list C" using b1 by simp
    then show ?thesis unfolding c_def by (rule bit_eq_list)
  qed
  define f where "f = (\<lambda>e. \<Sum>j<32. if c (1024 * j + e) then X j (beta 32) else 0)"
  have ef: "EqOn 1024 (FV (FFTEnc.encodeIdx3 fx)) f"
    unfolding EqOn_def by (auto simp: FV_nth encodeIdx3_gf bits f_def)
  have "FV (FFTTop3.inputT3 a) u = chain beta (2 ^ 42) 10 f u"
    using btfy10_chain[OF s2w_sc42 ef] u by (simp add: inp EqOn_def)
  also have "\<dots> = fft beta 10 (2 ^ 42) f u" by (rule net_fft) (simp_all add: u)
  also have "\<dots> = evalN 10 f om" unfolding om_def by (rule fft_eval[OF cb64]) (simp_all add: u)
  also have "\<dots> = (\<Sum>d<2 ^ 10 * 32. (if c d then 1 else 0) * X d om)"
  proof -
    have "evalN 10 (\<lambda>a. \<Sum>b<32. (if c (a + 2 ^ 10 * b) then 1 else 0) * X b (Cantor.cantor beta (2 ^ 42 div 2 ^ 10))) om
        = (\<Sum>d<2 ^ 10 * 32. (if c d then 1 else 0) * X d om)"
      unfolding om_def by (rule eval_partial[OF cb64, symmetric]) (simp_all add: u)
    moreover have "Cantor.cantor beta (2 ^ 42 div 2 ^ 10) = beta 32" using beta32 by simp
    moreover have "(\<lambda>a. \<Sum>b<32. (if c (a + 2 ^ 10 * b) then 1 else 0) * X b (beta 32)) = f"
      by (rule ext) (simp add: f_def add.commute if_one_mult)
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = poly (map_poly emb (Pl (take 512 (L a)))) om"
  proof -
    have "Pl (take 512 (L a)) = (\<Sum>d<2 ^ 15. smult (of_bool (c d)) (XP d))"
      unfolding c_def C_def x_def w_def by (rule forward_coords3)
    then have "poly (map_poly emb (Pl (take 512 (L a)))) om = (\<Sum>d<2 ^ 15. emb (of_bool (c d)) * X d om)"
      by (rule eval_novel_emb)
    then show ?thesis by (simp add: emb_of_bool)
  qed
  finally show ?thesis by (simp add: om_def)
qed

lemma bnd_Pl_take512: "bnd 32768 (Pl (take 512 (L (a :: (576, w64) seq))))"
  using bnd_Pl[of "take 512 (L a)"] by (simp add: L_def)

theorem ibtfy_words3:
  fixes a b :: "(576, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode3 fx = FFTEnc.encodeIdx3 fx"
  defines "P \<equiv> Pl (take 512 (L a)) * Pl (take 512 (L b))"
  defines "pv \<equiv> word_to_seq (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<65536])) :: 65536 word)"
  defines "n \<equiv> FFTBC.bc1_65536 pv"
  assumes e: "e < 1024"
  shows "seq_to_word (nth_seq (FFTRef.ibtfy10 (left_shift 1 42) (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))) e)
       = encword (\<lambda>j. bit (seq_to_word n) (e + 1024 * j))"
proof -
  have bP: "bnd 65536 P" unfolding P_def by (rule bnd_mult[OF bnd_Pl_take512 bnd_Pl_take512]) simp
  have pvP: "pw (seq_to_word pv) = P" unfolding pv_def using bit_poly_word[where 'n=65536, of P] bP by simp
  have coords: "P = (\<Sum>d<2 ^ 16. smult (of_bool (bit (seq_to_word n) d)) (XP d))"
  proof -
    have "P = pw (seq_to_word (FFTBC.ibc1_65536 n))" by (simp add: n_def ibc_bc_65536 pvP)
    also have "\<dots> = iconv T16 1 (pw (seq_to_word n))" by (rule ibc1_65536_iconv)
    also have "\<dots> = iconv T16 1 (\<Sum>d<2 ^ sz T16. monom (of_bool (bit (seq_to_word n) d)) d)"
      by (simp only: pw_sum_monom16 T16_sz)
    also have "\<dots> = (\<Sum>d<2 ^ sz T16. smult (of_bool (bit (seq_to_word n) d)) (XP d))"
      by (rule iconv_novel[OF T16_wf])
    finally show ?thesis by (simp add: T16_sz)
  qed
  define g where "g = (\<lambda>a'. gfw (encword (\<lambda>j. bit (seq_to_word n) (a' + 1024 * j))))"
  have gform: "g = (\<lambda>a'. \<Sum>b'<64. (if bit (seq_to_word n) (a' + 2 ^ 10 * b') then 1 else 0) * X b' (Cantor.cantor beta (2 ^ 42 div 2 ^ 10)))"
    using beta32 by (simp add: g_def gfw_encword if_one_mult fun_eq_iff)
  have prod: "EqOn 1024 (FV (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))) (chain beta (2 ^ 42) 10 g)"
    unfolding EqOn_def
  proof (intro allI impI)
    fix u :: nat assume u: "u < 1024"
    define om where "om = Cantor.cantor beta (2 ^ 42 + u)"
    have "chain beta (2 ^ 42) 10 g u = fft beta 10 (2 ^ 42) g u" by (rule net_fft) (simp_all add: u)
    also have "\<dots> = evalN 10 g om" unfolding om_def by (rule fft_eval[OF cb64]) (simp_all add: u)
    also have "\<dots> = (\<Sum>d<2 ^ 10 * 64. (if bit (seq_to_word n) d then 1 else 0) * X d om)"
      unfolding gform om_def by (rule eval_partial[OF cb64, symmetric]) (simp_all add: u)
    also have "\<dots> = poly (map_poly emb P) om"
      using eval_novel_emb[OF coords, of om] by (simp add: emb_of_bool)
    also have "\<dots> = FV (FFTTop3.inputT3 a) u * FV (FFTTop3.inputT3 b) u"
      by (simp add: P_def emb_poly.hom_mult forward_eval3[OF enc u] om_def)
    finally show "FV (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b)) u = chain beta (2 ^ 42) 10 g u"
      using u by (simp add: gf264v_FV_gen)
  qed
  have "EqOn 1024 (FV (FFTRef.ibtfy10 (left_shift 1 42) (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))))
      (ichain beta (2 ^ 42) 10 (chain beta (2 ^ 42) 10 g))"
    by (rule ibtfy10_ichain[OF s2w_sc42 prod])
  then have "FV (FFTRef.ibtfy10 (left_shift 1 42) (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))) e = g e"
    using e by (simp add: EqOn_def ichain_chain)
  then have "gfw (seq_to_word (nth_seq (FFTRef.ibtfy10 (left_shift 1 42) (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))) e))
      = gfw (encword (\<lambda>j. bit (seq_to_word n) (e + 1024 * j)))"
    using e by (simp add: FV_nth g_def)
  then show ?thesis by (rule gfw_inj)
qed

theorem fftpart3_correct:
  fixes a b :: "(576, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode3 fx = FFTEnc.encodeIdx3 fx"
    and dec: "\<And>fx. FFTEnc.decode3 fx = FFTEnc.decodeIdx3 fx"
  shows "Pl (L (FFTTop.as64 TY(1024) (coerce_seq_len (FFTBC.ibc1_65536w (coerce_seq_len (FFTTop.as32 TY(1024)
            (FFTEnc.decode3 (FFTRef.ibtfy10 (left_shift 1 42) (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b)))))
            :: (2048, (32, bool) seq) seq)) :: (2 \<times> 1024, (32, bool) seq) seq)))
       = Pl (take 512 (L a)) * Pl (take 512 (L b))"
proof -
  define P where "P = Pl (take 512 (L a)) * Pl (take 512 (L b))"
  define pv where "pv = (word_to_seq (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<65536])) :: 65536 word) :: (65536, bool) seq)"
  define n where "n = FFTBC.bc1_65536 pv"
  define Y where "Y = FFTRef.ibtfy10 (left_shift 1 42) (FFTRef.gf264v TY(1024) (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))"
  define D where "D = FFTEnc.decodeIdx3 Y"
  have bP: "bnd 65536 P" unfolding P_def by (rule bnd_mult[OF bnd_Pl_take512 bnd_Pl_take512]) simp
  have pvP: "pw (seq_to_word pv) = P" unfolding pv_def using bit_poly_word[where 'n=65536, of P] bP by simp
  have Yw: "seq_to_word (nth_seq Y e) = encword (\<lambda>j. bit (seq_to_word n) (e + 1024 * j))" if "e < 1024" for e
    unfolding Y_def n_def pv_def P_def by (rule ibtfy_words3[OF enc that])
  have Dbits: "bitsof (L D) p = bit (seq_to_word n) p" if p: "p < 65536" for p
  proof -
    have "bitsof (L D) p = bit (linw decw (seq_to_word (nth_seq Y (p mod 1024)))) (p div 1024)"
      unfolding D_def by (simp add: decodeIdx3_bit[OF p] linmap_dec)
    also have "\<dots> = bit (seq_to_word n) (p mod 1024 + 1024 * (p div 1024))"
    proof -
      have pd: "p div 1024 < 64" using p by simp
      have pm: "p mod 1024 < 1024" by simp
      show ?thesis by (simp only: Yw[OF pm] decode_encword[OF pd])
    qed
    also have "p mod 1024 + 1024 * (p div 1024) = p" by (rule mod_mult_div_eq)
    finally show ?thesis .
  qed
  have DPl: "Pl (L D) = pw (seq_to_word n)"
  proof (rule poly_eqI)
    fix p
    show "coeff (Pl (L D)) p = coeff (pw (seq_to_word n)) p"
    proof (cases "p < 65536")
      case True then show ?thesis by (simp add: coeff_Pl coeff_pw Dbits)
    next
      case False
      then have "\<not> p div 64 < 1024" by (simp add: div_less_iff_less_mult)
      then have "\<not> bitsof (L D) p" by (simp add: bitsof_def L_def)
      then show ?thesis using False by (simp add: coeff_Pl coeff_pw bit_s2w)
    qed
  qed
  have flatD: "seq_to_list (coerce_seq_len (FFTBC.flat32 TY(2048) (coerce_seq_len (FFTTop.as32 TY(1024) D) :: (2048, (32, bool) seq) seq)) :: (65536, bool) seq) = seq_to_list n"
  proof (rule PL_inj)
    show "length (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(2048) (coerce_seq_len (FFTTop.as32 TY(1024) D) :: (2048, (32, bool) seq) seq)) :: (65536, bool) seq)) = length (seq_to_list n)"
      by simp
    have "seq_to_list (FFTBC.flat32 TY(2048) (coerce_seq_len (FFTTop.as32 TY(1024) D) :: (2048, (32, bool) seq) seq)) = seq_to_list (FFTBC.flat32 TY(2 \<times> 1024) (FFTTop.as32 TY(1024) D))"
      by (simp add: flat32_list stl_coerce)
    then have "PL (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(2048) (coerce_seq_len (FFTTop.as32 TY(1024) D) :: (2048, (32, bool) seq) seq)) :: (65536, bool) seq)) = Pl (L D)"
      by (simp add: stl_coerce flat32_as32 Pl_PL L_def)
    then show "PL (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(2048) (coerce_seq_len (FFTTop.as32 TY(1024) D) :: (2048, (32, bool) seq) seq)) :: (65536, bool) seq)) = PL (seq_to_list n)"
      by (simp add: DPl pw_PL)
  qed
  have cn: "(coerce_seq_len (FFTBC.flat32 TY(2048) (coerce_seq_len (FFTTop.as32 TY(1024) D) :: (2048, (32, bool) seq) seq)) :: (65536, bool) seq) = n"
    by (metis flatD seq_preserved)
  define Z where "Z = FFTBC.ibc1_65536w (coerce_seq_len (FFTTop.as32 TY(1024) D) :: (2048, (32, bool) seq) seq)"
  have "seq_to_list (FFTBC.flat32 TY(2048) Z) = seq_to_list (FFTBC.ibc1_65536 n)"
    by (simp add: Z_def ibc1_65536w_bits stl_coerce cn[symmetric] FFTBC.ibc1_65536_def)
  then have z: "seq_to_list (FFTBC.flat32 TY(2048) Z) = seq_to_list pv"
    by (simp add: n_def ibc_bc_65536)
  have "Pl (L (FFTTop.as64 TY(1024) (coerce_seq_len Z :: (2 \<times> 1024, (32, bool) seq) seq))) = PL (seq_to_list (FFTBC.flat32 TY(2048) Z))"
    by (simp add: L_def Pl_PL flat_as64_gen flat32_list stl_coerce)
  then have "Pl (L (FFTTop.as64 TY(1024) (coerce_seq_len Z :: (2 \<times> 1024, (32, bool) seq) seq))) = pw (seq_to_word pv)"
    by (simp add: z pw_PL)
  then show ?thesis by (simp add: dec D_def[symmetric] Y_def[symmetric] Z_def pvP P_def)
qed

lemma fkm32_correct: "Pl (L (FFTRef.km32 a b)) = Pl (L a) * Pl (L b)"
  unfolding FFTRef.km32_def
  apply simp
  apply ((subst L_coerce, simp)?)
  apply (rule trans[OF kstep_correct])
       apply (simp_all add: L_coerce fkm16_correct)
  done

lemma fkm64_correct: "Pl (L (FFTRef.km64 a b)) = Pl (L a) * Pl (L b)"
  unfolding FFTRef.km64_def
  apply simp
  apply ((subst L_coerce, simp)?)
  apply (rule trans[OF kstep_correct])
       apply (simp_all add: L_coerce fkm32_correct)
  done

lemma pl3_Pl:
  fixes v :: "('n::len, w64) seq"
  assumes "LENGTH('o::len0) + LENGTH('n) \<le> 1152"
  shows "Pl (L (FFTTop3.pl3 TY('o) TY('n) v)) = monom 1 (64 * LENGTH('o)) * Pl (L v)"
  using assms by (simp add: FFTTop3.pl3_def L_append L_zero L_coerce Pl_append)

lemma seg3_L:
  fixes v :: "(('o::len0 + 'n::len) + 'r::len0, w64) seq"
  shows "L (FFTTop3.seg3 TY('o) TY('n) TY('r) v) = take LENGTH('n) (drop LENGTH('o) (L v))"
  by (simp add: FFTTop3.seg3_def L_take L_drop L_coerce)

lemma low_split3:
  assumes "length xs = 576"
  shows "Pl (take 512 xs) = Pl (take 64 xs) + monom 1 4096 * Pl (take 64 (drop 64 xs)) + monom 1 8192 * Pl (take 64 (drop 128 xs)) + monom 1 12288 * Pl (take 64 (drop 192 xs)) + monom 1 16384 * Pl (take 64 (drop 256 xs)) + monom 1 20480 * Pl (take 64 (drop 320 xs)) + monom 1 24576 * Pl (take 64 (drop 384 xs)) + monom 1 28672 * Pl (take 64 (drop 448 xs))"
proof -
  have t: "Pl (take (n + m) (drop off xs)) = Pl (take n (drop off xs)) + monom 1 (64 * n) * Pl (take m (drop (off + n) xs))"
    if "off + n + m \<le> 576" for off n m using Pl_split_seg[of off n m xs] that assms by simp
  show ?thesis
    by (simp only: t[of 0 64 448, simplified] t[of 64 64 384, simplified] t[of 128 64 320, simplified]
        t[of 192 64 256, simplified] t[of 256 64 192, simplified] t[of 320 64 128, simplified]
        t[of 384 64 64, simplified])
       (simp add: distrib_left monom_mm add.assoc)
qed

lemma length_L576: "length (L (a :: (576, w64) seq)) = 576"
  by (simp add: L_def)

lemma ypow4096: "monom (1::gf2) (4096 * k) = monom 1 4096 ^ k"
  by (simp add: monom_pow mult.commute)

theorem mulT3_correct:
  fixes a b :: "(576, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode3 fx = FFTEnc.encodeIdx3 fx"
    and dec: "\<And>fx. FFTEnc.decode3 fx = FFTEnc.decodeIdx3 fx"
  shows "Pl (L (FFTTop3.mulT3 a b (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))) = Pl (L a) * Pl (L b)"
proof -
  define xs where "xs = L a"
  define ys where "ys = L b"
  have lx: "length xs = 576" and ly: "length ys = 576" by (simp_all add: xs_def ys_def length_L576)
  have whole: "Pl zs = Pl (take 512 zs) + monom 1 32768 * Pl (drop 512 zs)" if "length zs = 576" for zs :: "64 word list"
    using Pl_take_drop[of 512 zs] that by simp
  have "Pl (L (FFTTop3.mulT3 a b (FFTTop3.inputT3 a) (FFTTop3.inputT3 b)))
      = Pl (take 512 xs) * Pl (take 512 ys) +
     (monom 1 65536 * (Pl (drop 512 xs) * Pl (drop 512 ys)) +
      monom 1 32768 * (Pl (take 64 xs) * Pl (drop 512 ys) + Pl (take 64 ys) * Pl (drop 512 xs)) +
      monom 1 36864 * (Pl (take 64 (drop 64 xs)) * Pl (drop 512 ys) + Pl (take 64 (drop 64 ys)) * Pl (drop 512 xs)) +
      monom 1 40960 * (Pl (take 64 (drop 128 xs)) * Pl (drop 512 ys) + Pl (take 64 (drop 128 ys)) * Pl (drop 512 xs)) +
      monom 1 45056 * (Pl (take 64 (drop 192 xs)) * Pl (drop 512 ys) + Pl (take 64 (drop 192 ys)) * Pl (drop 512 xs)) +
      monom 1 49152 * (Pl (take 64 (drop 256 xs)) * Pl (drop 512 ys) + Pl (take 64 (drop 256 ys)) * Pl (drop 512 xs)) +
      monom 1 53248 * (Pl (take 64 (drop 320 xs)) * Pl (drop 512 ys) + Pl (take 64 (drop 320 ys)) * Pl (drop 512 xs)) +
      monom 1 57344 * (Pl (take 64 (drop 384 xs)) * Pl (drop 512 ys) + Pl (take 64 (drop 384 ys)) * Pl (drop 512 xs)) +
      monom 1 61440 * (Pl (take 64 (drop 448 xs)) * Pl (drop 512 ys) + Pl (take 64 (drop 448 ys)) * Pl (drop 512 xs)))"
    apply (simp only: FFTTop3.mulT3_def Let_def)
    apply (simp del: xor_logic_seq add: L_xor L_append L_zero L_coerce Pl_xor Pl_append pl3_Pl seg3_L L_drop L_take
       fkm64_correct fftpart3_correct[OF enc dec] xs_def ys_def)
    done
  also have "\<dots> = Pl xs * Pl ys"
  proof -
    define Y where "Y = monom (1::gf2) 4096"
    have ys: "monom (1::gf2) 4096 = Y ^ 1" "monom (1::gf2) 8192 = Y ^ 2" "monom (1::gf2) 12288 = Y ^ 3" "monom (1::gf2) 16384 = Y ^ 4" "monom (1::gf2) 20480 = Y ^ 5" "monom (1::gf2) 24576 = Y ^ 6" "monom (1::gf2) 28672 = Y ^ 7" "monom (1::gf2) 32768 = Y ^ 8" "monom (1::gf2) 36864 = Y ^ 9" "monom (1::gf2) 40960 = Y ^ 10" "monom (1::gf2) 45056 = Y ^ 11" "monom (1::gf2) 49152 = Y ^ 12" "monom (1::gf2) 53248 = Y ^ 13" "monom (1::gf2) 57344 = Y ^ 14" "monom (1::gf2) 61440 = Y ^ 15" "monom (1::gf2) 65536 = Y ^ 16"
      by (simp_all add: Y_def ypow4096[symmetric])
    have ex: "Y ^ 9 = Y ^ 8 * Y ^ 1" "Y ^ 10 = Y ^ 8 * Y ^ 2" "Y ^ 11 = Y ^ 8 * Y ^ 3" "Y ^ 12 = Y ^ 8 * Y ^ 4" "Y ^ 13 = Y ^ 8 * Y ^ 5" "Y ^ 14 = Y ^ 8 * Y ^ 6" "Y ^ 15 = Y ^ 8 * Y ^ 7" "Y ^ 16 = Y ^ 8 * Y ^ 8"
      by (simp_all only: power_add[symmetric]) simp_all
    show ?thesis
      apply (simp only: whole[OF lx] whole[OF ly] low_split3[OF lx] low_split3[OF ly])
      apply (simp only: ys)
      apply (simp only: ex)
      apply (simp only: algebra_simps)
      done
  qed
  finally show ?thesis by (simp add: xs_def ys_def)
qed

end
