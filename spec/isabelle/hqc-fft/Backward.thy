theory Backward
  imports Cross
begin

lemma gf264v_FV:
  fixes x y :: "(512, w64) seq"
  assumes i: "i < 512"
  shows "FV (FFTRef.gf264v TY(512) x y) i = FV x i * FV y i"
proof -
  have "seq_to_list (FFTRef.gf264v TY(512) x y) = map (\<lambda>(p, q). FFTRef.gf264 p q) (zip (seq_to_list x) (seq_to_list y))"
    by (simp add: FFTRef.gf264v_def seq_to_list split_def comp_def)
  then show ?thesis using i by (simp add: FV_def gv_def gf264_gf)
qed

lemma bit_poly_word:
  fixes P :: "gf2 poly"
  assumes "bnd LENGTH('n::len) P"
  shows "pw (seq_to_word (word_to_seq (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<LENGTH('n)])) :: 'n word))) = P"
proof (rule poly_eqI)
  fix i
  define w where "w = (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<LENGTH('n)])) :: 'n word)"
  have "bit w i \<longleftrightarrow> i < LENGTH('n) \<and> coeff P i = 1"
    by (auto simp: w_def bit_of_bl_iff rev_nth)
  moreover have "coeff P i = 0" if "\<not> i < LENGTH('n)" using assms that by (simp add: bnd_def)
  moreover have "coeff P i = 1 \<or> coeff P i = 0" by (cases "coeff P i") auto
  ultimately show "coeff (pw (seq_to_word (word_to_seq w))) i = coeff P i"
    by (auto simp: coeff_pw)
qed

lemma pw_sum_monom15: "pw (seq_to_word (C :: (32768, bool) seq)) = (\<Sum>d<2 ^ 15. monom (of_bool (bit (seq_to_word C) d)) d)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_sum sum.delta bit_s2w)

lemma bnd_Pl_take: "bnd 16384 (Pl (take 256 (L (a :: (280, w64) seq))))"
proof -
  have "Pl (take 256 (L a)) = pw (seq_to_word (FFTBC.flat32 TY(512) (coerce_seq_len (FFTTop.as32 TY(256) (take' TY(256) TY(24) TY(w64) (coerce_seq_len a))) :: (512, (32, bool) seq) seq)))"
  proof -
    have "seq_to_list (FFTBC.flat32 TY(512) (coerce_seq_len (FFTTop.as32 TY(256) (take' TY(256) TY(24) TY(w64) (coerce_seq_len a))) :: (512, (32, bool) seq) seq))
        = seq_to_list (FFTBC.flat32 TY(2 \<times> 256) (FFTTop.as32 TY(256) (take' TY(256) TY(24) TY(w64) (coerce_seq_len a))))"
      by (simp add: flat32_list stl_coerce)
    then show ?thesis by (simp add: pw_PL flat32_as32 Pl_PL[symmetric] L_def[symmetric] L_take L_coerce)
  qed
  moreover have "bnd 16384 (pw (seq_to_word (FFTBC.flat32 TY(512) (coerce_seq_len (FFTTop.as32 TY(256) (take' TY(256) TY(24) TY(w64) (coerce_seq_len a))) :: (512, (32, bool) seq) seq))))"
    by (rule bnd_mono[OF bnd_pw]) simp
  ultimately show ?thesis by simp
qed

theorem ibtfy_words:
  fixes a b :: "(280, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode fx = FFTEnc.encodeIdx fx"
  defines "P \<equiv> Pl (take 256 (L a)) * Pl (take 256 (L b))"
  defines "pv \<equiv> word_to_seq (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<32768])) :: 32768 word)"
  defines "n \<equiv> FFTBC.bc1_32768 pv"
  assumes e: "e < 512"
  shows "seq_to_word (nth_seq (FFTRef.ibtfy9 (left_shift 1 41) (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b))) e)
       = encword (\<lambda>j. bit (seq_to_word n) (e + 512 * j))"
proof -
  have bP: "bnd 32768 P"
    unfolding P_def by (rule bnd_mult[OF bnd_Pl_take bnd_Pl_take]) simp
  have pvP: "pw (seq_to_word pv) = P" unfolding pv_def using bit_poly_word[where 'n=32768, of P] bP by simp
  have coords: "P = (\<Sum>d<2 ^ 15. smult (of_bool (bit (seq_to_word n) d)) (XP d))"
  proof -
    have "P = pw (seq_to_word (FFTBC.ibc1_32768 n))" by (simp add: n_def ibc_bc_32768 pvP)
    also have "\<dots> = iconv T15 1 (pw (seq_to_word n))" by (rule ibc1_32768_iconv)
    also have "\<dots> = iconv T15 1 (\<Sum>d<2 ^ sz T15. monom (of_bool (bit (seq_to_word n) d)) d)"
      by (simp only: pw_sum_monom15 T15_sz)
    also have "\<dots> = (\<Sum>d<2 ^ sz T15. smult (of_bool (bit (seq_to_word n) d)) (XP d))"
      by (rule iconv_novel[OF T15_wf])
    finally show ?thesis by (simp add: T15_sz)
  qed
  define g where "g = (\<lambda>a'. gfw (encword (\<lambda>j. bit (seq_to_word n) (a' + 512 * j))))"
  have gform: "g = (\<lambda>a'. \<Sum>b'<64. (if bit (seq_to_word n) (a' + 2 ^ 9 * b') then 1 else 0) * X b' (Cantor.cantor beta (2 ^ 41 div 2 ^ 9)))"
    using beta32 by (simp add: g_def gfw_encword if_one_mult fun_eq_iff)
  have prod: "EqOn 512 (FV (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b))) (chain beta (2 ^ 41) 9 g)"
    unfolding EqOn_def
  proof (intro allI impI)
    fix u :: nat assume u: "u < 512"
    define om where "om = Cantor.cantor beta (2 ^ 41 + u)"
    have "chain beta (2 ^ 41) 9 g u = fft beta 9 (2 ^ 41) g u" by (rule net_fft) (simp_all add: u)
    also have "\<dots> = evalN 9 g om" unfolding om_def by (rule fft_eval[OF cb64]) (simp_all add: u)
    also have "\<dots> = (\<Sum>d<2 ^ 9 * 64. (if bit (seq_to_word n) d then 1 else 0) * X d om)"
      unfolding gform om_def by (rule eval_partial[OF cb64, symmetric]) (simp_all add: u)
    also have "\<dots> = poly (map_poly emb P) om"
      using eval_novel_emb[OF coords, of om] by (simp add: emb_of_bool)
    also have "\<dots> = FV (FFTTop.inputT a) u * FV (FFTTop.inputT b) u"
      by (simp add: P_def emb_poly.hom_mult forward_eval[OF enc u] om_def)
    finally show "FV (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b)) u = chain beta (2 ^ 41) 9 g u"
      using u by (simp add: gf264v_FV)
  qed
  have "EqOn 512 (FV (FFTRef.ibtfy9 (left_shift 1 41) (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b))))
      (ichain beta (2 ^ 41) 9 (chain beta (2 ^ 41) 9 g))"
    by (rule ibtfy9_ichain[OF s2w_sc prod])
  then have "FV (FFTRef.ibtfy9 (left_shift 1 41) (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b))) e = g e"
    using e by (simp add: EqOn_def ichain_chain)
  then have "gfw (seq_to_word (nth_seq (FFTRef.ibtfy9 (left_shift 1 41) (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b))) e))
      = gfw (encword (\<lambda>j. bit (seq_to_word n) (e + 512 * j)))"
    using e by (simp add: FV_nth g_def)
  then show ?thesis by (rule gfw_inj)
qed

lemma PL_inj: "length l1 = length l2 \<Longrightarrow> PL l1 = PL l2 \<Longrightarrow> l1 = l2"
proof (rule nth_equalityI)
  fix k assume len: "length l1 = length l2" and e: "PL l1 = PL l2" and k: "k < length l1"
  define p where "p = length l1 - Suc k"
  have p: "p < length l1" "length l1 - Suc p = k" using k by (simp_all add: p_def)
  have "coeff (PL l1) p = coeff (PL l2) p" using e by simp
  then have "of_bool (l1 ! k) = (of_bool (l2 ! k) :: gf2)" using p len by (simp add: coeff_PL)
  then show "l1 ! k = l2 ! k" by (cases "l1 ! k"; cases "l2 ! k") simp_all
qed simp

lemma flat_as64_gen: "concat (map seq_to_list (rev (seq_to_list (FFTTop.as64 TY('n::len) y))))
    = concat (map seq_to_list (rev (seq_to_list (y :: (2 \<times> 'n, (32, bool) seq) seq))))"
proof -
  define G where "G = group_list LENGTH('n) 2 (seq_to_list y)"
  have g: "\<forall>x\<in>set G. length x = 2"
    using group_list_grouped[of "seq_to_list y" "LENGTH('n)" 2] by (simp add: G_def)
  have cG: "concat G = seq_to_list y" by (simp add: G_def concat_group_list_inv)
  have "concat (map seq_to_list (rev (seq_to_list (FFTTop.as64 TY('n) y)))) = concat (rev (map (\<lambda>g. seq_to_list (g ! Suc 0) @ seq_to_list (g ! 0)) G))"
    by (simp add: as64_list G_def[symmetric] rev_map comp_def seq_to_list.append_seq)
  also have "\<dots> = concat (map seq_to_list (rev (concat G)))" by (rule concat_rev_pairs[OF g])
  finally show ?thesis by (simp add: cG)
qed

lemma ibc1_32768w_bits:
  fixes v :: "(1024, (32, bool) seq) seq"
  shows "FFTBC.flat32 TY(1024) (FFTBC.ibc1_32768w v)
       = coerce_seq_len (FFTBC.irepr32768 (FFTBC.ibc256of32768 (coerce_seq_len (FFTBC.ibc1of256 TY(128) (coerce_seq_len (FFTBC.flat32 TY(1024) v))))))"
  by (simp add: FFTBC.ibc1_32768w_def FFTBC.irepr32W_def FFTBC.ibc256of32W_def FFTBC.ibc1of256of32W_def flat32_unflat32)

theorem fftpart_correct:
  fixes a b :: "(280, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode fx = FFTEnc.encodeIdx fx"
    and dec: "\<And>fx. FFTEnc.decode fx = FFTEnc.decodeIdx fx"
  shows "Pl (L (FFTTop.as64 TY(512) (coerce_seq_len (FFTBC.ibc1_32768w (coerce_seq_len (FFTTop.as32 TY(512)
            (FFTEnc.decode (FFTRef.ibtfy9 (left_shift 1 41) (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b)))))
            :: (1024, (32, bool) seq) seq)) :: (2 \<times> 512, (32, bool) seq) seq)))
       = Pl (take 256 (L a)) * Pl (take 256 (L b))"
proof -
  define P where "P = Pl (take 256 (L a)) * Pl (take 256 (L b))"
  define pv where "pv = (word_to_seq (of_bl (rev (map (\<lambda>i. coeff P i = 1) [0..<32768])) :: 32768 word) :: (32768, bool) seq)"
  define n where "n = FFTBC.bc1_32768 pv"
  define Y where "Y = FFTRef.ibtfy9 (left_shift 1 41) (FFTRef.gf264v TY(512) (FFTTop.inputT a) (FFTTop.inputT b))"
  define D where "D = FFTEnc.decodeIdx Y"
  have bP: "bnd 32768 P" unfolding P_def by (rule bnd_mult[OF bnd_Pl_take bnd_Pl_take]) simp
  have pvP: "pw (seq_to_word pv) = P" unfolding pv_def using bit_poly_word[where 'n=32768, of P] bP by simp
  have Yw: "seq_to_word (nth_seq Y e) = encword (\<lambda>j. bit (seq_to_word n) (e + 512 * j))" if "e < 512" for e
    unfolding Y_def n_def pv_def P_def by (rule ibtfy_words[OF enc that])
  have Dbits: "bitsof (L D) p = bit (seq_to_word n) p" if p: "p < 32768" for p
  proof -
    have "bitsof (L D) p = bit (linw decw (seq_to_word (nth_seq Y (p mod 512)))) (p div 512)"
      unfolding D_def by (simp add: decodeIdx_bit[OF p] linmap_dec)
    also have "\<dots> = bit (seq_to_word n) (p mod 512 + 512 * (p div 512))"
    proof -
      have pd: "p div 512 < 64" using p by simp
      have pm: "p mod 512 < 512" by simp
      show ?thesis by (simp only: Yw[OF pm] decode_encword[OF pd])
    qed
    also have "p mod 512 + 512 * (p div 512) = p" by (rule mod_mult_div_eq)
    finally show ?thesis .
  qed
  have DPl: "Pl (L D) = pw (seq_to_word n)"
  proof (rule poly_eqI)
    fix p
    show "coeff (Pl (L D)) p = coeff (pw (seq_to_word n)) p"
    proof (cases "p < 32768")
      case True then show ?thesis by (simp add: coeff_Pl coeff_pw Dbits)
    next
      case False
      then have "\<not> p div 64 < 512" by (simp add: div_less_iff_less_mult)
      then have "\<not> bitsof (L D) p" by (simp add: bitsof_def L_def)
      then show ?thesis using False by (simp add: coeff_Pl coeff_pw bit_s2w)
    qed
  qed
  have flatD: "seq_to_list (coerce_seq_len (FFTBC.flat32 TY(1024) (coerce_seq_len (FFTTop.as32 TY(512) D) :: (1024, (32, bool) seq) seq)) :: (32768, bool) seq) = seq_to_list n"
  proof (rule PL_inj)
    show "length (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(1024) (coerce_seq_len (FFTTop.as32 TY(512) D) :: (1024, (32, bool) seq) seq)) :: (32768, bool) seq)) = length (seq_to_list n)"
      by simp
    have "seq_to_list (FFTBC.flat32 TY(1024) (coerce_seq_len (FFTTop.as32 TY(512) D) :: (1024, (32, bool) seq) seq)) = seq_to_list (FFTBC.flat32 TY(2 \<times> 512) (FFTTop.as32 TY(512) D))"
      by (simp add: flat32_list stl_coerce)
    then have "PL (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(1024) (coerce_seq_len (FFTTop.as32 TY(512) D) :: (1024, (32, bool) seq) seq)) :: (32768, bool) seq)) = Pl (L D)"
      by (simp add: stl_coerce flat32_as32 Pl_PL L_def)
    then show "PL (seq_to_list (coerce_seq_len (FFTBC.flat32 TY(1024) (coerce_seq_len (FFTTop.as32 TY(512) D) :: (1024, (32, bool) seq) seq)) :: (32768, bool) seq)) = PL (seq_to_list n)"
      by (simp add: DPl pw_PL)
  qed
  have cn: "(coerce_seq_len (FFTBC.flat32 TY(1024) (coerce_seq_len (FFTTop.as32 TY(512) D) :: (1024, (32, bool) seq) seq)) :: (32768, bool) seq) = n"
    by (metis flatD seq_preserved)
  define Z where "Z = FFTBC.ibc1_32768w (coerce_seq_len (FFTTop.as32 TY(512) D) :: (1024, (32, bool) seq) seq)"
  have "seq_to_list (FFTBC.flat32 TY(1024) Z) = seq_to_list (FFTBC.ibc1_32768 n)"
    by (simp add: Z_def ibc1_32768w_bits stl_coerce cn[symmetric] FFTBC.ibc1_32768_def)
  then have z: "seq_to_list (FFTBC.flat32 TY(1024) Z) = seq_to_list pv"
    by (simp add: n_def ibc_bc_32768)
  have "Pl (L (FFTTop.as64 TY(512) (coerce_seq_len Z :: (2 \<times> 512, (32, bool) seq) seq))) = PL (seq_to_list (FFTBC.flat32 TY(1024) Z))"
    by (simp add: L_def Pl_PL flat_as64_gen flat32_list stl_coerce)
  then have "Pl (L (FFTTop.as64 TY(512) (coerce_seq_len Z :: (2 \<times> 512, (32, bool) seq) seq))) = pw (seq_to_word pv)"
    by (simp add: z pw_PL)
  then show ?thesis by (simp add: dec D_def[symmetric] Y_def[symmetric] Z_def pvP P_def)
qed

end
