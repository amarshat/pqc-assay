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

end
