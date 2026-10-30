theory Forward
  imports ViewBridge
begin

text \<open>The input transform of the hqc-1 model evaluates the low 256 words of its argument, read as a
  polynomial over GF(2) and embedded in GF(2^64), at the 512 points cantor(2^41 + u). The hypothesis
  enc is the model lemma encode == encodeIdx that make hqc-fft-lemmas proves with abc.\<close>

lemma s2w_sc: "seq_to_word (left_shift (1 :: w64) 41) = 2 ^ 41"
  by (simp add: seq_to_word.left_shift word_seq_convs shiftl_def push_bit_eq_mult)

lemma bits_eq_pw: "seq_to_list x = seq_to_list y \<Longrightarrow> pw (seq_to_word (x :: ('n::len, bool) seq)) = pw (seq_to_word (y :: ('m::len, bool) seq))"
  by (simp add: pw_PL)

lemma bit_eq_list:
  assumes e: "seq_to_list x = seq_to_list y"
  shows "bit (seq_to_word (x :: ('n::len, bool) seq)) d = bit (seq_to_word (y :: ('m::len, bool) seq)) d"
proof -
  have l: "LENGTH('n) = LENGTH('m)" using arg_cong[OF e, of length] by simp
  show ?thesis by (simp add: bit_s2w e l)
qed

lemma stl_coerce: "LENGTH('m) = LENGTH('n) \<Longrightarrow> seq_to_list (coerce_seq_len (x :: ('n::len0, 'a) seq) :: ('m::len0, 'a) seq) = seq_to_list x"
  by (simp add: coerce_seq_len.rep_eq)

lemma if_one_mult: "(if b then 1 else 0) * (y :: 'a :: comm_ring_1) = (if b then y else 0)"
  by simp

lemma emb_of_bool: "emb (of_bool b) = (if b then 1 else 0)"
  by (simp add: emb_def)

lemma pw_sum_monom: "pw (seq_to_word (C :: (16384, bool) seq)) = (\<Sum>d<2 ^ 14. monom (of_bool (bit (seq_to_word C) d)) d)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_sum sum.delta bit_s2w)

text \<open>Step 1: the encode input bits are the novel-basis coordinates of the low part.\<close>

theorem forward_coords:
  fixes a :: "(280, w64) seq"
  defines "w \<equiv> take' TY(256) TY(24) TY(w64) (coerce_seq_len a)"
  defines "x \<equiv> (coerce_seq_len (FFTTop.as32 TY(256) w) :: (512, (32, bool) seq) seq)"
  defines "C \<equiv> FFTBC.bc1 (coerce_seq_len (FFTBC.flat32 TY(512) x))"
  shows "Pl (take 256 (L a)) = (\<Sum>d<2 ^ 14. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
proof -
  have "pw (seq_to_word (FFTBC.ibc1 C)) = iconv T14 1 (pw (seq_to_word C))" by (rule ibc1_iconv)
  also have "\<dots> = iconv T14 1 (\<Sum>d<2 ^ sz T14. monom (of_bool (bit (seq_to_word C) d)) d)"
    by (simp add: pw_sum_monom T14_sz)
  also have "\<dots> = (\<Sum>d<2 ^ sz T14. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
    by (rule iconv_novel[OF T14_wf])
  finally have i: "pw (seq_to_word (FFTBC.ibc1 C)) = (\<Sum>d<2 ^ 14. smult (of_bool (bit (seq_to_word C) d)) (XP d))"
    by (simp add: T14_sz)
  have "pw (seq_to_word (FFTBC.ibc1 C)) = pw (seq_to_word (FFTBC.flat32 TY(512) x))"
    by (simp add: C_def ibc_bc_16384 pw_coerce)
  also have "\<dots> = PL (concat (map seq_to_list (rev (seq_to_list w))))"
  proof -
    have "seq_to_list (FFTBC.flat32 TY(512) x) = seq_to_list (FFTBC.flat32 TY(2 \<times> 256) (FFTTop.as32 TY(256) w))"
      by (simp add: flat32_list x_def stl_coerce)
    then show ?thesis by (simp add: pw_PL flat32_as32)
  qed
  also have "\<dots> = Pl (L w)" by (simp add: L_def Pl_PL)
  also have "L w = take 256 (L a)" by (simp add: w_def L_take L_coerce)
  finally show ?thesis using i by simp
qed

lemma FV_nth: "i < LENGTH('n) \<Longrightarrow> FV (p :: ('n::len, w64) seq) i = gfw (seq_to_word (nth_seq p i))"
  by (simp add: FV_def gv_def nth_seq.rep_eq)

lemma cb64: "cantor_basis 64 beta" by (rule beta_cantor)

theorem forward_eval:
  fixes a :: "(280, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode fx = FFTEnc.encodeIdx fx" and u: "u < 512"
  shows "FV (FFTTop.inputT a) u = poly (map_poly emb (Pl (take 256 (L a)))) (Cantor.cantor beta (2 ^ 41 + u))"
proof -
  define w where "w = take' TY(256) TY(24) TY(w64) (coerce_seq_len a)"
  define x where "x = (coerce_seq_len (FFTTop.as32 TY(256) w) :: (512, (32, bool) seq) seq)"
  define C where "C = FFTBC.bc1 (coerce_seq_len (FFTBC.flat32 TY(512) x))"
  define fx where "fx = FFTTop.as64 TY(256) (coerce_seq_len (FFTBC.bc1w x))"
  define c where "c = (\<lambda>d. bit (seq_to_word C) d)"
  define om where "om = Cantor.cantor beta (2 ^ 41 + u)"
  have inp: "FFTTop.inputT a = FFTRef.btfy9 (left_shift 1 41) (FFTEnc.encodeIdx fx)"
    by (simp add: FFTTop.inputT_def enc fx_def x_def w_def)
  have bits: "bit (seq_to_word (FFTEnc.flat fx)) d = c d" for d
  proof -
    have b1: "seq_to_list (FFTBC.flat32 TY(512) (FFTBC.bc1w x)) = seq_to_list C"
      by (simp add: bc1w_bits stl_coerce C_def FFTBC.bc1_def)
    have "seq_to_list (FFTEnc.flat fx) = seq_to_list (FFTBC.flat32 TY(512) (FFTBC.bc1w x))"
      by (simp add: fx_def flat_as64 flat32_list stl_coerce)
    then have "seq_to_list (FFTEnc.flat fx) = seq_to_list C" using b1 by simp
    then show ?thesis unfolding c_def by (rule bit_eq_list)
  qed
  define f where "f = (\<lambda>e. \<Sum>j<32. if c (512 * j + e) then X j (beta 32) else 0)"
  have ef: "EqOn 512 (FV (FFTEnc.encodeIdx fx)) f"
    unfolding EqOn_def by (auto simp: FV_nth encodeIdx_gf bits f_def)
  have "FV (FFTTop.inputT a) u = chain beta (2 ^ 41) 9 f u"
    using btfy9_chain[OF s2w_sc ef] u by (simp add: inp EqOn_def)
  also have "\<dots> = fft beta 9 (2 ^ 41) f u" by (rule net_fft) (simp_all add: u)
  also have "\<dots> = evalN 9 f om" unfolding om_def by (rule fft_eval[OF cb64]) (simp_all add: u)
  also have "\<dots> = (\<Sum>d<2 ^ 9 * 32. (if c d then 1 else 0) * X d om)"
  proof -
    have "evalN 9 (\<lambda>a. \<Sum>b<32. (if c (a + 2 ^ 9 * b) then 1 else 0) * X b (Cantor.cantor beta (2 ^ 41 div 2 ^ 9))) om
        = (\<Sum>d<2 ^ 9 * 32. (if c d then 1 else 0) * X d om)"
      unfolding om_def by (rule eval_partial[OF cb64, symmetric]) (simp_all add: u)
    moreover have "Cantor.cantor beta (2 ^ 41 div 2 ^ 9) = beta 32" using beta32 by simp
    moreover have "(\<lambda>a. \<Sum>b<32. (if c (a + 2 ^ 9 * b) then 1 else 0) * X b (beta 32)) = f"
      by (rule ext) (simp add: f_def add.commute if_one_mult)
    ultimately show ?thesis by simp
  qed
  also have "\<dots> = poly (map_poly emb (Pl (take 256 (L a)))) om"
  proof -
    have "Pl (take 256 (L a)) = (\<Sum>d<2 ^ 14. smult (of_bool (c d)) (XP d))"
      unfolding c_def C_def x_def w_def by (rule forward_coords)
    then have "poly (map_poly emb (Pl (take 256 (L a)))) om = (\<Sum>d<2 ^ 14. emb (of_bool (c d)) * X d om)"
      by (rule eval_novel_emb)
    then show ?thesis by (simp add: emb_of_bool)
  qed
  finally show ?thesis by (simp add: om_def)
qed

end
