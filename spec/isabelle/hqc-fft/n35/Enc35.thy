theory Enc35
  imports "HQC_FFT.Forward"
begin

text \<open>encode_64 and decode_64 at the hqc-3 and hqc-5 sizes: the index forms in GF(2^64), and the
  flat views of the encode input. Instances of the hqc-1 proofs (EncBridge, DecBridge, ViewBridge)
  with the sizes changed.\<close>


lemma idx16: "j < 32 \<Longrightarrow> e < 1024 \<Longrightarrow> unat (1024 * word_of_nat j + word_of_nat e :: 16 word) = 1024 * j + e"
  by (simp add: unat_word_ariths unat_of_nat)

lemma encode_bit3:
  fixes fx :: "(512, w64) seq" and e j :: nat
  assumes "e < 1024" "j < 32"
  shows "bit (seq_to_word (rev_seq (coerce_seq_len (map_seq (\<lambda>j. nth_end_list (seq_to_list (FFTEnc.flat3 fx)) (to_nat (0x400 * j + from_nat e)))
            (fromToLessThan TY(0) TY(32) TY((16, bool) seq)))) :: (32, bool) seq)) j
       = bit (seq_to_word (FFTEnc.flat3 fx)) (1024 * j + e)"
  using assms by (simp add: bit_s2w rev_seq.rep_eq coerce_seq_len.rep_eq map_seq_code seq_to_list.fromToLessThan rev_nth
      to_nat_seq_to_word plus_seq_conv times_seq_conv seq_to_word.from_nat from_nat_word numeral_seq_word_conv idx16)

theorem encodeIdx3_gf:
  fixes fx :: "(512, w64) seq"
  assumes e: "e < 1024"
  shows "gfw (seq_to_word (nth_seq (FFTEnc.encodeIdx3 fx) e))
       = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat3 fx)) (1024 * j + e) then X j (beta 32) else 0)"
proof -
  define V where "V = (rev_seq (coerce_seq_len (map_seq (\<lambda>j. nth_end_list (seq_to_list (FFTEnc.flat3 fx)) (to_nat (0x400 * j + from_nat e)))
            (fromToLessThan TY(0) TY(32) TY((16, bool) seq)))) :: (32, bool) seq)"
  have nt: "nth_seq (FFTEnc.encodeIdx3 fx) e = FFTEnc.linmap TY(32) FFTEnc.encMat V"
    using e by (simp add: FFTEnc.encodeIdx3_def Let_def seq_to_list nth_seq.rep_eq V_def)
  have "gfw (seq_to_word (nth_seq (FFTEnc.encodeIdx3 fx) e))
      = sum_list (map gfw (map (\<lambda>j. if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0) [0..<32]))"
    by (simp add: nt linmap_word gfw_foldl_xor)
  also have "\<dots> = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat3 fx)) (1024 * j + e) then X j (beta 32) else 0)"
  proof -
    have pt: "\<And>j. j < 32 \<Longrightarrow> gfw (if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0)
            = (if bit (seq_to_word (FFTEnc.flat3 fx)) (1024 * j + e) then X j (beta 32) else 0)"
      using e by (simp add: V_def encode_bit3 encw_nth enc_x)
    have "sum_list (map gfw (map (\<lambda>j. if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0) [0..<32]))
        = (\<Sum>j\<in>{0..<32}. gfw (if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0))"
      by (simp only: map_map sum_set_upt_conv_sum_list_nat[symmetric] set_upt comp_def)
    also have "\<dots> = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat3 fx)) (1024 * j + e) then X j (beta 32) else 0)"
      by (simp only: atLeast0LessThan) (rule sum.cong, rule refl, simp add: pt)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed


lemma idx16m: "p < 65536 \<Longrightarrow> to_nat (from_nat p mod 0x400 :: (16, bool) seq) = p mod 1024"
  and idx16d: "p < 65536 \<Longrightarrow> to_nat (from_nat p div 0x400 :: (16, bool) seq) = p div 1024"
  by (simp_all add: to_nat_seq_to_word word_seq_convs seq_to_word.from_nat unat_word_ariths unat_of_nat
      unat_mod unat_div from_nat_word unat_of_nat_eq)

lemma decodeIdx3_bit:
  fixes fx :: "(1024, w64) seq"
  assumes p: "p < 65536"
  shows "bitsof (L (FFTEnc.decodeIdx3 fx)) p
       = bit (seq_to_word (FFTEnc.linmap TY(64) FFTEnc.decMat (nth_seq fx (p mod 1024)))) (p div 1024)"
proof -
  define bf where "bf = (\<lambda>p::nat. nth_end_list (seq_to_list (nth_list (map (FFTEnc.linmap TY(64) FFTEnc.decMat) (seq_to_list fx))
                           (to_nat (from_nat p mod 0x400 :: (16, bool) seq)))) (to_nat (from_nat p div 0x400 :: (16, bool) seq)))"
  define BL where "BL = map bf [0..<65536]"
  define G where "G = group_list 1024 64 (rev BL)"
  have lBL: "length (rev BL) = 1024 * 64" by (simp add: BL_def)
  have sl: "seq_to_list (FFTEnc.decodeIdx3 fx) = rev (map list_to_seq G)"
    by (simp add: FFTEnc.decodeIdx3_def Let_def FFTEnc.unflat23_def seq_to_list G_def BL_def bf_def comp_def)
  define i where "i = p div 64"
  define r where "r = p mod 64"
  have i: "i < 1024" using p by (simp add: i_def)
  have r: "r < 64" by (simp add: r_def)
  have pir: "p = 64 * i + r" by (simp add: i_def r_def)
  have lg: "length (G ! (1023 - i)) = 64" using i lBL by (simp add: G_def)
  have "L (FFTEnc.decodeIdx3 fx) ! i = seq_to_word (list_to_seq (G ! (1023 - i)) :: w64)"
    using i by (simp add: L_def sl rev_nth G_def)
  then have "bitsof (L (FFTEnc.decodeIdx3 fx)) p = bit (seq_to_word (list_to_seq (G ! (1023 - i)) :: w64)) r"
    using i by (simp add: bitsof_def L_def i_def r_def)
  also have "\<dots> = (G ! (1023 - i)) ! (63 - r)"
    using r lg by (simp add: bit_s2w)
  also have "\<dots> = rev BL ! ((1023 - i) * 64 + (63 - r))"
    using i r lBL by (simp add: G_def group_list_elem)
  also have "\<dots> = BL ! p"
  proof -
    have "(1023 - i) * 64 + (63 - r) < length BL" using i r by (simp add: BL_def)
    moreover have "length BL - Suc ((1023 - i) * 64 + (63 - r)) = p" using i r pir by (simp add: BL_def)
    ultimately show ?thesis by (simp add: rev_nth)
  qed
  also have "\<dots> = bf p" using p by (simp add: BL_def)
  also have "\<dots> = bit (seq_to_word (FFTEnc.linmap TY(64) FFTEnc.decMat (nth_seq fx (p mod 1024)))) (p div 1024)"
  proof -
    have pm: "p mod 1024 < 1024" by simp
    have pd: "p div 1024 < 64" using p by simp
    show ?thesis using p pm pd by (simp add: bf_def idx16m idx16d bit_s2w nth_seq.rep_eq)
  qed
  finally show ?thesis .
qed


lemma flat3_list: "seq_to_list (FFTEnc.flat3 (fx :: (512, w64) seq)) = concat (map seq_to_list (rev (seq_to_list fx)))"
  by (simp add: FFTEnc.flat3_def seq_to_list)

theorem flat3_as64: "seq_to_list (FFTEnc.flat3 (FFTTop.as64 TY(512) y)) = seq_to_list (FFTBC.flat32 TY(2 \<times> 512) y)"
proof -
  define G where "G = group_list 512 2 (seq_to_list y)"
  have g: "\<forall>x\<in>set G. length x = 2"
    using group_list_grouped[of "seq_to_list y" 512 2] by (simp add: G_def)
  have cG: "concat G = seq_to_list y" by (simp add: G_def concat_group_list_inv)
  have "seq_to_list (FFTEnc.flat3 (FFTTop.as64 TY(512) y)) = concat (rev (map (\<lambda>g. seq_to_list (g ! Suc 0) @ seq_to_list (g ! 0)) G))"
    by (simp add: flat3_list as64_list G_def[symmetric] rev_map comp_def seq_to_list.append_seq)
  also have "\<dots> = concat (map seq_to_list (rev (concat G)))" by (rule concat_rev_pairs[OF g])
  also have "\<dots> = seq_to_list (FFTBC.flat32 TY(2 \<times> 512) y)" by (simp add: flat32_list cG)
  finally show ?thesis .
qed


lemma idx17: "j < 32 \<Longrightarrow> e < 2048 \<Longrightarrow> unat (2048 * word_of_nat j + word_of_nat e :: 17 word) = 2048 * j + e"
  by (simp add: unat_word_ariths unat_of_nat)

lemma encode_bit5:
  fixes fx :: "(1024, w64) seq" and e j :: nat
  assumes "e < 2048" "j < 32"
  shows "bit (seq_to_word (rev_seq (coerce_seq_len (map_seq (\<lambda>j. nth_end_list (seq_to_list (FFTEnc.flat5 fx)) (to_nat (0x800 * j + from_nat e)))
            (fromToLessThan TY(0) TY(32) TY((17, bool) seq)))) :: (32, bool) seq)) j
       = bit (seq_to_word (FFTEnc.flat5 fx)) (2048 * j + e)"
  using assms by (simp add: bit_s2w rev_seq.rep_eq coerce_seq_len.rep_eq map_seq_code seq_to_list.fromToLessThan rev_nth
      to_nat_seq_to_word plus_seq_conv times_seq_conv seq_to_word.from_nat from_nat_word numeral_seq_word_conv idx17)

theorem encodeIdx5_gf:
  fixes fx :: "(1024, w64) seq"
  assumes e: "e < 2048"
  shows "gfw (seq_to_word (nth_seq (FFTEnc.encodeIdx5 fx) e))
       = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat5 fx)) (2048 * j + e) then X j (beta 32) else 0)"
proof -
  define V where "V = (rev_seq (coerce_seq_len (map_seq (\<lambda>j. nth_end_list (seq_to_list (FFTEnc.flat5 fx)) (to_nat (0x800 * j + from_nat e)))
            (fromToLessThan TY(0) TY(32) TY((17, bool) seq)))) :: (32, bool) seq)"
  have nt: "nth_seq (FFTEnc.encodeIdx5 fx) e = FFTEnc.linmap TY(32) FFTEnc.encMat V"
    using e by (simp add: FFTEnc.encodeIdx5_def Let_def seq_to_list nth_seq.rep_eq V_def)
  have "gfw (seq_to_word (nth_seq (FFTEnc.encodeIdx5 fx) e))
      = sum_list (map gfw (map (\<lambda>j. if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0) [0..<32]))"
    by (simp add: nt linmap_word gfw_foldl_xor)
  also have "\<dots> = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat5 fx)) (2048 * j + e) then X j (beta 32) else 0)"
  proof -
    have pt: "\<And>j. j < 32 \<Longrightarrow> gfw (if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0)
            = (if bit (seq_to_word (FFTEnc.flat5 fx)) (2048 * j + e) then X j (beta 32) else 0)"
      using e by (simp add: V_def encode_bit5 encw_nth enc_x)
    have "sum_list (map gfw (map (\<lambda>j. if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0) [0..<32]))
        = (\<Sum>j\<in>{0..<32}. gfw (if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0))"
      by (simp only: map_map sum_set_upt_conv_sum_list_nat[symmetric] set_upt comp_def)
    also have "\<dots> = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat5 fx)) (2048 * j + e) then X j (beta 32) else 0)"
      by (simp only: atLeast0LessThan) (rule sum.cong, rule refl, simp add: pt)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed


lemma idx17m: "p < 131072 \<Longrightarrow> to_nat (from_nat p mod 0x800 :: (17, bool) seq) = p mod 2048"
  and idx17d: "p < 131072 \<Longrightarrow> to_nat (from_nat p div 0x800 :: (17, bool) seq) = p div 2048"
  by (simp_all add: to_nat_seq_to_word word_seq_convs seq_to_word.from_nat unat_word_ariths unat_of_nat
      unat_mod unat_div from_nat_word unat_of_nat_eq)

lemma decodeIdx5_bit:
  fixes fx :: "(2048, w64) seq"
  assumes p: "p < 131072"
  shows "bitsof (L (FFTEnc.decodeIdx5 fx)) p
       = bit (seq_to_word (FFTEnc.linmap TY(64) FFTEnc.decMat (nth_seq fx (p mod 2048)))) (p div 2048)"
proof -
  define bf where "bf = (\<lambda>p::nat. nth_end_list (seq_to_list (nth_list (map (FFTEnc.linmap TY(64) FFTEnc.decMat) (seq_to_list fx))
                           (to_nat (from_nat p mod 0x800 :: (17, bool) seq)))) (to_nat (from_nat p div 0x800 :: (17, bool) seq)))"
  define BL where "BL = map bf [0..<131072]"
  define G where "G = group_list 2048 64 (rev BL)"
  have lBL: "length (rev BL) = 2048 * 64" by (simp add: BL_def)
  have sl: "seq_to_list (FFTEnc.decodeIdx5 fx) = rev (map list_to_seq G)"
    by (simp add: FFTEnc.decodeIdx5_def Let_def FFTEnc.unflat25_def seq_to_list G_def BL_def bf_def comp_def)
  define i where "i = p div 64"
  define r where "r = p mod 64"
  have i: "i < 2048" using p by (simp add: i_def)
  have r: "r < 64" by (simp add: r_def)
  have pir: "p = 64 * i + r" by (simp add: i_def r_def)
  have lg: "length (G ! (2047 - i)) = 64" using i lBL by (simp add: G_def)
  have "L (FFTEnc.decodeIdx5 fx) ! i = seq_to_word (list_to_seq (G ! (2047 - i)) :: w64)"
    using i by (simp add: L_def sl rev_nth G_def)
  then have "bitsof (L (FFTEnc.decodeIdx5 fx)) p = bit (seq_to_word (list_to_seq (G ! (2047 - i)) :: w64)) r"
    using i by (simp add: bitsof_def L_def i_def r_def)
  also have "\<dots> = (G ! (2047 - i)) ! (63 - r)"
    using r lg by (simp add: bit_s2w)
  also have "\<dots> = rev BL ! ((2047 - i) * 64 + (63 - r))"
    using i r lBL by (simp add: G_def group_list_elem)
  also have "\<dots> = BL ! p"
  proof -
    have "(2047 - i) * 64 + (63 - r) < length BL" using i r by (simp add: BL_def)
    moreover have "length BL - Suc ((2047 - i) * 64 + (63 - r)) = p" using i r pir by (simp add: BL_def)
    ultimately show ?thesis by (simp add: rev_nth)
  qed
  also have "\<dots> = bf p" using p by (simp add: BL_def)
  also have "\<dots> = bit (seq_to_word (FFTEnc.linmap TY(64) FFTEnc.decMat (nth_seq fx (p mod 2048)))) (p div 2048)"
  proof -
    have pm: "p mod 2048 < 2048" by simp
    have pd: "p div 2048 < 64" using p by simp
    show ?thesis using p pm pd by (simp add: bf_def idx17m idx17d bit_s2w nth_seq.rep_eq)
  qed
  finally show ?thesis .
qed


lemma flat5_list: "seq_to_list (FFTEnc.flat5 (fx :: (1024, w64) seq)) = concat (map seq_to_list (rev (seq_to_list fx)))"
  by (simp add: FFTEnc.flat5_def seq_to_list)

theorem flat5_as64: "seq_to_list (FFTEnc.flat5 (FFTTop.as64 TY(1024) y)) = seq_to_list (FFTBC.flat32 TY(2 \<times> 1024) y)"
proof -
  define G where "G = group_list 1024 2 (seq_to_list y)"
  have g: "\<forall>x\<in>set G. length x = 2"
    using group_list_grouped[of "seq_to_list y" 1024 2] by (simp add: G_def)
  have cG: "concat G = seq_to_list y" by (simp add: G_def concat_group_list_inv)
  have "seq_to_list (FFTEnc.flat5 (FFTTop.as64 TY(1024) y)) = concat (rev (map (\<lambda>g. seq_to_list (g ! Suc 0) @ seq_to_list (g ! 0)) G))"
    by (simp add: flat5_list as64_list G_def[symmetric] rev_map comp_def seq_to_list.append_seq)
  also have "\<dots> = concat (map seq_to_list (rev (concat G)))" by (rule concat_rev_pairs[OF g])
  also have "\<dots> = seq_to_list (FFTBC.flat32 TY(2 \<times> 1024) y)" by (simp add: flat32_list cG)
  finally show ?thesis .
qed

end
