theory DecBridge
  imports Hom HQC_FFT_Const.DecConst
begin

lemma idx15: "p < 32768 \<Longrightarrow> to_nat (from_nat p mod 0x200 :: (15, bool) seq) = p mod 512"
  and idx15d: "p < 32768 \<Longrightarrow> to_nat (from_nat p div 0x200 :: (15, bool) seq) = p div 512"
  by (simp_all add: to_nat_seq_to_word word_seq_convs seq_to_word.from_nat unat_word_ariths unat_of_nat
      unat_mod unat_div from_nat_word unat_of_nat_eq)

lemma decodeIdx_bit:
  fixes fx :: "(512, w64) seq"
  assumes p: "p < 32768"
  shows "bitsof (L (FFTEnc.decodeIdx fx)) p
       = bit (seq_to_word (FFTEnc.linmap TY(64) FFTEnc.decMat (nth_seq fx (p mod 512)))) (p div 512)"
proof -
  define bf where "bf = (\<lambda>p::nat. nth_end_list (seq_to_list (nth_list (map (FFTEnc.linmap TY(64) FFTEnc.decMat) (seq_to_list fx))
                           (to_nat (from_nat p mod 0x200 :: (15, bool) seq)))) (to_nat (from_nat p div 0x200 :: (15, bool) seq)))"
  define BL where "BL = map bf [0..<32768]"
  define G where "G = group_list 512 64 (rev BL)"
  have lBL: "length (rev BL) = 512 * 64" by (simp add: BL_def)
  have sl: "seq_to_list (FFTEnc.decodeIdx fx) = rev (map list_to_seq G)"
    by (simp add: FFTEnc.decodeIdx_def Let_def FFTEnc.unflat2_def seq_to_list G_def BL_def bf_def comp_def)
  define i where "i = p div 64"
  define r where "r = p mod 64"
  have i: "i < 512" using p by (simp add: i_def)
  have r: "r < 64" by (simp add: r_def)
  have pir: "p = 64 * i + r" by (simp add: i_def r_def)
  have lg: "length (G ! (511 - i)) = 64" using i lBL by (simp add: G_def)
  have "L (FFTEnc.decodeIdx fx) ! i = seq_to_word (list_to_seq (G ! (511 - i)) :: w64)"
    using i by (simp add: L_def sl rev_nth G_def)
  then have "bitsof (L (FFTEnc.decodeIdx fx)) p = bit (seq_to_word (list_to_seq (G ! (511 - i)) :: w64)) r"
    using i by (simp add: bitsof_def L_def i_def r_def)
  also have "\<dots> = (G ! (511 - i)) ! (63 - r)"
    using r lg by (simp add: bit_s2w)
  also have "\<dots> = rev BL ! ((511 - i) * 64 + (63 - r))"
    using i r lBL by (simp add: G_def group_list_elem)
  also have "\<dots> = BL ! p"
  proof -
    have "(511 - i) * 64 + (63 - r) < length BL" using i r by (simp add: BL_def)
    moreover have "length BL - Suc ((511 - i) * 64 + (63 - r)) = p" using i r pir by (simp add: BL_def)
    ultimately show ?thesis by (simp add: rev_nth)
  qed
  also have "\<dots> = bf p" using p by (simp add: BL_def)
  also have "\<dots> = bit (seq_to_word (FFTEnc.linmap TY(64) FFTEnc.decMat (nth_seq fx (p mod 512)))) (p div 512)"
  proof -
    have pm: "p mod 512 < 512" by simp
    have pd: "p div 512 < 64" using p by simp
    show ?thesis using p pm pd by (simp add: bf_def idx15 idx15d bit_s2w nth_seq.rep_eq)
  qed
  finally show ?thesis .
qed

lemma linmap64_word:
  fixes mat :: "(64, w64) seq" and v :: "(64, bool) seq"
  shows "seq_to_word (FFTEnc.linmap TY(64) mat v)
       = foldl (XOR) 0 (map (\<lambda>j. if bit (seq_to_word v) j then seq_to_word (nth_seq mat j) else 0) [0..<64])"
proof -
  have "seq_to_word (FFTEnc.linmap TY(64) mat v) = foldl (XOR) 0
      (map (seq_to_word \<circ> ((\<lambda>j. if if pos_nat j < 64 then seq_to_word v !! (LENGTH(64) - Suc (LENGTH(64) - Suc (pos_nat j)))
                                   else oob_seq_elem (rev_seq v) then nth_seq mat (pos_nat j) else 0) \<circ> int)) [0..<64])"
    by (simp add: FFTEnc.linmap_def word_seq_convs foldl_seq.rep_eq seq_to_list.fromToLessThan s2w_foldl_xor seq_to_list.map_seq)
  also have "\<dots> = foldl (XOR) 0 (map (\<lambda>j. if bit (seq_to_word v) j then seq_to_word (nth_seq mat j) else 0) [0..<64])"
    by (intro arg_cong[where f="foldl (XOR) 0"] map_cong refl) (auto simp: seq_to_word.zero)
  finally show ?thesis .
qed

lemma decw_nth: "j < 64 \<Longrightarrow> seq_to_word (nth_seq FFTEnc.decMat j) = decw ! j"
proof -
  assume j: "j < 64"
  have "decw ! j = map seq_to_word (seq_to_list FFTEnc.decMat) ! j" using decw_lifted by (simp add: L_def)
  also have "\<dots> = seq_to_word (seq_to_list FFTEnc.decMat ! j)" using j by simp
  finally show ?thesis using j by (simp add: nth_seq.rep_eq)
qed

lemma linmap_dec: "seq_to_word (FFTEnc.linmap TY(64) FFTEnc.decMat v) = linw decw (seq_to_word v)"
  unfolding linmap64_word linw_def
  by (rule arg_cong[where f="foldl (XOR) 0"], rule map_cong) (simp_all add: decw_nth)

lemma linw_xor: "linw m (a XOR b) = linw m a XOR linw m b"
proof -
  have "foldl (XOR) 0 (map (\<lambda>j. if bit (a XOR b) j then m ! j else 0) xs)
      = foldl (XOR) 0 (map (\<lambda>j. if bit a j then m ! j else 0) xs) XOR foldl (XOR) 0 (map (\<lambda>j. if bit b j then m ! j else 0) xs)"
    for xs :: "nat list"
  proof (induction xs rule: rev_induct)
    case Nil then show ?case by simp
  next
    case (snoc x xs)
    then show ?case by (auto simp: bit_xor_iff ac_simps)
  qed
  then show ?thesis by (simp add: linw_def)
qed

lemma foldl_xor_zero: "foldl (XOR) (0 :: 'a::len word) (map (\<lambda>j. 0) xs) = 0"
  by (induction xs rule: rev_induct) simp_all

lemma linw_zero [simp]: "linw m 0 = 0"
  by (simp add: linw_def foldl_xor_zero)

end
