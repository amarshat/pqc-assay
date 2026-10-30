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

definition decok :: "nat \<Rightarrow> bool" where "decok j \<longleftrightarrow> linw decw (encw ! j) = 2 ^ j"

lemma decall_0: "\<forall>j<(0::nat). decok j" by simp
lemma decall_1: "\<forall>j<(1::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 1"
  then have "j < 0 \<or> j = 0" by linarith
  moreover have "decok 0" unfolding decok_def by (rule dec_enc_0)
  ultimately show "decok j" using decall_0 by auto
qed
lemma decall_2: "\<forall>j<(2::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 2"
  then have "j < 1 \<or> j = 1" by linarith
  moreover have "decok 1" unfolding decok_def by (rule dec_enc_1)
  ultimately show "decok j" using decall_1 by auto
qed
lemma decall_3: "\<forall>j<(3::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 3"
  then have "j < 2 \<or> j = 2" by linarith
  moreover have "decok 2" unfolding decok_def by (rule dec_enc_2)
  ultimately show "decok j" using decall_2 by auto
qed
lemma decall_4: "\<forall>j<(4::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 4"
  then have "j < 3 \<or> j = 3" by linarith
  moreover have "decok 3" unfolding decok_def by (rule dec_enc_3)
  ultimately show "decok j" using decall_3 by auto
qed
lemma decall_5: "\<forall>j<(5::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 5"
  then have "j < 4 \<or> j = 4" by linarith
  moreover have "decok 4" unfolding decok_def by (rule dec_enc_4)
  ultimately show "decok j" using decall_4 by auto
qed
lemma decall_6: "\<forall>j<(6::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 6"
  then have "j < 5 \<or> j = 5" by linarith
  moreover have "decok 5" unfolding decok_def by (rule dec_enc_5)
  ultimately show "decok j" using decall_5 by auto
qed
lemma decall_7: "\<forall>j<(7::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 7"
  then have "j < 6 \<or> j = 6" by linarith
  moreover have "decok 6" unfolding decok_def by (rule dec_enc_6)
  ultimately show "decok j" using decall_6 by auto
qed
lemma decall_8: "\<forall>j<(8::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 8"
  then have "j < 7 \<or> j = 7" by linarith
  moreover have "decok 7" unfolding decok_def by (rule dec_enc_7)
  ultimately show "decok j" using decall_7 by auto
qed
lemma decall_9: "\<forall>j<(9::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 9"
  then have "j < 8 \<or> j = 8" by linarith
  moreover have "decok 8" unfolding decok_def by (rule dec_enc_8)
  ultimately show "decok j" using decall_8 by auto
qed
lemma decall_10: "\<forall>j<(10::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 10"
  then have "j < 9 \<or> j = 9" by linarith
  moreover have "decok 9" unfolding decok_def by (rule dec_enc_9)
  ultimately show "decok j" using decall_9 by auto
qed
lemma decall_11: "\<forall>j<(11::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 11"
  then have "j < 10 \<or> j = 10" by linarith
  moreover have "decok 10" unfolding decok_def by (rule dec_enc_10)
  ultimately show "decok j" using decall_10 by auto
qed
lemma decall_12: "\<forall>j<(12::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 12"
  then have "j < 11 \<or> j = 11" by linarith
  moreover have "decok 11" unfolding decok_def by (rule dec_enc_11)
  ultimately show "decok j" using decall_11 by auto
qed
lemma decall_13: "\<forall>j<(13::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 13"
  then have "j < 12 \<or> j = 12" by linarith
  moreover have "decok 12" unfolding decok_def by (rule dec_enc_12)
  ultimately show "decok j" using decall_12 by auto
qed
lemma decall_14: "\<forall>j<(14::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 14"
  then have "j < 13 \<or> j = 13" by linarith
  moreover have "decok 13" unfolding decok_def by (rule dec_enc_13)
  ultimately show "decok j" using decall_13 by auto
qed
lemma decall_15: "\<forall>j<(15::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 15"
  then have "j < 14 \<or> j = 14" by linarith
  moreover have "decok 14" unfolding decok_def by (rule dec_enc_14)
  ultimately show "decok j" using decall_14 by auto
qed
lemma decall_16: "\<forall>j<(16::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 16"
  then have "j < 15 \<or> j = 15" by linarith
  moreover have "decok 15" unfolding decok_def by (rule dec_enc_15)
  ultimately show "decok j" using decall_15 by auto
qed
lemma decall_17: "\<forall>j<(17::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 17"
  then have "j < 16 \<or> j = 16" by linarith
  moreover have "decok 16" unfolding decok_def by (rule dec_enc_16)
  ultimately show "decok j" using decall_16 by auto
qed
lemma decall_18: "\<forall>j<(18::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 18"
  then have "j < 17 \<or> j = 17" by linarith
  moreover have "decok 17" unfolding decok_def by (rule dec_enc_17)
  ultimately show "decok j" using decall_17 by auto
qed
lemma decall_19: "\<forall>j<(19::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 19"
  then have "j < 18 \<or> j = 18" by linarith
  moreover have "decok 18" unfolding decok_def by (rule dec_enc_18)
  ultimately show "decok j" using decall_18 by auto
qed
lemma decall_20: "\<forall>j<(20::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 20"
  then have "j < 19 \<or> j = 19" by linarith
  moreover have "decok 19" unfolding decok_def by (rule dec_enc_19)
  ultimately show "decok j" using decall_19 by auto
qed
lemma decall_21: "\<forall>j<(21::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 21"
  then have "j < 20 \<or> j = 20" by linarith
  moreover have "decok 20" unfolding decok_def by (rule dec_enc_20)
  ultimately show "decok j" using decall_20 by auto
qed
lemma decall_22: "\<forall>j<(22::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 22"
  then have "j < 21 \<or> j = 21" by linarith
  moreover have "decok 21" unfolding decok_def by (rule dec_enc_21)
  ultimately show "decok j" using decall_21 by auto
qed
lemma decall_23: "\<forall>j<(23::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 23"
  then have "j < 22 \<or> j = 22" by linarith
  moreover have "decok 22" unfolding decok_def by (rule dec_enc_22)
  ultimately show "decok j" using decall_22 by auto
qed
lemma decall_24: "\<forall>j<(24::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 24"
  then have "j < 23 \<or> j = 23" by linarith
  moreover have "decok 23" unfolding decok_def by (rule dec_enc_23)
  ultimately show "decok j" using decall_23 by auto
qed
lemma decall_25: "\<forall>j<(25::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 25"
  then have "j < 24 \<or> j = 24" by linarith
  moreover have "decok 24" unfolding decok_def by (rule dec_enc_24)
  ultimately show "decok j" using decall_24 by auto
qed
lemma decall_26: "\<forall>j<(26::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 26"
  then have "j < 25 \<or> j = 25" by linarith
  moreover have "decok 25" unfolding decok_def by (rule dec_enc_25)
  ultimately show "decok j" using decall_25 by auto
qed
lemma decall_27: "\<forall>j<(27::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 27"
  then have "j < 26 \<or> j = 26" by linarith
  moreover have "decok 26" unfolding decok_def by (rule dec_enc_26)
  ultimately show "decok j" using decall_26 by auto
qed
lemma decall_28: "\<forall>j<(28::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 28"
  then have "j < 27 \<or> j = 27" by linarith
  moreover have "decok 27" unfolding decok_def by (rule dec_enc_27)
  ultimately show "decok j" using decall_27 by auto
qed
lemma decall_29: "\<forall>j<(29::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 29"
  then have "j < 28 \<or> j = 28" by linarith
  moreover have "decok 28" unfolding decok_def by (rule dec_enc_28)
  ultimately show "decok j" using decall_28 by auto
qed
lemma decall_30: "\<forall>j<(30::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 30"
  then have "j < 29 \<or> j = 29" by linarith
  moreover have "decok 29" unfolding decok_def by (rule dec_enc_29)
  ultimately show "decok j" using decall_29 by auto
qed
lemma decall_31: "\<forall>j<(31::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 31"
  then have "j < 30 \<or> j = 30" by linarith
  moreover have "decok 30" unfolding decok_def by (rule dec_enc_30)
  ultimately show "decok j" using decall_30 by auto
qed
lemma decall_32: "\<forall>j<(32::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 32"
  then have "j < 31 \<or> j = 31" by linarith
  moreover have "decok 31" unfolding decok_def by (rule dec_enc_31)
  ultimately show "decok j" using decall_31 by auto
qed
lemma decall_33: "\<forall>j<(33::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 33"
  then have "j < 32 \<or> j = 32" by linarith
  moreover have "decok 32" unfolding decok_def by (rule dec_enc_32)
  ultimately show "decok j" using decall_32 by auto
qed
lemma decall_34: "\<forall>j<(34::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 34"
  then have "j < 33 \<or> j = 33" by linarith
  moreover have "decok 33" unfolding decok_def by (rule dec_enc_33)
  ultimately show "decok j" using decall_33 by auto
qed
lemma decall_35: "\<forall>j<(35::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 35"
  then have "j < 34 \<or> j = 34" by linarith
  moreover have "decok 34" unfolding decok_def by (rule dec_enc_34)
  ultimately show "decok j" using decall_34 by auto
qed
lemma decall_36: "\<forall>j<(36::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 36"
  then have "j < 35 \<or> j = 35" by linarith
  moreover have "decok 35" unfolding decok_def by (rule dec_enc_35)
  ultimately show "decok j" using decall_35 by auto
qed
lemma decall_37: "\<forall>j<(37::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 37"
  then have "j < 36 \<or> j = 36" by linarith
  moreover have "decok 36" unfolding decok_def by (rule dec_enc_36)
  ultimately show "decok j" using decall_36 by auto
qed
lemma decall_38: "\<forall>j<(38::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 38"
  then have "j < 37 \<or> j = 37" by linarith
  moreover have "decok 37" unfolding decok_def by (rule dec_enc_37)
  ultimately show "decok j" using decall_37 by auto
qed
lemma decall_39: "\<forall>j<(39::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 39"
  then have "j < 38 \<or> j = 38" by linarith
  moreover have "decok 38" unfolding decok_def by (rule dec_enc_38)
  ultimately show "decok j" using decall_38 by auto
qed
lemma decall_40: "\<forall>j<(40::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 40"
  then have "j < 39 \<or> j = 39" by linarith
  moreover have "decok 39" unfolding decok_def by (rule dec_enc_39)
  ultimately show "decok j" using decall_39 by auto
qed
lemma decall_41: "\<forall>j<(41::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 41"
  then have "j < 40 \<or> j = 40" by linarith
  moreover have "decok 40" unfolding decok_def by (rule dec_enc_40)
  ultimately show "decok j" using decall_40 by auto
qed
lemma decall_42: "\<forall>j<(42::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 42"
  then have "j < 41 \<or> j = 41" by linarith
  moreover have "decok 41" unfolding decok_def by (rule dec_enc_41)
  ultimately show "decok j" using decall_41 by auto
qed
lemma decall_43: "\<forall>j<(43::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 43"
  then have "j < 42 \<or> j = 42" by linarith
  moreover have "decok 42" unfolding decok_def by (rule dec_enc_42)
  ultimately show "decok j" using decall_42 by auto
qed
lemma decall_44: "\<forall>j<(44::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 44"
  then have "j < 43 \<or> j = 43" by linarith
  moreover have "decok 43" unfolding decok_def by (rule dec_enc_43)
  ultimately show "decok j" using decall_43 by auto
qed
lemma decall_45: "\<forall>j<(45::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 45"
  then have "j < 44 \<or> j = 44" by linarith
  moreover have "decok 44" unfolding decok_def by (rule dec_enc_44)
  ultimately show "decok j" using decall_44 by auto
qed
lemma decall_46: "\<forall>j<(46::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 46"
  then have "j < 45 \<or> j = 45" by linarith
  moreover have "decok 45" unfolding decok_def by (rule dec_enc_45)
  ultimately show "decok j" using decall_45 by auto
qed
lemma decall_47: "\<forall>j<(47::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 47"
  then have "j < 46 \<or> j = 46" by linarith
  moreover have "decok 46" unfolding decok_def by (rule dec_enc_46)
  ultimately show "decok j" using decall_46 by auto
qed
lemma decall_48: "\<forall>j<(48::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 48"
  then have "j < 47 \<or> j = 47" by linarith
  moreover have "decok 47" unfolding decok_def by (rule dec_enc_47)
  ultimately show "decok j" using decall_47 by auto
qed
lemma decall_49: "\<forall>j<(49::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 49"
  then have "j < 48 \<or> j = 48" by linarith
  moreover have "decok 48" unfolding decok_def by (rule dec_enc_48)
  ultimately show "decok j" using decall_48 by auto
qed
lemma decall_50: "\<forall>j<(50::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 50"
  then have "j < 49 \<or> j = 49" by linarith
  moreover have "decok 49" unfolding decok_def by (rule dec_enc_49)
  ultimately show "decok j" using decall_49 by auto
qed
lemma decall_51: "\<forall>j<(51::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 51"
  then have "j < 50 \<or> j = 50" by linarith
  moreover have "decok 50" unfolding decok_def by (rule dec_enc_50)
  ultimately show "decok j" using decall_50 by auto
qed
lemma decall_52: "\<forall>j<(52::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 52"
  then have "j < 51 \<or> j = 51" by linarith
  moreover have "decok 51" unfolding decok_def by (rule dec_enc_51)
  ultimately show "decok j" using decall_51 by auto
qed
lemma decall_53: "\<forall>j<(53::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 53"
  then have "j < 52 \<or> j = 52" by linarith
  moreover have "decok 52" unfolding decok_def by (rule dec_enc_52)
  ultimately show "decok j" using decall_52 by auto
qed
lemma decall_54: "\<forall>j<(54::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 54"
  then have "j < 53 \<or> j = 53" by linarith
  moreover have "decok 53" unfolding decok_def by (rule dec_enc_53)
  ultimately show "decok j" using decall_53 by auto
qed
lemma decall_55: "\<forall>j<(55::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 55"
  then have "j < 54 \<or> j = 54" by linarith
  moreover have "decok 54" unfolding decok_def by (rule dec_enc_54)
  ultimately show "decok j" using decall_54 by auto
qed
lemma decall_56: "\<forall>j<(56::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 56"
  then have "j < 55 \<or> j = 55" by linarith
  moreover have "decok 55" unfolding decok_def by (rule dec_enc_55)
  ultimately show "decok j" using decall_55 by auto
qed
lemma decall_57: "\<forall>j<(57::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 57"
  then have "j < 56 \<or> j = 56" by linarith
  moreover have "decok 56" unfolding decok_def by (rule dec_enc_56)
  ultimately show "decok j" using decall_56 by auto
qed
lemma decall_58: "\<forall>j<(58::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 58"
  then have "j < 57 \<or> j = 57" by linarith
  moreover have "decok 57" unfolding decok_def by (rule dec_enc_57)
  ultimately show "decok j" using decall_57 by auto
qed
lemma decall_59: "\<forall>j<(59::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 59"
  then have "j < 58 \<or> j = 58" by linarith
  moreover have "decok 58" unfolding decok_def by (rule dec_enc_58)
  ultimately show "decok j" using decall_58 by auto
qed
lemma decall_60: "\<forall>j<(60::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 60"
  then have "j < 59 \<or> j = 59" by linarith
  moreover have "decok 59" unfolding decok_def by (rule dec_enc_59)
  ultimately show "decok j" using decall_59 by auto
qed
lemma decall_61: "\<forall>j<(61::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 61"
  then have "j < 60 \<or> j = 60" by linarith
  moreover have "decok 60" unfolding decok_def by (rule dec_enc_60)
  ultimately show "decok j" using decall_60 by auto
qed
lemma decall_62: "\<forall>j<(62::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 62"
  then have "j < 61 \<or> j = 61" by linarith
  moreover have "decok 61" unfolding decok_def by (rule dec_enc_61)
  ultimately show "decok j" using decall_61 by auto
qed
lemma decall_63: "\<forall>j<(63::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 63"
  then have "j < 62 \<or> j = 62" by linarith
  moreover have "decok 62" unfolding decok_def by (rule dec_enc_62)
  ultimately show "decok j" using decall_62 by auto
qed
lemma decall_64: "\<forall>j<(64::nat). decok j"
proof (intro allI impI)
  fix j :: nat assume "j < 64"
  then have "j < 63 \<or> j = 63" by linarith
  moreover have "decok 63" unfolding decok_def by (rule dec_enc_63)
  ultimately show "decok j" using decall_63 by auto
qed

lemma dec_enc: "j < 64 \<Longrightarrow> linw decw (encw ! j) = 2 ^ j"
  using decall_64 by (simp add: decok_def)

definition encword :: "(nat \<Rightarrow> bool) \<Rightarrow> 64 word" where
  "encword c = foldl (XOR) 0 (map (\<lambda>j. if c j then encw ! j else 0) [0..<64])"

lemma linw_foldl: "linw m (foldl (XOR) 0 (map g xs)) = foldl (XOR) 0 (map (\<lambda>j. linw m (g j)) xs)"
  by (induction xs rule: rev_induct) (simp_all add: linw_xor)

lemma bit_foldl_pow: "bit (foldl (XOR) (0 :: 64 word) (map (\<lambda>j. if c j then 2 ^ j else 0) [0..<n])) t \<longleftrightarrow> t < n \<and> t < 64 \<and> c t"
  by (induction n) (auto simp: bit_xor_iff bit_exp_iff less_Suc_eq)

theorem decode_encword: "t < 64 \<Longrightarrow> bit (linw decw (encword c)) t = c t"
proof -
  assume t: "t < 64"
  have "linw decw (encword c) = foldl (XOR) 0 (map (\<lambda>j. linw decw (if c j then encw ! j else 0)) [0..<64])"
    by (simp add: encword_def linw_foldl)
  also have "\<dots> = foldl (XOR) 0 (map (\<lambda>j. if c j then 2 ^ j else 0) [0..<64])"
    by (rule arg_cong[where f="foldl (XOR) 0"], rule map_cong) (simp_all add: dec_enc)
  finally show ?thesis using t by (simp add: bit_foldl_pow)
qed

theorem gfw_encword: "gfw (encword c) = (\<Sum>j<64. (if c j then X j (beta 32) else 0))"
proof -
  have "gfw (encword c) = sum_list (map gfw (map (\<lambda>j. if c j then encw ! j else 0) [0..<64]))"
    by (simp add: encword_def gfw_foldl_xor)
  also have "\<dots> = (\<Sum>j\<in>{0..<64}. gfw (if c j then encw ! j else 0))"
    by (simp only: map_map sum_set_upt_conv_sum_list_nat[symmetric] set_upt comp_def)
  also have "\<dots> = (\<Sum>j<64. (if c j then X j (beta 32) else 0))"
    by (simp only: atLeast0LessThan) (rule sum.cong, rule refl, simp add: enc_x)
  finally show ?thesis .
qed

end
