theory EncBridge
  imports BtfyBridge HQC_FFT_Const.EncConst
begin

lemma linmap_word:
  fixes mat :: "(64, w64) seq" and v :: "(32, bool) seq"
  shows "seq_to_word (FFTEnc.linmap TY(32) mat v)
       = foldl (XOR) 0 (map (\<lambda>j. if bit (seq_to_word v) j then seq_to_word (nth_seq mat j) else 0) [0..<32])"
proof -
  have "seq_to_word (FFTEnc.linmap TY(32) mat v) = foldl (XOR) 0
      (map (seq_to_word \<circ> ((\<lambda>j. if if pos_nat j < 32 then seq_to_word v !! (LENGTH(32) - Suc (LENGTH(32) - Suc (pos_nat j)))
                                   else oob_seq_elem (rev_seq v) then nth_seq mat (pos_nat j) else 0) \<circ> int)) [0..<32])"
    by (simp add: FFTEnc.linmap_def word_seq_convs foldl_seq.rep_eq seq_to_list.fromToLessThan s2w_foldl_xor seq_to_list.map_seq)
  also have "\<dots> = foldl (XOR) 0 (map (\<lambda>j. if bit (seq_to_word v) j then seq_to_word (nth_seq mat j) else 0) [0..<32])"
    by (intro arg_cong[where f="foldl (XOR) 0"] map_cong refl) (auto simp: seq_to_word.zero)
  finally show ?thesis .
qed

lemma idx14: "j < 32 \<Longrightarrow> e < 512 \<Longrightarrow> unat (512 * word_of_nat j + word_of_nat e :: 14 word) = 512 * j + e"
  by (simp add: unat_word_ariths unat_of_nat)

lemma encode_bit:
  fixes fx :: "(256, w64) seq" and e j :: nat
  assumes "e < 512" "j < 32"
  shows "bit (seq_to_word (rev_seq (coerce_seq_len (map_seq (\<lambda>j. nth_end_list (seq_to_list (FFTEnc.flat fx)) (to_nat (0x200 * j + from_nat e)))
            (fromToLessThan TY(0) TY(32) TY((14, bool) seq)))) :: (32, bool) seq)) j
       = bit (seq_to_word (FFTEnc.flat fx)) (512 * j + e)"
  using assms by (simp add: bit_s2w rev_seq.rep_eq coerce_seq_len.rep_eq map_seq_code seq_to_list.fromToLessThan rev_nth
      to_nat_seq_to_word plus_seq_conv times_seq_conv seq_to_word.from_nat from_nat_word numeral_seq_word_conv idx14)

lemma encw_nth: "j < 64 \<Longrightarrow> seq_to_word (nth_seq FFTEnc.encMat j) = encw ! j"
proof -
  assume j: "j < 64"
  have "encw ! j = map seq_to_word (seq_to_list FFTEnc.encMat) ! j" using encw_lifted by (simp add: L_def)
  also have "\<dots> = seq_to_word (seq_to_list FFTEnc.encMat ! j)" using j by simp
  finally show ?thesis using j by (simp add: nth_seq.rep_eq)
qed

lemma beta32: "Cantor.cantor beta (2 ^ 32) = beta 32"
proof -
  have "Cantor.cantor beta (2 ^ 32) = (\<Sum>i<64. if bit ((2::nat) ^ 32) i then beta i else 0)"
    by (rule Cantor.cantor_sum) simp
  also have "\<dots> = beta 32" unfolding bit_exp_iff by (simp add: if_distrib cong: if_cong)
  finally show ?thesis .
qed

lemma sv_beta32: "t \<le> 32 \<Longrightarrow> sv t (beta 32) = beta (32 - t)"
proof -
  assume t: "t \<le> 32"
  have "sv t (beta 32) = sv t (Cantor.cantor beta (2 ^ 32))" by (simp only: beta32)
  also have "\<dots> = Cantor.cantor beta (2 ^ 32 div 2 ^ t)" by (rule sv_cantor[OF beta_cantor]) simp
  also have "2 ^ 32 div 2 ^ t = (2::nat) ^ (32 - t)" using t by (simp add: power_diff)
  also have "Cantor.cantor beta (2 ^ (32 - t)) = beta (32 - t)"
  proof -
    have "Cantor.cantor beta (2 ^ (32 - t)) = (\<Sum>i<64. if bit ((2::nat) ^ (32 - t)) i then beta i else 0)"
    proof (rule Cantor.cantor_sum)
      have "(2::nat) ^ (32 - t) \<le> 2 ^ 32" by (intro power_increasing) simp_all
      then show "(2::nat) ^ (32 - t) < 2 ^ 64" by simp
    qed
    also have "\<dots> = beta (32 - t)" using t unfolding bit_exp_iff by (simp add: if_distrib cong: if_cong)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

lemma lsb_Suc0: "bit (Suc 0 :: nat) 0"
  by (simp add: bit_0)

lemma X_beta32: "j < 64 \<Longrightarrow> X j (beta 32) = (\<Prod>t<6. if bit j t then beta (32 - t) else 1)"
  by (simp add: X_prod[of j 6] sv_beta32 cong: if_cong)

lemma enc_x_0: "gfw (encw ! 0) = X 0 (beta 32)"
  using enc_row_0 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_1: "gfw (encw ! 1) = X 1 (beta 32)"
  using enc_row_1 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_2: "gfw (encw ! 2) = X 2 (beta 32)"
  using enc_row_2 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_3: "gfw (encw ! 3) = X 3 (beta 32)"
  using enc_row_3 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_4: "gfw (encw ! 4) = X 4 (beta 32)"
  using enc_row_4 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_5: "gfw (encw ! 5) = X 5 (beta 32)"
  using enc_row_5 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_6: "gfw (encw ! 6) = X 6 (beta 32)"
  using enc_row_6 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_7: "gfw (encw ! 7) = X 7 (beta 32)"
  using enc_row_7 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_8: "gfw (encw ! 8) = X 8 (beta 32)"
  using enc_row_8 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_9: "gfw (encw ! 9) = X 9 (beta 32)"
  using enc_row_9 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_10: "gfw (encw ! 10) = X 10 (beta 32)"
  using enc_row_10 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_11: "gfw (encw ! 11) = X 11 (beta 32)"
  using enc_row_11 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_12: "gfw (encw ! 12) = X 12 (beta 32)"
  using enc_row_12 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_13: "gfw (encw ! 13) = X 13 (beta 32)"
  using enc_row_13 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_14: "gfw (encw ! 14) = X 14 (beta 32)"
  using enc_row_14 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_15: "gfw (encw ! 15) = X 15 (beta 32)"
  using enc_row_15 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_16: "gfw (encw ! 16) = X 16 (beta 32)"
  using enc_row_16 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_17: "gfw (encw ! 17) = X 17 (beta 32)"
  using enc_row_17 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_18: "gfw (encw ! 18) = X 18 (beta 32)"
  using enc_row_18 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_19: "gfw (encw ! 19) = X 19 (beta 32)"
  using enc_row_19 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_20: "gfw (encw ! 20) = X 20 (beta 32)"
  using enc_row_20 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_21: "gfw (encw ! 21) = X 21 (beta 32)"
  using enc_row_21 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_22: "gfw (encw ! 22) = X 22 (beta 32)"
  using enc_row_22 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_23: "gfw (encw ! 23) = X 23 (beta 32)"
  using enc_row_23 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_24: "gfw (encw ! 24) = X 24 (beta 32)"
  using enc_row_24 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_25: "gfw (encw ! 25) = X 25 (beta 32)"
  using enc_row_25 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_26: "gfw (encw ! 26) = X 26 (beta 32)"
  using enc_row_26 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_27: "gfw (encw ! 27) = X 27 (beta 32)"
  using enc_row_27 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_28: "gfw (encw ! 28) = X 28 (beta 32)"
  using enc_row_28 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_29: "gfw (encw ! 29) = X 29 (beta 32)"
  using enc_row_29 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_30: "gfw (encw ! 30) = X 30 (beta 32)"
  using enc_row_30 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_31: "gfw (encw ! 31) = X 31 (beta 32)"
  using enc_row_31 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)


lemma enc_x_32: "gfw (encw ! 32) = X 32 (beta 32)"
  using enc_row_32 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_33: "gfw (encw ! 33) = X 33 (beta 32)"
  using enc_row_33 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_34: "gfw (encw ! 34) = X 34 (beta 32)"
  using enc_row_34 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_35: "gfw (encw ! 35) = X 35 (beta 32)"
  using enc_row_35 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_36: "gfw (encw ! 36) = X 36 (beta 32)"
  using enc_row_36 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_37: "gfw (encw ! 37) = X 37 (beta 32)"
  using enc_row_37 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_38: "gfw (encw ! 38) = X 38 (beta 32)"
  using enc_row_38 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_39: "gfw (encw ! 39) = X 39 (beta 32)"
  using enc_row_39 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_40: "gfw (encw ! 40) = X 40 (beta 32)"
  using enc_row_40 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_41: "gfw (encw ! 41) = X 41 (beta 32)"
  using enc_row_41 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_42: "gfw (encw ! 42) = X 42 (beta 32)"
  using enc_row_42 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_43: "gfw (encw ! 43) = X 43 (beta 32)"
  using enc_row_43 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_44: "gfw (encw ! 44) = X 44 (beta 32)"
  using enc_row_44 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_45: "gfw (encw ! 45) = X 45 (beta 32)"
  using enc_row_45 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_46: "gfw (encw ! 46) = X 46 (beta 32)"
  using enc_row_46 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_47: "gfw (encw ! 47) = X 47 (beta 32)"
  using enc_row_47 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_48: "gfw (encw ! 48) = X 48 (beta 32)"
  using enc_row_48 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_49: "gfw (encw ! 49) = X 49 (beta 32)"
  using enc_row_49 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_50: "gfw (encw ! 50) = X 50 (beta 32)"
  using enc_row_50 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_51: "gfw (encw ! 51) = X 51 (beta 32)"
  using enc_row_51 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_52: "gfw (encw ! 52) = X 52 (beta 32)"
  using enc_row_52 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_53: "gfw (encw ! 53) = X 53 (beta 32)"
  using enc_row_53 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_54: "gfw (encw ! 54) = X 54 (beta 32)"
  using enc_row_54 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_55: "gfw (encw ! 55) = X 55 (beta 32)"
  using enc_row_55 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_56: "gfw (encw ! 56) = X 56 (beta 32)"
  using enc_row_56 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_57: "gfw (encw ! 57) = X 57 (beta 32)"
  using enc_row_57 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_58: "gfw (encw ! 58) = X 58 (beta 32)"
  using enc_row_58 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_59: "gfw (encw ! 59) = X 59 (beta 32)"
  using enc_row_59 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_60: "gfw (encw ! 60) = X 60 (beta 32)"
  using enc_row_60 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_61: "gfw (encw ! 61) = X 61 (beta 32)"
  using enc_row_61 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_62: "gfw (encw ! 62) = X 62 (beta 32)"
  using enc_row_62 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

lemma enc_x_63: "gfw (encw ! 63) = X 63 (beta 32)"
  using enc_row_63 by (simp add: X_beta32 lessThan_nat_numeral pred_numeral_simps lsb_Suc0 ac_simps)

definition encok :: "nat \<Rightarrow> bool" where "encok j \<longleftrightarrow> gfw (encw ! j) = X j (beta 32)"

lemma encall_0: "\<forall>j<(0::nat). encok j" by simp
lemma encall_1: "\<forall>j<(1::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 1"
  then have "j < 0 \<or> j = 0" by linarith
  moreover have "encok 0" unfolding encok_def by (rule enc_x_0)
  ultimately show "encok j" using encall_0 by auto
qed
lemma encall_2: "\<forall>j<(2::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 2"
  then have "j < 1 \<or> j = 1" by linarith
  moreover have "encok 1" unfolding encok_def by (rule enc_x_1)
  ultimately show "encok j" using encall_1 by auto
qed
lemma encall_3: "\<forall>j<(3::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 3"
  then have "j < 2 \<or> j = 2" by linarith
  moreover have "encok 2" unfolding encok_def by (rule enc_x_2)
  ultimately show "encok j" using encall_2 by auto
qed
lemma encall_4: "\<forall>j<(4::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 4"
  then have "j < 3 \<or> j = 3" by linarith
  moreover have "encok 3" unfolding encok_def by (rule enc_x_3)
  ultimately show "encok j" using encall_3 by auto
qed
lemma encall_5: "\<forall>j<(5::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 5"
  then have "j < 4 \<or> j = 4" by linarith
  moreover have "encok 4" unfolding encok_def by (rule enc_x_4)
  ultimately show "encok j" using encall_4 by auto
qed
lemma encall_6: "\<forall>j<(6::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 6"
  then have "j < 5 \<or> j = 5" by linarith
  moreover have "encok 5" unfolding encok_def by (rule enc_x_5)
  ultimately show "encok j" using encall_5 by auto
qed
lemma encall_7: "\<forall>j<(7::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 7"
  then have "j < 6 \<or> j = 6" by linarith
  moreover have "encok 6" unfolding encok_def by (rule enc_x_6)
  ultimately show "encok j" using encall_6 by auto
qed
lemma encall_8: "\<forall>j<(8::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 8"
  then have "j < 7 \<or> j = 7" by linarith
  moreover have "encok 7" unfolding encok_def by (rule enc_x_7)
  ultimately show "encok j" using encall_7 by auto
qed
lemma encall_9: "\<forall>j<(9::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 9"
  then have "j < 8 \<or> j = 8" by linarith
  moreover have "encok 8" unfolding encok_def by (rule enc_x_8)
  ultimately show "encok j" using encall_8 by auto
qed
lemma encall_10: "\<forall>j<(10::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 10"
  then have "j < 9 \<or> j = 9" by linarith
  moreover have "encok 9" unfolding encok_def by (rule enc_x_9)
  ultimately show "encok j" using encall_9 by auto
qed
lemma encall_11: "\<forall>j<(11::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 11"
  then have "j < 10 \<or> j = 10" by linarith
  moreover have "encok 10" unfolding encok_def by (rule enc_x_10)
  ultimately show "encok j" using encall_10 by auto
qed
lemma encall_12: "\<forall>j<(12::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 12"
  then have "j < 11 \<or> j = 11" by linarith
  moreover have "encok 11" unfolding encok_def by (rule enc_x_11)
  ultimately show "encok j" using encall_11 by auto
qed
lemma encall_13: "\<forall>j<(13::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 13"
  then have "j < 12 \<or> j = 12" by linarith
  moreover have "encok 12" unfolding encok_def by (rule enc_x_12)
  ultimately show "encok j" using encall_12 by auto
qed
lemma encall_14: "\<forall>j<(14::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 14"
  then have "j < 13 \<or> j = 13" by linarith
  moreover have "encok 13" unfolding encok_def by (rule enc_x_13)
  ultimately show "encok j" using encall_13 by auto
qed
lemma encall_15: "\<forall>j<(15::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 15"
  then have "j < 14 \<or> j = 14" by linarith
  moreover have "encok 14" unfolding encok_def by (rule enc_x_14)
  ultimately show "encok j" using encall_14 by auto
qed
lemma encall_16: "\<forall>j<(16::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 16"
  then have "j < 15 \<or> j = 15" by linarith
  moreover have "encok 15" unfolding encok_def by (rule enc_x_15)
  ultimately show "encok j" using encall_15 by auto
qed
lemma encall_17: "\<forall>j<(17::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 17"
  then have "j < 16 \<or> j = 16" by linarith
  moreover have "encok 16" unfolding encok_def by (rule enc_x_16)
  ultimately show "encok j" using encall_16 by auto
qed
lemma encall_18: "\<forall>j<(18::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 18"
  then have "j < 17 \<or> j = 17" by linarith
  moreover have "encok 17" unfolding encok_def by (rule enc_x_17)
  ultimately show "encok j" using encall_17 by auto
qed
lemma encall_19: "\<forall>j<(19::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 19"
  then have "j < 18 \<or> j = 18" by linarith
  moreover have "encok 18" unfolding encok_def by (rule enc_x_18)
  ultimately show "encok j" using encall_18 by auto
qed
lemma encall_20: "\<forall>j<(20::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 20"
  then have "j < 19 \<or> j = 19" by linarith
  moreover have "encok 19" unfolding encok_def by (rule enc_x_19)
  ultimately show "encok j" using encall_19 by auto
qed
lemma encall_21: "\<forall>j<(21::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 21"
  then have "j < 20 \<or> j = 20" by linarith
  moreover have "encok 20" unfolding encok_def by (rule enc_x_20)
  ultimately show "encok j" using encall_20 by auto
qed
lemma encall_22: "\<forall>j<(22::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 22"
  then have "j < 21 \<or> j = 21" by linarith
  moreover have "encok 21" unfolding encok_def by (rule enc_x_21)
  ultimately show "encok j" using encall_21 by auto
qed
lemma encall_23: "\<forall>j<(23::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 23"
  then have "j < 22 \<or> j = 22" by linarith
  moreover have "encok 22" unfolding encok_def by (rule enc_x_22)
  ultimately show "encok j" using encall_22 by auto
qed
lemma encall_24: "\<forall>j<(24::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 24"
  then have "j < 23 \<or> j = 23" by linarith
  moreover have "encok 23" unfolding encok_def by (rule enc_x_23)
  ultimately show "encok j" using encall_23 by auto
qed
lemma encall_25: "\<forall>j<(25::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 25"
  then have "j < 24 \<or> j = 24" by linarith
  moreover have "encok 24" unfolding encok_def by (rule enc_x_24)
  ultimately show "encok j" using encall_24 by auto
qed
lemma encall_26: "\<forall>j<(26::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 26"
  then have "j < 25 \<or> j = 25" by linarith
  moreover have "encok 25" unfolding encok_def by (rule enc_x_25)
  ultimately show "encok j" using encall_25 by auto
qed
lemma encall_27: "\<forall>j<(27::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 27"
  then have "j < 26 \<or> j = 26" by linarith
  moreover have "encok 26" unfolding encok_def by (rule enc_x_26)
  ultimately show "encok j" using encall_26 by auto
qed
lemma encall_28: "\<forall>j<(28::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 28"
  then have "j < 27 \<or> j = 27" by linarith
  moreover have "encok 27" unfolding encok_def by (rule enc_x_27)
  ultimately show "encok j" using encall_27 by auto
qed
lemma encall_29: "\<forall>j<(29::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 29"
  then have "j < 28 \<or> j = 28" by linarith
  moreover have "encok 28" unfolding encok_def by (rule enc_x_28)
  ultimately show "encok j" using encall_28 by auto
qed
lemma encall_30: "\<forall>j<(30::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 30"
  then have "j < 29 \<or> j = 29" by linarith
  moreover have "encok 29" unfolding encok_def by (rule enc_x_29)
  ultimately show "encok j" using encall_29 by auto
qed
lemma encall_31: "\<forall>j<(31::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 31"
  then have "j < 30 \<or> j = 30" by linarith
  moreover have "encok 30" unfolding encok_def by (rule enc_x_30)
  ultimately show "encok j" using encall_30 by auto
qed
lemma encall_32: "\<forall>j<(32::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 32"
  then have "j < 31 \<or> j = 31" by linarith
  moreover have "encok 31" unfolding encok_def by (rule enc_x_31)
  ultimately show "encok j" using encall_31 by auto
qed
lemma encall_33: "\<forall>j<(33::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 33"
  then have "j < 32 \<or> j = 32" by linarith
  moreover have "encok 32" unfolding encok_def by (rule enc_x_32)
  ultimately show "encok j" using encall_32 by auto
qed
lemma encall_34: "\<forall>j<(34::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 34"
  then have "j < 33 \<or> j = 33" by linarith
  moreover have "encok 33" unfolding encok_def by (rule enc_x_33)
  ultimately show "encok j" using encall_33 by auto
qed
lemma encall_35: "\<forall>j<(35::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 35"
  then have "j < 34 \<or> j = 34" by linarith
  moreover have "encok 34" unfolding encok_def by (rule enc_x_34)
  ultimately show "encok j" using encall_34 by auto
qed
lemma encall_36: "\<forall>j<(36::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 36"
  then have "j < 35 \<or> j = 35" by linarith
  moreover have "encok 35" unfolding encok_def by (rule enc_x_35)
  ultimately show "encok j" using encall_35 by auto
qed
lemma encall_37: "\<forall>j<(37::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 37"
  then have "j < 36 \<or> j = 36" by linarith
  moreover have "encok 36" unfolding encok_def by (rule enc_x_36)
  ultimately show "encok j" using encall_36 by auto
qed
lemma encall_38: "\<forall>j<(38::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 38"
  then have "j < 37 \<or> j = 37" by linarith
  moreover have "encok 37" unfolding encok_def by (rule enc_x_37)
  ultimately show "encok j" using encall_37 by auto
qed
lemma encall_39: "\<forall>j<(39::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 39"
  then have "j < 38 \<or> j = 38" by linarith
  moreover have "encok 38" unfolding encok_def by (rule enc_x_38)
  ultimately show "encok j" using encall_38 by auto
qed
lemma encall_40: "\<forall>j<(40::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 40"
  then have "j < 39 \<or> j = 39" by linarith
  moreover have "encok 39" unfolding encok_def by (rule enc_x_39)
  ultimately show "encok j" using encall_39 by auto
qed
lemma encall_41: "\<forall>j<(41::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 41"
  then have "j < 40 \<or> j = 40" by linarith
  moreover have "encok 40" unfolding encok_def by (rule enc_x_40)
  ultimately show "encok j" using encall_40 by auto
qed
lemma encall_42: "\<forall>j<(42::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 42"
  then have "j < 41 \<or> j = 41" by linarith
  moreover have "encok 41" unfolding encok_def by (rule enc_x_41)
  ultimately show "encok j" using encall_41 by auto
qed
lemma encall_43: "\<forall>j<(43::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 43"
  then have "j < 42 \<or> j = 42" by linarith
  moreover have "encok 42" unfolding encok_def by (rule enc_x_42)
  ultimately show "encok j" using encall_42 by auto
qed
lemma encall_44: "\<forall>j<(44::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 44"
  then have "j < 43 \<or> j = 43" by linarith
  moreover have "encok 43" unfolding encok_def by (rule enc_x_43)
  ultimately show "encok j" using encall_43 by auto
qed
lemma encall_45: "\<forall>j<(45::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 45"
  then have "j < 44 \<or> j = 44" by linarith
  moreover have "encok 44" unfolding encok_def by (rule enc_x_44)
  ultimately show "encok j" using encall_44 by auto
qed
lemma encall_46: "\<forall>j<(46::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 46"
  then have "j < 45 \<or> j = 45" by linarith
  moreover have "encok 45" unfolding encok_def by (rule enc_x_45)
  ultimately show "encok j" using encall_45 by auto
qed
lemma encall_47: "\<forall>j<(47::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 47"
  then have "j < 46 \<or> j = 46" by linarith
  moreover have "encok 46" unfolding encok_def by (rule enc_x_46)
  ultimately show "encok j" using encall_46 by auto
qed
lemma encall_48: "\<forall>j<(48::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 48"
  then have "j < 47 \<or> j = 47" by linarith
  moreover have "encok 47" unfolding encok_def by (rule enc_x_47)
  ultimately show "encok j" using encall_47 by auto
qed
lemma encall_49: "\<forall>j<(49::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 49"
  then have "j < 48 \<or> j = 48" by linarith
  moreover have "encok 48" unfolding encok_def by (rule enc_x_48)
  ultimately show "encok j" using encall_48 by auto
qed
lemma encall_50: "\<forall>j<(50::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 50"
  then have "j < 49 \<or> j = 49" by linarith
  moreover have "encok 49" unfolding encok_def by (rule enc_x_49)
  ultimately show "encok j" using encall_49 by auto
qed
lemma encall_51: "\<forall>j<(51::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 51"
  then have "j < 50 \<or> j = 50" by linarith
  moreover have "encok 50" unfolding encok_def by (rule enc_x_50)
  ultimately show "encok j" using encall_50 by auto
qed
lemma encall_52: "\<forall>j<(52::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 52"
  then have "j < 51 \<or> j = 51" by linarith
  moreover have "encok 51" unfolding encok_def by (rule enc_x_51)
  ultimately show "encok j" using encall_51 by auto
qed
lemma encall_53: "\<forall>j<(53::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 53"
  then have "j < 52 \<or> j = 52" by linarith
  moreover have "encok 52" unfolding encok_def by (rule enc_x_52)
  ultimately show "encok j" using encall_52 by auto
qed
lemma encall_54: "\<forall>j<(54::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 54"
  then have "j < 53 \<or> j = 53" by linarith
  moreover have "encok 53" unfolding encok_def by (rule enc_x_53)
  ultimately show "encok j" using encall_53 by auto
qed
lemma encall_55: "\<forall>j<(55::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 55"
  then have "j < 54 \<or> j = 54" by linarith
  moreover have "encok 54" unfolding encok_def by (rule enc_x_54)
  ultimately show "encok j" using encall_54 by auto
qed
lemma encall_56: "\<forall>j<(56::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 56"
  then have "j < 55 \<or> j = 55" by linarith
  moreover have "encok 55" unfolding encok_def by (rule enc_x_55)
  ultimately show "encok j" using encall_55 by auto
qed
lemma encall_57: "\<forall>j<(57::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 57"
  then have "j < 56 \<or> j = 56" by linarith
  moreover have "encok 56" unfolding encok_def by (rule enc_x_56)
  ultimately show "encok j" using encall_56 by auto
qed
lemma encall_58: "\<forall>j<(58::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 58"
  then have "j < 57 \<or> j = 57" by linarith
  moreover have "encok 57" unfolding encok_def by (rule enc_x_57)
  ultimately show "encok j" using encall_57 by auto
qed
lemma encall_59: "\<forall>j<(59::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 59"
  then have "j < 58 \<or> j = 58" by linarith
  moreover have "encok 58" unfolding encok_def by (rule enc_x_58)
  ultimately show "encok j" using encall_58 by auto
qed
lemma encall_60: "\<forall>j<(60::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 60"
  then have "j < 59 \<or> j = 59" by linarith
  moreover have "encok 59" unfolding encok_def by (rule enc_x_59)
  ultimately show "encok j" using encall_59 by auto
qed
lemma encall_61: "\<forall>j<(61::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 61"
  then have "j < 60 \<or> j = 60" by linarith
  moreover have "encok 60" unfolding encok_def by (rule enc_x_60)
  ultimately show "encok j" using encall_60 by auto
qed
lemma encall_62: "\<forall>j<(62::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 62"
  then have "j < 61 \<or> j = 61" by linarith
  moreover have "encok 61" unfolding encok_def by (rule enc_x_61)
  ultimately show "encok j" using encall_61 by auto
qed
lemma encall_63: "\<forall>j<(63::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 63"
  then have "j < 62 \<or> j = 62" by linarith
  moreover have "encok 62" unfolding encok_def by (rule enc_x_62)
  ultimately show "encok j" using encall_62 by auto
qed
lemma encall_64: "\<forall>j<(64::nat). encok j"
proof (intro allI impI)
  fix j :: nat assume "j < 64"
  then have "j < 63 \<or> j = 63" by linarith
  moreover have "encok 63" unfolding encok_def by (rule enc_x_63)
  ultimately show "encok j" using encall_63 by auto
qed

lemma enc_x: "j < 64 \<Longrightarrow> gfw (encw ! j) = X j (beta 32)"
  using encall_64 by (simp add: encok_def)

theorem encodeIdx_gf:
  fixes fx :: "(256, w64) seq"
  assumes e: "e < 512"
  shows "gfw (seq_to_word (nth_seq (FFTEnc.encodeIdx fx) e))
       = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat fx)) (512 * j + e) then X j (beta 32) else 0)"
proof -
  define V where "V = (rev_seq (coerce_seq_len (map_seq (\<lambda>j. nth_end_list (seq_to_list (FFTEnc.flat fx)) (to_nat (0x200 * j + from_nat e)))
            (fromToLessThan TY(0) TY(32) TY((14, bool) seq)))) :: (32, bool) seq)"
  have nt: "nth_seq (FFTEnc.encodeIdx fx) e = FFTEnc.linmap TY(32) FFTEnc.encMat V"
    using e by (simp add: FFTEnc.encodeIdx_def Let_def seq_to_list nth_seq.rep_eq V_def)
  have "gfw (seq_to_word (nth_seq (FFTEnc.encodeIdx fx) e))
      = sum_list (map gfw (map (\<lambda>j. if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0) [0..<32]))"
    by (simp add: nt linmap_word gfw_foldl_xor)
  also have "\<dots> = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat fx)) (512 * j + e) then X j (beta 32) else 0)"
  proof -
    have pt: "\<And>j. j < 32 \<Longrightarrow> gfw (if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0)
            = (if bit (seq_to_word (FFTEnc.flat fx)) (512 * j + e) then X j (beta 32) else 0)"
      using e by (simp add: V_def encode_bit encw_nth enc_x)
    have "sum_list (map gfw (map (\<lambda>j. if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0) [0..<32]))
        = (\<Sum>j\<in>{0..<32}. gfw (if bit (seq_to_word V) j then seq_to_word (nth_seq FFTEnc.encMat j) else 0))"
      by (simp only: map_map sum_set_upt_conv_sum_list_nat[symmetric] set_upt comp_def)
    also have "\<dots> = (\<Sum>j<32. if bit (seq_to_word (FFTEnc.flat fx)) (512 * j + e) then X j (beta 32) else 0)"
      by (simp only: atLeast0LessThan) (rule sum.cong, rule refl, simp add: pt)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

end
