theory Btfy35
  imports "HQC_FFT.IStageBridge"
begin

text \<open>The butterfly networks at the hqc-3 and hqc-5 sizes: btfy_64(poly, 10, 2^42) and
  btfy_64(poly, 11, 2^43) and their inverses are the stage chains of the network theory. Generated
  from the same template as btfy9_chain and ibtfy9_ichain.\<close>

theorem btfy10_chain:
  fixes sc :: w64 and p :: "(1024, w64) seq"
  assumes sc: "seq_to_word sc = 2 ^ 42" and e: "EqOn 1024 (FV p) f"
  shows "EqOn 1024 (FV (FFTRef.btfy10 sc p)) (chain beta (2 ^ 42) 10 f)"
proof -
  have tw0: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word sc)) = twf beta (2 ^ 42) 0 mm" if "mm < 512" for mm
  proof -
    have "seq_to_word sc = drop_bit 0 (2 ^ 42)" by (simp only: sc) simp
    then show ?thesis using tw_level[of 42 0 10 mm] that by simp
  qed
  have tw1: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc 1))) = twf beta (2 ^ 42) 1 mm" if "mm < 256" for mm
  proof -
    have "seq_to_word (right_shift sc 1) = drop_bit 1 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 1 10 mm] that by simp
  qed
  have tw2: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (2::int)))) = twf beta (2 ^ 42) 2 mm" if "mm < 128" for mm
  proof -
    have "seq_to_word (right_shift sc (2::int)) = drop_bit 2 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 2 10 mm] that by simp
  qed
  have tw3: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (3::int)))) = twf beta (2 ^ 42) 3 mm" if "mm < 64" for mm
  proof -
    have "seq_to_word (right_shift sc (3::int)) = drop_bit 3 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 3 10 mm] that by simp
  qed
  have tw4: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (4::int)))) = twf beta (2 ^ 42) 4 mm" if "mm < 32" for mm
  proof -
    have "seq_to_word (right_shift sc (4::int)) = drop_bit 4 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 4 10 mm] that by simp
  qed
  have tw5: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (5::int)))) = twf beta (2 ^ 42) 5 mm" if "mm < 16" for mm
  proof -
    have "seq_to_word (right_shift sc (5::int)) = drop_bit 5 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 5 10 mm] that by simp
  qed
  have tw6: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (6::int)))) = twf beta (2 ^ 42) 6 mm" if "mm < 8" for mm
  proof -
    have "seq_to_word (right_shift sc (6::int)) = drop_bit 6 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 6 10 mm] that by simp
  qed
  have tw7: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (7::int)))) = twf beta (2 ^ 42) 7 mm" if "mm < 4" for mm
  proof -
    have "seq_to_word (right_shift sc (7::int)) = drop_bit 7 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 7 10 mm] that by simp
  qed
  have tw8: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (8::int)))) = twf beta (2 ^ 42) 8 mm" if "mm < 2" for mm
  proof -
    have "seq_to_word (right_shift sc (8::int)) = drop_bit 8 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 8 10 mm] that by simp
  qed
  have tw9: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (9::int)))) = twf beta (2 ^ 42) 9 mm" if "mm < 1" for mm
  proof -
    have "seq_to_word (right_shift sc (9::int)) = drop_bit 9 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 9 10 mm] that by simp
  qed
  have chb: "chain beta b 10 f = stagef 1 (twf beta b 0) (stagef 2 (twf beta b 1) (stagef 4 (twf beta b 2) (stagef 8 (twf beta b 3) (stagef 16 (twf beta b 4) (stagef 32 (twf beta b 5) (stagef 64 (twf beta b 6) (stagef 128 (twf beta b 7) (stagef 256 (twf beta b 8) (stagef 512 (twf beta b 9) (f))))))))))" for b
  proof -
    have n: "(10::nat) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0))))))))))" by simp
    show ?thesis by (simp only: n chain.simps) (simp add: numeral_eq_Suc)
  qed
  have ch: "chain beta (2 ^ 42) 10 f = stagef 1 (twf beta (2 ^ 42) 0) (stagef 2 (twf beta (2 ^ 42) 1) (stagef 4 (twf beta (2 ^ 42) 2) (stagef 8 (twf beta (2 ^ 42) 3) (stagef 16 (twf beta (2 ^ 42) 4) (stagef 32 (twf beta (2 ^ 42) 5) (stagef 64 (twf beta (2 ^ 42) 6) (stagef 128 (twf beta (2 ^ 42) 7) (stagef 256 (twf beta (2 ^ 42) 8) (stagef 512 (twf beta (2 ^ 42) 9) (f))))))))))"
    by (rule chb)
  have nf: "FFTRef.btfy10 sc p = (coerce_seq_len (FFTRef.stage TY(1) TY(512) sc (coerce_seq_len (FFTRef.stage TY(2) TY(256) (right_shift sc 1) (coerce_seq_len (FFTRef.stage TY(4) TY(128) (right_shift sc (2::int)) (coerce_seq_len (FFTRef.stage TY(8) TY(64) (right_shift sc (3::int)) (coerce_seq_len (FFTRef.stage TY(16) TY(32) (right_shift sc (4::int)) (coerce_seq_len (FFTRef.stage TY(32) TY(16) (right_shift sc (5::int)) (coerce_seq_len (FFTRef.stage TY(64) TY(8) (right_shift sc (6::int)) (coerce_seq_len (FFTRef.stage TY(128) TY(4) (right_shift sc (7::int)) (coerce_seq_len (FFTRef.stage TY(256) TY(2) (right_shift sc (8::int)) (coerce_seq_len (FFTRef.stage TY(512) TY(1) (right_shift sc (9::int)) (coerce_seq_len p)))))))))))))))))))) :: (1024, w64) seq)"
    by (simp add: FFTRef.btfy10_def)
  show ?thesis
    unfolding nf ch
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw0, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw1, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw2, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw3, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw4, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw5, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw6, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw7, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw8, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw9, simp)
    apply (subst FV_coerce, simp)
    by (rule e)
qed

theorem ibtfy10_ichain:
  fixes sc :: w64 and p :: "(1024, w64) seq"
  assumes sc: "seq_to_word sc = 2 ^ 42" and e: "EqOn 1024 (FV p) f"
  shows "EqOn 1024 (FV (FFTRef.ibtfy10 sc p)) (ichain beta (2 ^ 42) 10 f)"
proof -
  have tw0: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word sc)) = twf beta (2 ^ 42) 0 mm" if "mm < 512" for mm
  proof -
    have "seq_to_word sc = drop_bit 0 (2 ^ 42)" by (simp only: sc) simp
    then show ?thesis using tw_level[of 42 0 10 mm] that by simp
  qed
  have tw1: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc 1))) = twf beta (2 ^ 42) 1 mm" if "mm < 256" for mm
  proof -
    have "seq_to_word (right_shift sc 1) = drop_bit 1 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 1 10 mm] that by simp
  qed
  have tw2: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (2::int)))) = twf beta (2 ^ 42) 2 mm" if "mm < 128" for mm
  proof -
    have "seq_to_word (right_shift sc (2::int)) = drop_bit 2 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 2 10 mm] that by simp
  qed
  have tw3: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (3::int)))) = twf beta (2 ^ 42) 3 mm" if "mm < 64" for mm
  proof -
    have "seq_to_word (right_shift sc (3::int)) = drop_bit 3 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 3 10 mm] that by simp
  qed
  have tw4: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (4::int)))) = twf beta (2 ^ 42) 4 mm" if "mm < 32" for mm
  proof -
    have "seq_to_word (right_shift sc (4::int)) = drop_bit 4 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 4 10 mm] that by simp
  qed
  have tw5: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (5::int)))) = twf beta (2 ^ 42) 5 mm" if "mm < 16" for mm
  proof -
    have "seq_to_word (right_shift sc (5::int)) = drop_bit 5 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 5 10 mm] that by simp
  qed
  have tw6: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (6::int)))) = twf beta (2 ^ 42) 6 mm" if "mm < 8" for mm
  proof -
    have "seq_to_word (right_shift sc (6::int)) = drop_bit 6 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 6 10 mm] that by simp
  qed
  have tw7: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (7::int)))) = twf beta (2 ^ 42) 7 mm" if "mm < 4" for mm
  proof -
    have "seq_to_word (right_shift sc (7::int)) = drop_bit 7 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 7 10 mm] that by simp
  qed
  have tw8: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (8::int)))) = twf beta (2 ^ 42) 8 mm" if "mm < 2" for mm
  proof -
    have "seq_to_word (right_shift sc (8::int)) = drop_bit 8 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 8 10 mm] that by simp
  qed
  have tw9: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (9::int)))) = twf beta (2 ^ 42) 9 mm" if "mm < 1" for mm
  proof -
    have "seq_to_word (right_shift sc (9::int)) = drop_bit 9 (2 ^ 42)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 42 9 10 mm] that by simp
  qed
  have chb: "ichain beta b 10 f = istagef 512 (twf beta b 9) (istagef 256 (twf beta b 8) (istagef 128 (twf beta b 7) (istagef 64 (twf beta b 6) (istagef 32 (twf beta b 5) (istagef 16 (twf beta b 4) (istagef 8 (twf beta b 3) (istagef 4 (twf beta b 2) (istagef 2 (twf beta b 1) (istagef 1 (twf beta b 0) (f))))))))))" for b
  proof -
    have n: "(10::nat) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0))))))))))" by simp
    show ?thesis by (simp only: n ichain.simps) (simp add: numeral_eq_Suc)
  qed
  have ch: "ichain beta (2 ^ 42) 10 f = istagef 512 (twf beta (2 ^ 42) 9) (istagef 256 (twf beta (2 ^ 42) 8) (istagef 128 (twf beta (2 ^ 42) 7) (istagef 64 (twf beta (2 ^ 42) 6) (istagef 32 (twf beta (2 ^ 42) 5) (istagef 16 (twf beta (2 ^ 42) 4) (istagef 8 (twf beta (2 ^ 42) 3) (istagef 4 (twf beta (2 ^ 42) 2) (istagef 2 (twf beta (2 ^ 42) 1) (istagef 1 (twf beta (2 ^ 42) 0) (f))))))))))"
    by (rule chb)
  have nf: "FFTRef.ibtfy10 sc p = (coerce_seq_len (FFTRef.istage TY(512) TY(1) (right_shift sc (9::int)) (coerce_seq_len (FFTRef.istage TY(256) TY(2) (right_shift sc (8::int)) (coerce_seq_len (FFTRef.istage TY(128) TY(4) (right_shift sc (7::int)) (coerce_seq_len (FFTRef.istage TY(64) TY(8) (right_shift sc (6::int)) (coerce_seq_len (FFTRef.istage TY(32) TY(16) (right_shift sc (5::int)) (coerce_seq_len (FFTRef.istage TY(16) TY(32) (right_shift sc (4::int)) (coerce_seq_len (FFTRef.istage TY(8) TY(64) (right_shift sc (3::int)) (coerce_seq_len (FFTRef.istage TY(4) TY(128) (right_shift sc (2::int)) (coerce_seq_len (FFTRef.istage TY(2) TY(256) (right_shift sc 1) (coerce_seq_len (FFTRef.istage TY(1) TY(512) sc (coerce_seq_len p)))))))))))))))))))) :: (1024, w64) seq)"
    by (simp add: FFTRef.ibtfy10_def)
  show ?thesis
    unfolding nf ch
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw9, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw8, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw7, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw6, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw5, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw4, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw3, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw2, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw1, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw0, simp)
    apply (subst FV_coerce, simp)
    by (rule e)
qed

theorem btfy11_chain:
  fixes sc :: w64 and p :: "(2048, w64) seq"
  assumes sc: "seq_to_word sc = 2 ^ 43" and e: "EqOn 2048 (FV p) f"
  shows "EqOn 2048 (FV (FFTRef.btfy11 sc p)) (chain beta (2 ^ 43) 11 f)"
proof -
  have tw0: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word sc)) = twf beta (2 ^ 43) 0 mm" if "mm < 1024" for mm
  proof -
    have "seq_to_word sc = drop_bit 0 (2 ^ 43)" by (simp only: sc) simp
    then show ?thesis using tw_level[of 43 0 11 mm] that by simp
  qed
  have tw1: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc 1))) = twf beta (2 ^ 43) 1 mm" if "mm < 512" for mm
  proof -
    have "seq_to_word (right_shift sc 1) = drop_bit 1 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 1 11 mm] that by simp
  qed
  have tw2: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (2::int)))) = twf beta (2 ^ 43) 2 mm" if "mm < 256" for mm
  proof -
    have "seq_to_word (right_shift sc (2::int)) = drop_bit 2 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 2 11 mm] that by simp
  qed
  have tw3: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (3::int)))) = twf beta (2 ^ 43) 3 mm" if "mm < 128" for mm
  proof -
    have "seq_to_word (right_shift sc (3::int)) = drop_bit 3 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 3 11 mm] that by simp
  qed
  have tw4: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (4::int)))) = twf beta (2 ^ 43) 4 mm" if "mm < 64" for mm
  proof -
    have "seq_to_word (right_shift sc (4::int)) = drop_bit 4 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 4 11 mm] that by simp
  qed
  have tw5: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (5::int)))) = twf beta (2 ^ 43) 5 mm" if "mm < 32" for mm
  proof -
    have "seq_to_word (right_shift sc (5::int)) = drop_bit 5 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 5 11 mm] that by simp
  qed
  have tw6: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (6::int)))) = twf beta (2 ^ 43) 6 mm" if "mm < 16" for mm
  proof -
    have "seq_to_word (right_shift sc (6::int)) = drop_bit 6 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 6 11 mm] that by simp
  qed
  have tw7: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (7::int)))) = twf beta (2 ^ 43) 7 mm" if "mm < 8" for mm
  proof -
    have "seq_to_word (right_shift sc (7::int)) = drop_bit 7 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 7 11 mm] that by simp
  qed
  have tw8: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (8::int)))) = twf beta (2 ^ 43) 8 mm" if "mm < 4" for mm
  proof -
    have "seq_to_word (right_shift sc (8::int)) = drop_bit 8 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 8 11 mm] that by simp
  qed
  have tw9: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (9::int)))) = twf beta (2 ^ 43) 9 mm" if "mm < 2" for mm
  proof -
    have "seq_to_word (right_shift sc (9::int)) = drop_bit 9 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 9 11 mm] that by simp
  qed
  have tw10: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (10::int)))) = twf beta (2 ^ 43) 10 mm" if "mm < 1" for mm
  proof -
    have "seq_to_word (right_shift sc (10::int)) = drop_bit 10 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 10 11 mm] that by simp
  qed
  have chb: "chain beta b 11 f = stagef 1 (twf beta b 0) (stagef 2 (twf beta b 1) (stagef 4 (twf beta b 2) (stagef 8 (twf beta b 3) (stagef 16 (twf beta b 4) (stagef 32 (twf beta b 5) (stagef 64 (twf beta b 6) (stagef 128 (twf beta b 7) (stagef 256 (twf beta b 8) (stagef 512 (twf beta b 9) (stagef 1024 (twf beta b 10) (f)))))))))))" for b
  proof -
    have n: "(11::nat) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0)))))))))))" by simp
    show ?thesis by (simp only: n chain.simps) (simp add: numeral_eq_Suc)
  qed
  have ch: "chain beta (2 ^ 43) 11 f = stagef 1 (twf beta (2 ^ 43) 0) (stagef 2 (twf beta (2 ^ 43) 1) (stagef 4 (twf beta (2 ^ 43) 2) (stagef 8 (twf beta (2 ^ 43) 3) (stagef 16 (twf beta (2 ^ 43) 4) (stagef 32 (twf beta (2 ^ 43) 5) (stagef 64 (twf beta (2 ^ 43) 6) (stagef 128 (twf beta (2 ^ 43) 7) (stagef 256 (twf beta (2 ^ 43) 8) (stagef 512 (twf beta (2 ^ 43) 9) (stagef 1024 (twf beta (2 ^ 43) 10) (f)))))))))))"
    by (rule chb)
  have nf: "FFTRef.btfy11 sc p = (coerce_seq_len (FFTRef.stage TY(1) TY(1024) sc (coerce_seq_len (FFTRef.stage TY(2) TY(512) (right_shift sc 1) (coerce_seq_len (FFTRef.stage TY(4) TY(256) (right_shift sc (2::int)) (coerce_seq_len (FFTRef.stage TY(8) TY(128) (right_shift sc (3::int)) (coerce_seq_len (FFTRef.stage TY(16) TY(64) (right_shift sc (4::int)) (coerce_seq_len (FFTRef.stage TY(32) TY(32) (right_shift sc (5::int)) (coerce_seq_len (FFTRef.stage TY(64) TY(16) (right_shift sc (6::int)) (coerce_seq_len (FFTRef.stage TY(128) TY(8) (right_shift sc (7::int)) (coerce_seq_len (FFTRef.stage TY(256) TY(4) (right_shift sc (8::int)) (coerce_seq_len (FFTRef.stage TY(512) TY(2) (right_shift sc (9::int)) (coerce_seq_len (FFTRef.stage TY(1024) TY(1) (right_shift sc (10::int)) (coerce_seq_len p)))))))))))))))))))))) :: (2048, w64) seq)"
    by (simp add: FFTRef.btfy11_def)
  show ?thesis
    unfolding nf ch
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw0, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw1, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw2, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw3, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw4, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw5, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw6, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw7, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw8, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw9, simp)
    apply (subst FV_coerce, simp)
    apply (rule stage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw10, simp)
    apply (subst FV_coerce, simp)
    by (rule e)
qed

theorem ibtfy11_ichain:
  fixes sc :: w64 and p :: "(2048, w64) seq"
  assumes sc: "seq_to_word sc = 2 ^ 43" and e: "EqOn 2048 (FV p) f"
  shows "EqOn 2048 (FV (FFTRef.ibtfy11 sc p)) (ichain beta (2 ^ 43) 11 f)"
proof -
  have tw0: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word sc)) = twf beta (2 ^ 43) 0 mm" if "mm < 1024" for mm
  proof -
    have "seq_to_word sc = drop_bit 0 (2 ^ 43)" by (simp only: sc) simp
    then show ?thesis using tw_level[of 43 0 11 mm] that by simp
  qed
  have tw1: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc 1))) = twf beta (2 ^ 43) 1 mm" if "mm < 512" for mm
  proof -
    have "seq_to_word (right_shift sc 1) = drop_bit 1 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 1 11 mm] that by simp
  qed
  have tw2: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (2::int)))) = twf beta (2 ^ 43) 2 mm" if "mm < 256" for mm
  proof -
    have "seq_to_word (right_shift sc (2::int)) = drop_bit 2 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 2 11 mm] that by simp
  qed
  have tw3: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (3::int)))) = twf beta (2 ^ 43) 3 mm" if "mm < 128" for mm
  proof -
    have "seq_to_word (right_shift sc (3::int)) = drop_bit 3 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 3 11 mm] that by simp
  qed
  have tw4: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (4::int)))) = twf beta (2 ^ 43) 4 mm" if "mm < 64" for mm
  proof -
    have "seq_to_word (right_shift sc (4::int)) = drop_bit 4 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 4 11 mm] that by simp
  qed
  have tw5: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (5::int)))) = twf beta (2 ^ 43) 5 mm" if "mm < 32" for mm
  proof -
    have "seq_to_word (right_shift sc (5::int)) = drop_bit 5 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 5 11 mm] that by simp
  qed
  have tw6: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (6::int)))) = twf beta (2 ^ 43) 6 mm" if "mm < 16" for mm
  proof -
    have "seq_to_word (right_shift sc (6::int)) = drop_bit 6 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 6 11 mm] that by simp
  qed
  have tw7: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (7::int)))) = twf beta (2 ^ 43) 7 mm" if "mm < 8" for mm
  proof -
    have "seq_to_word (right_shift sc (7::int)) = drop_bit 7 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 7 11 mm] that by simp
  qed
  have tw8: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (8::int)))) = twf beta (2 ^ 43) 8 mm" if "mm < 4" for mm
  proof -
    have "seq_to_word (right_shift sc (8::int)) = drop_bit 8 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 8 11 mm] that by simp
  qed
  have tw9: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (9::int)))) = twf beta (2 ^ 43) 9 mm" if "mm < 2" for mm
  proof -
    have "seq_to_word (right_shift sc (9::int)) = drop_bit 9 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 9 11 mm] that by simp
  qed
  have tw10: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (10::int)))) = twf beta (2 ^ 43) 10 mm" if "mm < 1" for mm
  proof -
    have "seq_to_word (right_shift sc (10::int)) = drop_bit 10 (2 ^ 43)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 43 10 11 mm] that by simp
  qed
  have chb: "ichain beta b 11 f = istagef 1024 (twf beta b 10) (istagef 512 (twf beta b 9) (istagef 256 (twf beta b 8) (istagef 128 (twf beta b 7) (istagef 64 (twf beta b 6) (istagef 32 (twf beta b 5) (istagef 16 (twf beta b 4) (istagef 8 (twf beta b 3) (istagef 4 (twf beta b 2) (istagef 2 (twf beta b 1) (istagef 1 (twf beta b 0) (f)))))))))))" for b
  proof -
    have n: "(11::nat) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0)))))))))))" by simp
    show ?thesis by (simp only: n ichain.simps) (simp add: numeral_eq_Suc)
  qed
  have ch: "ichain beta (2 ^ 43) 11 f = istagef 1024 (twf beta (2 ^ 43) 10) (istagef 512 (twf beta (2 ^ 43) 9) (istagef 256 (twf beta (2 ^ 43) 8) (istagef 128 (twf beta (2 ^ 43) 7) (istagef 64 (twf beta (2 ^ 43) 6) (istagef 32 (twf beta (2 ^ 43) 5) (istagef 16 (twf beta (2 ^ 43) 4) (istagef 8 (twf beta (2 ^ 43) 3) (istagef 4 (twf beta (2 ^ 43) 2) (istagef 2 (twf beta (2 ^ 43) 1) (istagef 1 (twf beta (2 ^ 43) 0) (f)))))))))))"
    by (rule chb)
  have nf: "FFTRef.ibtfy11 sc p = (coerce_seq_len (FFTRef.istage TY(1024) TY(1) (right_shift sc (10::int)) (coerce_seq_len (FFTRef.istage TY(512) TY(2) (right_shift sc (9::int)) (coerce_seq_len (FFTRef.istage TY(256) TY(4) (right_shift sc (8::int)) (coerce_seq_len (FFTRef.istage TY(128) TY(8) (right_shift sc (7::int)) (coerce_seq_len (FFTRef.istage TY(64) TY(16) (right_shift sc (6::int)) (coerce_seq_len (FFTRef.istage TY(32) TY(32) (right_shift sc (5::int)) (coerce_seq_len (FFTRef.istage TY(16) TY(64) (right_shift sc (4::int)) (coerce_seq_len (FFTRef.istage TY(8) TY(128) (right_shift sc (3::int)) (coerce_seq_len (FFTRef.istage TY(4) TY(256) (right_shift sc (2::int)) (coerce_seq_len (FFTRef.istage TY(2) TY(512) (right_shift sc 1) (coerce_seq_len (FFTRef.istage TY(1) TY(1024) sc (coerce_seq_len p)))))))))))))))))))))) :: (2048, w64) seq)"
    by (simp add: FFTRef.ibtfy11_def)
  show ?thesis
    unfolding nf ch
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw10, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw9, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw8, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw7, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw6, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw5, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw4, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw3, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw2, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw1, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw0, simp)
    apply (subst FV_coerce, simp)
    by (rule e)
qed

end
