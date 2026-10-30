theory BtfyBridge
  imports StageBridge
begin

text \<open>The twiddle of unit mm at stage si of btfy_64(poly, 9, 2^41): the model's
  cantor((2 mm) XOR (2^41 >> si)) is cantor beta (2^(41-si) + 2 mm), the twf of the network.\<close>

lemma xor_pow_disjoint:
  assumes "a < 2 ^ n" "n < 64"
  shows "unat ((word_of_nat a :: 64 word) XOR 2 ^ n) = a + 2 ^ n"
proof -
  have dis: "\<not> bit (word_of_nat a :: 64 word) i \<or> \<not> bit (2 ^ n :: 64 word) i" for i
  proof (cases "i = n")
    case True
    have "\<not> bit a n" using assms(1) by (simp add: bit_iff_odd)
    then show ?thesis using True by (simp add: bit_of_nat_iff)
  next
    case False then show ?thesis by (simp add: bit_exp_iff)
  qed
  have x: "(word_of_nat a :: 64 word) XOR 2 ^ n = word_of_nat a + 2 ^ n"
  proof -
    have "(word_of_nat a :: 64 word) XOR 2 ^ n = word_of_nat a OR 2 ^ n"
      by (rule bit_eqI) (use dis in \<open>auto simp: bit_xor_iff bit_or_iff\<close>)
    also have "\<dots> = word_of_nat a + 2 ^ n" by (rule disjunctive_add[symmetric]) (use dis in auto)
    finally show ?thesis .
  qed
  have bnd: "a + 2 ^ n < 2 ^ 64"
  proof -
    have "a + 2 ^ n < 2 ^ n + 2 ^ n" using assms(1) by simp
    also have "\<dots> = 2 ^ Suc n" by simp
    also have "\<dots> \<le> 2 ^ 64" using assms(2) by (intro power_increasing) simp_all
    finally show ?thesis .
  qed
  have "unat ((word_of_nat a :: 64 word) + 2 ^ n) = unat (word_of_nat (a + 2 ^ n) :: 64 word)" by simp
  also have "\<dots> = a + 2 ^ n" using bnd by (subst unat_of_nat_eq) simp_all
  finally show ?thesis by (simp only: x)
qed

lemma drop_pow: "m < 64 \<Longrightarrow> n \<le> m \<Longrightarrow> drop_bit n (2 ^ m :: 64 word) = 2 ^ (m - n)"
  by (rule bit_eqI) (auto simp: bit_drop_bit_eq bit_exp_iff)

lemma tw_level:
  assumes B: "B < 64" and si: "si < M" and MB: "M \<le> B" and mm: "mm < 2 ^ (M - Suc si)"
  shows "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR drop_bit si (2 ^ B :: 64 word))) = twf beta (2 ^ B) si mm"
proof -
  have m2: "2 * mm < 2 ^ (B - si)"
  proof -
    have "2 * mm < 2 * 2 ^ (M - Suc si)" using mm by simp
    also have "\<dots> = 2 ^ (M - si)"
    proof -
      have "M - si = Suc (M - Suc si)" using si by simp
      then show ?thesis by (simp only: power_Suc)
    qed
    also have "\<dots> \<le> 2 ^ (B - si)" using MB by (intro power_increasing) simp_all
    finally show ?thesis .
  qed
  have db: "drop_bit si (2 ^ B :: 64 word) = 2 ^ (B - si)"
    using drop_pow[of B si] B si MB by simp
  have w: "(2 * word_of_nat mm :: 64 word) = word_of_nat (2 * mm)" by simp
  have u: "unat ((2 * word_of_nat mm) XOR drop_bit si (2 ^ B :: 64 word)) = 2 * mm + 2 ^ (B - si)"
    using xor_pow_disjoint[OF m2] B by (simp only: db w)
  have t: "(2 ^ B + mm * 2 ^ Suc si) div 2 ^ si = 2 ^ (B - si) + 2 * mm"
  proof -
    have "(2 :: nat) ^ B = 2 ^ (B - si) * 2 ^ si" using si MB by (simp add: power_add[symmetric])
    moreover have "mm * 2 ^ Suc si = (2 * mm) * 2 ^ si" by simp
    ultimately have "2 ^ B + mm * 2 ^ Suc si = (2 ^ (B - si) + 2 * mm) * 2 ^ si" by (simp add: algebra_simps)
    then show ?thesis by simp
  qed
  show ?thesis unfolding twf_def u t by (simp only: add.commute)
qed

lemma FV_coerce:
  "LEN('n) = LEN('m) \<Longrightarrow> FV (coerce_seq_len (x :: ('n, w64) seq) :: ('m, w64) seq) = FV x"
  by (rule ext) (simp add: FV_def gv_def coerce_seq_len.rep_eq)

lemma s2w_rshift: "0 \<le> i \<Longrightarrow> seq_to_word (right_shift (x :: w64) i) = drop_bit (nat i) (seq_to_word x)"
  by (simp add: seq_to_word.right_shift shiftr_def)

lemma stage_step_num:
  fixes p :: "('k::len \<times> 2 \<times> 'h::len, w64) seq" and s :: w64
  assumes "LENGTH('h) = h" "LENGTH('k) = k" "k * (2 * h) = N" "k \<le> 2 ^ 32"
    and "EqOn N (FV p) G"
    and "\<And>mm. mm < k \<Longrightarrow> Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)) = tw mm"
  shows "EqOn N (FV (FFTRef.stage TY('h) TY('k) s p)) (stagef h tw G)"
  using stage_step[of p G s tw] assms by simp

theorem btfy9_chain:
  fixes sc :: w64 and p :: "(512, w64) seq"
  assumes sc: "seq_to_word sc = 2 ^ 41" and e: "EqOn 512 (FV p) f"
  shows "EqOn 512 (FV (FFTRef.btfy9 sc p)) (chain beta (2 ^ 41) 9 f)"
proof -
  have tw0: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word sc)) = twf beta (2 ^ 41) 0 mm" if "mm < 256" for mm
  proof -
    have "seq_to_word sc = drop_bit 0 (2 ^ 41)" by (simp only: sc) simp
    then show ?thesis using tw_level[of 41 0 9 mm] that by simp
  qed
  have tw1: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc 1))) = twf beta (2 ^ 41) 1 mm" if "mm < 128" for mm
  proof -
    have "seq_to_word (right_shift sc 1) = drop_bit 1 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 1 9 mm] that by simp
  qed
  have tw2: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (2::int)))) = twf beta (2 ^ 41) 2 mm" if "mm < 64" for mm
  proof -
    have "seq_to_word (right_shift sc (2::int)) = drop_bit 2 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 2 9 mm] that by simp
  qed
  have tw3: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (3::int)))) = twf beta (2 ^ 41) 3 mm" if "mm < 32" for mm
  proof -
    have "seq_to_word (right_shift sc (3::int)) = drop_bit 3 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 3 9 mm] that by simp
  qed
  have tw4: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (4::int)))) = twf beta (2 ^ 41) 4 mm" if "mm < 16" for mm
  proof -
    have "seq_to_word (right_shift sc (4::int)) = drop_bit 4 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 4 9 mm] that by simp
  qed
  have tw5: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (5::int)))) = twf beta (2 ^ 41) 5 mm" if "mm < 8" for mm
  proof -
    have "seq_to_word (right_shift sc (5::int)) = drop_bit 5 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 5 9 mm] that by simp
  qed
  have tw6: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (6::int)))) = twf beta (2 ^ 41) 6 mm" if "mm < 4" for mm
  proof -
    have "seq_to_word (right_shift sc (6::int)) = drop_bit 6 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 6 9 mm] that by simp
  qed
  have tw7: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (7::int)))) = twf beta (2 ^ 41) 7 mm" if "mm < 2" for mm
  proof -
    have "seq_to_word (right_shift sc (7::int)) = drop_bit 7 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 7 9 mm] that by simp
  qed
  have tw8: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (8::int)))) = twf beta (2 ^ 41) 8 mm" if "mm < 1" for mm
  proof -
    have "seq_to_word (right_shift sc (8::int)) = drop_bit 8 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 8 9 mm] that by simp
  qed
  have chb: "chain beta b 9 f = stagef 1 (twf beta b 0) (stagef 2 (twf beta b 1) (stagef 4 (twf beta b 2) (stagef 8 (twf beta b 3) (stagef 16 (twf beta b 4) (stagef 32 (twf beta b 5) (stagef 64 (twf beta b 6) (stagef 128 (twf beta b 7) (stagef 256 (twf beta b 8) (f)))))))))" for b
  proof -
    have n9: "(9::nat) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))" by simp
    show ?thesis by (simp only: n9 chain.simps) (simp add: numeral_eq_Suc)
  qed
  have ch: "chain beta (2 ^ 41) 9 f = stagef 1 (twf beta (2 ^ 41) 0) (stagef 2 (twf beta (2 ^ 41) 1) (stagef 4 (twf beta (2 ^ 41) 2) (stagef 8 (twf beta (2 ^ 41) 3) (stagef 16 (twf beta (2 ^ 41) 4) (stagef 32 (twf beta (2 ^ 41) 5) (stagef 64 (twf beta (2 ^ 41) 6) (stagef 128 (twf beta (2 ^ 41) 7) (stagef 256 (twf beta (2 ^ 41) 8) (f)))))))))"
    by (rule chb)
  have nf: "FFTRef.btfy9 sc p = (coerce_seq_len (FFTRef.stage TY(1) TY(256) sc (coerce_seq_len (FFTRef.stage TY(2) TY(128) (right_shift sc 1) (coerce_seq_len (FFTRef.stage TY(4) TY(64) (right_shift sc (2::int)) (coerce_seq_len (FFTRef.stage TY(8) TY(32) (right_shift sc (3::int)) (coerce_seq_len (FFTRef.stage TY(16) TY(16) (right_shift sc (4::int)) (coerce_seq_len (FFTRef.stage TY(32) TY(8) (right_shift sc (5::int)) (coerce_seq_len (FFTRef.stage TY(64) TY(4) (right_shift sc (6::int)) (coerce_seq_len (FFTRef.stage TY(128) TY(2) (right_shift sc (7::int)) (coerce_seq_len (FFTRef.stage TY(256) TY(1) (right_shift sc (8::int)) (coerce_seq_len p)))))))))))))))))) :: (512, w64) seq)"
    by (simp add: FFTRef.btfy9_def)
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
    by (rule e)
qed

end
