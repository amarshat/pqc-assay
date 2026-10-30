theory CantorBridge
  imports HQC_FFT_Const.CantorConst
begin

text \<open>The lifted cantor (FFTRef.cry) is the sum of the basis elements at the set bits of its
  argument, so as a field element it is cantor beta of the index.\<close>

lemma s2w_foldl_xor:
  "seq_to_word (foldl (\<lambda>a b. word_to_seq (seq_to_word a XOR seq_to_word b)) acc xs)
     = foldl (XOR) (seq_to_word acc) (map seq_to_word xs)"
  by (induction xs arbitrary: acc) simp_all

lemma cbw_nth: "i < 64 \<Longrightarrow> seq_to_word (nth_seq cantorBasis i) = cbw ! i"
proof -
  assume i: "i < 64"
  have "cbw ! i = map seq_to_word (seq_to_list cantorBasis) ! i" using cbw_lifted by (simp add: L_def)
  also have "\<dots> = seq_to_word (seq_to_list cantorBasis ! i)" using i by simp
  finally show ?thesis using i by (simp add: nth_seq.rep_eq)
qed

lemma cantor_word:
  fixes v :: w64
  shows "seq_to_word (FFTRef.cantor v) = foldl (XOR) 0 (map (\<lambda>i. if bit (seq_to_word v) i then cbw ! i else 0) [0..<64])"
proof -
  have "seq_to_word (FFTRef.cantor v) = foldl (XOR) 0
      (map (seq_to_word \<circ> ((\<lambda>i. if if pos_nat i < 64 then seq_to_word v !! (LENGTH(64) - Suc (LENGTH(64) - Suc (pos_nat i)))
                                   else oob_seq_elem (rev_seq v) then nth_seq cantorBasis (pos_nat i) else 0) \<circ> int)) [0..<64])"
    by (simp add: FFTRef.cantor_def word_seq_convs foldl_seq.rep_eq seq_to_list.fromTo s2w_foldl_xor seq_to_list.map_seq)
  also have "\<dots> = foldl (XOR) 0 (map (\<lambda>i. if bit (seq_to_word v) i then cbw ! i else 0) [0..<64])"
    by (intro arg_cong[where f="foldl (XOR) 0"] map_cong refl) (auto simp: cbw_nth seq_to_word.zero)
  finally show ?thesis .
qed

lemma gfw_foldl_xor: "gfw (foldl (XOR) acc xs) = gfw acc + sum_list (map gfw xs)"
  by (induction xs arbitrary: acc) (simp_all add: gfw_xor ac_simps)

theorem cantor_gf:
  fixes v :: w64
  shows "gfw (seq_to_word (FFTRef.cantor v)) = Cantor.cantor beta (unat (seq_to_word v))"
proof -
  have "gfw (seq_to_word (FFTRef.cantor v)) = (\<Sum>i<64. if bit (seq_to_word v) i then beta i else 0)"
    by (simp add: cantor_word gfw_foldl_xor sum_list_sum_nth atLeast0LessThan beta_def if_distrib cong: if_cong)
  also have "\<dots> = Cantor.cantor beta (unat (seq_to_word v))"
    using unat_lt2p[of "seq_to_word v"]
    by (subst Cantor.cantor_sum[of _ 64]) (simp_all add: bit_unsigned_iff cong: if_cong)
  finally show ?thesis .
qed

end
