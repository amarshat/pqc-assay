theory ViewBridge
  imports DecBridge HQC.FFTTop
begin

lemma flat32_list: "seq_to_list (FFTBC.flat32 TY('n::len) (v :: ('n, (32, bool) seq) seq)) = concat (map seq_to_list (rev (seq_to_list v)))"
  by (simp add: FFTBC.flat32_def seq_to_list)

lemma unflat32_list: "seq_to_list (FFTBC.unflat32 TY('n::len) (v :: (32 \<times> 'n, bool) seq)) = rev (map list_to_seq (group_list LENGTH('n) 32 (seq_to_list v)))"
  by (simp add: FFTBC.unflat32_def seq_to_list)

theorem flat32_unflat32: "FFTBC.flat32 TY('n::len) (FFTBC.unflat32 TY('n) (v :: (32 \<times> 'n, bool) seq)) = v"
proof -
  have g: "\<forall>x\<in>set (group_list LENGTH('n) 32 (seq_to_list v)). length x = 32"
    using group_list_grouped[of "seq_to_list v" "LENGTH('n)" 32] by simp
  have m: "map (\<lambda>x. seq_to_list (list_to_seq x :: (32, bool) seq)) (group_list LENGTH('n) 32 (seq_to_list v))
      = group_list LENGTH('n) 32 (seq_to_list v)"
    by (rule map_idI) (use g in simp)
  have "seq_to_list (FFTBC.flat32 TY('n) (FFTBC.unflat32 TY('n) v)) = seq_to_list v"
    by (simp add: flat32_list unflat32_list comp_def m concat_group_list_inv)
  then show ?thesis by (metis seq_preserved)
qed

lemma bc1w_bits:
  fixes v :: "(512, (32, bool) seq) seq"
  shows "FFTBC.flat32 TY(512) (FFTBC.bc1w v)
       = coerce_seq_len (FFTBC.bc1of256 TY(64) (coerce_seq_len (FFTBC.bc256of16384 (FFTBC.repr16384 (coerce_seq_len (FFTBC.flat32 TY(512) v))))))"
  by (simp add: FFTBC.bc1w_def FFTBC.bc1of256W_def FFTBC.bc256W_def FFTBC.reprW_def flat32_unflat32)

lemma take_drop_64: "seq_to_list (take' TY(32) TY(32) TY(bool) (coerce_seq_len x :: (32 + 32, bool) seq))
     @ seq_to_list (drop' TY(32) TY(32) TY(bool) (coerce_seq_len x :: (32 + 32, bool) seq)) = seq_to_list (x :: w64)"
  by (simp add: seq_to_list coerce_seq_len.rep_eq)

lemma as32_list: "seq_to_list (FFTTop.as32 TY('n::len) (w :: ('n, w64) seq))
    = concat (map (\<lambda>x. [drop' TY(32) TY(32) TY(bool) (coerce_seq_len x), take' TY(32) TY(32) TY(bool) (coerce_seq_len x)]) (seq_to_list w))"
  by (simp add: FFTTop.as32_def seq_to_list comp_def)

lemma concat_pairs: "concat (concat (map (\<lambda>x. [A x, B x]) xs)) = concat (map (\<lambda>x. A x @ B x) xs)"
  by (induction xs) simp_all

theorem flat32_as32: "seq_to_list (FFTBC.flat32 TY(2 \<times> 'n::len) (FFTTop.as32 TY('n) (w :: ('n, w64) seq)))
    = concat (map seq_to_list (rev (seq_to_list w)))"
proof -
  have "seq_to_list (FFTBC.flat32 TY(2 \<times> 'n) (FFTTop.as32 TY('n) w))
      = concat (map seq_to_list (rev (concat (map (\<lambda>x. [drop' TY(32) TY(32) TY(bool) (coerce_seq_len x), take' TY(32) TY(32) TY(bool) (coerce_seq_len x)]) (seq_to_list w)))))"
    by (simp add: flat32_list as32_list)
  also have "\<dots> = concat (map seq_to_list (rev (seq_to_list w)))"
    by (simp add: rev_concat rev_map map_concat comp_def concat_pairs take_drop_64)
  finally show ?thesis .
qed

text \<open>The polynomial of a bit list, most significant bit first (the order of seq_to_list).\<close>

definition PL :: "bool list \<Rightarrow> gf2 poly" where
  "PL l = (\<Sum>p<length l. monom (of_bool (l ! (length l - Suc p))) p)"

lemma coeff_PL: "coeff (PL l) p = of_bool (p < length l \<and> l ! (length l - Suc p))"
  by (auto simp: PL_def coeff_sum sum.delta)

lemma PL_append: "PL (A @ B) = PL B + monom 1 (length B) * PL A"
proof (rule poly_eqI)
  fix p
  show "coeff (PL (A @ B)) p = coeff (PL B + monom 1 (length B) * PL A) p"
  proof (cases "p < length B")
    case True
    have a: "\<not> (length A + length B - Suc p < length A)" using True by arith
    have b: "length A + length B - Suc p - length A = length B - Suc p" using True by arith
    show ?thesis using True by (simp add: coeff_PL coeff_monom_mult nth_append a b)
  next
    case False
    then show ?thesis
      by (auto simp: coeff_PL coeff_monom_mult nth_append)
  qed
qed

lemma pw_PL: "pw (seq_to_word (b :: ('n::len, bool) seq)) = PL (seq_to_list b)"
  by (rule poly_eqI) (simp add: coeff_pw coeff_PL bit_s2w)

lemma Pl_PL: "Pl (map seq_to_word l) = PL (concat (map seq_to_list (rev (l :: w64 list))))"
proof (induction l)
  case Nil then show ?case by (simp add: PL_def)
next
  case (Cons w ws)
  have "PL (concat (map seq_to_list (rev (w # ws)))) = PL (concat (map seq_to_list (rev ws)) @ seq_to_list w)" by simp
  also have "\<dots> = PL (seq_to_list w) + monom 1 64 * PL (concat (map seq_to_list (rev ws)))"
    by (simp add: PL_append)
  finally show ?case using Cons by (simp add: pw_PL)
qed

end
