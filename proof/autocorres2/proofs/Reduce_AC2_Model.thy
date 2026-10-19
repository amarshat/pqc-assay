theory Reduce_AC2_Model imports PQClean_AC2_Base.Reduce_AC2 begin

text \<open>Each theorem states that, on the input window Assay's reduce.c contracts use, the AutoCorres2
  abstraction of the unmodified PQClean C (C-parser semantics) takes no undefined-behaviour guard
  and returns the value of the lifted Cryptol model that SAW proves the LLVM bitcode equal to
  (proof/saw/mldsa_ntt.saw). AutoCorres2's generated ac_corres theorems link each abstraction to
  the C-parser's Simpl semantics of the C. So two independent C semantics agree on these functions.\<close>

context pp_reduce_global_addresses begin

text \<open>Step 1: the Cryptol model of montgomery_reduce as a plain 64/32-bit word expression.\<close>
lemma model_word:
  fixes aw :: "64 word"
  shows "seq_to_word (montgomery_reduce (word_to_seq aw))
       = (ucast (sshiftr (aw - scast (ucast (aw * 58728449) :: 32 word) * 8380417) 32) :: 32 word)"
  unfolding montgomery_reduce_def
  by (simp add: unsigned_take_bit_eq is_up QINV_def Q64_def probe_sext64 seq_to_word
                ucast_up_ucast take_bit_length_eq')

text \<open>Step 2: the 32-bit t is the same bit pattern in both semantics.\<close>
lemma uint_scast_down:
  fixes a :: "64 signed word"
  shows "uint (SCAST(64 signed \<rightarrow> 32 signed) a) = take_bit 32 (sint a)"
  apply (simp only: scast_eq uint_word_of_int_eq)
  apply simp
  done

lemma take32_sint64:
  fixes a :: "64 signed word"
  shows "take_bit 32 (sint a) = take_bit 32 (uint a)"
  apply (simp only: uint_sint[of a])
  apply (simp add: take_bit_take_bit)
  done

lemma mod32_sint64_mult:
  fixes a :: "64 signed word"
  shows "sint a * k mod 4294967296 = uint a * k mod 4294967296"
proof -
  have "sint a * k mod 4294967296 = take_bit 32 (take_bit 32 (sint a) * k)"
    by (simp add: take_bit_eq_mod mod_mult_left_eq)
  also have "\<dots> = take_bit 32 (take_bit 32 (uint a) * k)" by (simp only: take32_sint64)
  also have "\<dots> = uint a * k mod 4294967296" by (simp add: take_bit_eq_mod mod_mult_left_eq)
  finally show ?thesis .
qed

lemma t_word:
  fixes a :: "64 signed word"
  shows "UCAST(32 signed \<rightarrow> 32) (SCAST(64 signed \<rightarrow> 32 signed) a * 0x3802001)
       = (ucast (UCAST(64 signed \<rightarrow> 64) a * 58728449) :: 32 word)"
proof (rule word_uint_eq_iff[THEN iffD2])
  have m64: "uint a mod 18446744073709551616 = uint a"
    using uint_mod_same[of a] by simp
  have L: "uint (UCAST(32 signed \<rightarrow> 32) (SCAST(64 signed \<rightarrow> 32 signed) a * 0x3802001))
         = take_bit 32 (uint a * 58728449)"
    by (simp add: unsigned_ucast_eq uint_word_ariths uint_scast_down take_bit_eq_mod
                  mod_mult_left_eq mod32_sint64_mult m64)
  have R: "uint (ucast (UCAST(64 signed \<rightarrow> 64) a * 58728449) :: 32 word)
         = take_bit 32 (uint a * 58728449)"
    by (simp add: unsigned_ucast_eq uint_word_ariths take_bit_eq_mod mod_mod_cancel m64)
  show "uint (UCAST(32 signed \<rightarrow> 32) (SCAST(64 signed \<rightarrow> 32 signed) a * 0x3802001))
      = uint (ucast (UCAST(64 signed \<rightarrow> 64) a * 58728449) :: 32 word)"
    using L R by simp
qed

text \<open>Step 3: AutoCorres2 side, the shift-and-narrow in signed words (counterpart of red_value).\<close>
lemma red_value_s:
  fixes a :: "64 signed word" and T :: "32 signed word"
  assumes Alo: "- (2147483648 * 8380417) \<le> sint a" and Ahi: "sint a < 2147483648 * 8380417"
  shows "sint (SCAST(64 signed \<rightarrow> 32 signed) ((a - SCAST(32 signed \<rightarrow> 64 signed) T * 0x7FE001) >>> 32))
       = (sint a - sint T * 8380417) div 4294967296"
proof -
  have e1: "(2147483648::int) * 8380417 = 17996808470921216" by simp
  have t_lo: "(- 2147483648::int) \<le> sint T" using sint_greater_eq[of T] by simp
  have t_hi: "sint T \<le> 2147483647" using sint_lt[of T] by simp
  have tq_lo: "- 17996808470921216 \<le> sint T * 8380417"
    using mult_right_mono[OF t_lo, of 8380417] by simp
  have tq_hi: "sint T * 8380417 \<le> 17996808462540799"
    using mult_right_mono[OF t_hi, of 8380417] by simp
  have hom: "a - SCAST(32 signed \<rightarrow> 64 signed) T * 0x7FE001
           = (of_int (sint a - sint T * 8380417) :: 64 signed word)"
    by (simp add: of_int_sint_scast)
  have fitX: "- 9223372036854775808 \<le> sint a - sint T * 8380417
            \<and> sint a - sint T * 8380417 < 9223372036854775808"
    using Alo Ahi tq_lo tq_hi e1 by linarith
  have sintX: "sint (a - SCAST(32 signed \<rightarrow> 64 signed) T * 0x7FE001) = sint a - sint T * 8380417"
    unfolding hom by (rule sint_of_int_eq; (use fitX in simp))
  have sh: "sint ((a - SCAST(32 signed \<rightarrow> 64 signed) T * 0x7FE001) >>> 32)
          = (sint a - sint T * 8380417) div 4294967296"
    using sintX by (simp add: sshiftr_div_2n)
  have ub: "sint a - sint T * 8380417 < 35993616941842432" using Ahi tq_lo e1 by linarith
  have lb: "- 35993616941842432 \<le> sint a - sint T * 8380417" using Alo tq_hi e1 by linarith
  have v_hi: "(sint a - sint T * 8380417) div 4294967296 < 2147483648"
  proof -
    have "(sint a - sint T * 8380417) div 4294967296 \<le> 35993616941842431 div 4294967296"
      using ub by (auto intro: zdiv_mono1)
    thus ?thesis by simp
  qed
  have v_lo: "- 2147483648 \<le> (sint a - sint T * 8380417) div 4294967296"
  proof -
    have "(- 35993616941842432) div (4294967296::int) \<le> (sint a - sint T * 8380417) div 4294967296"
      using lb by (auto intro: zdiv_mono1)
    thus ?thesis by simp
  qed
  have "sint (SCAST(64 signed \<rightarrow> 32 signed) ((a - SCAST(32 signed \<rightarrow> 64 signed) T * 0x7FE001) >>> 32))
      = signed_take_bit 31 (sint ((a - SCAST(32 signed \<rightarrow> 64 signed) T * 0x7FE001) >>> 32))"
    by (simp add: signed_scast_eq)
  also have "\<dots> = (sint a - sint T * 8380417) div 4294967296"
    unfolding sh using v_lo v_hi by (simp add: signed_take_bit_int_eq_self)
  finally show ?thesis .
qed

text \<open>Same-length reinterpretation keeps the signed value.\<close>
lemma uint_ucast_same:
  assumes "LENGTH('a::len) = LENGTH('b::len)"
  shows "uint (UCAST('a \<rightarrow> 'b) w) = uint w"
proof -
  have "take_bit LENGTH('a) (uint w) = uint w" by (simp add: take_bit_int_eq_self uint_lt2p)
  then show ?thesis using assms by (simp add: unsigned_ucast_eq)
qed

lemma sint_ucast_same64: "sint (UCAST(64 signed \<rightarrow> 64) (a :: 64 signed word)) = sint a"
  by (simp add: sint_uint uint_ucast_same)

lemma sint_ucast_same32: "sint (UCAST(32 signed \<rightarrow> 32) (tw :: 32 signed word)) = sint tw"
  by (simp add: sint_uint uint_ucast_same)

lemma sint_ucast_same32': "sint (UCAST(32 \<rightarrow> 32 signed) (w :: 32 word)) = sint w"
  by (simp add: sint_uint uint_ucast_same)

lemma word32s_eq_by_sint:
  fixes x y :: "32 signed word"
  assumes "sint x = sint y" shows "x = y"
  by (metis assms of_int_sint)

text \<open>Main result: on montgomery_reduce's documented input window, the AutoCorres2 abstraction of the
  unmodified PQClean C (C-parser semantics, arithmetic right shift, no signed word abstraction for
  this function) takes no undefined-behaviour guard and returns the value of the lifted Cryptol model
  that SAW proves the LLVM bitcode equal to.\<close>
theorem montgomery_reduce_ac2_model:
  fixes a :: "64 signed word"
  assumes ok: "mont_input_ok (sint a)"
  shows "PQCLEAN_MLDSA44_CLEAN_montgomery_reduce' a
       = oreturn (UCAST(32 \<rightarrow> 32 signed)
                   (seq_to_word (montgomery_reduce (word_to_seq (UCAST(64 signed \<rightarrow> 64) a)))))"
proof -
  define tw where "tw = SCAST(64 signed \<rightarrow> 32 signed) a * 0x3802001"
  define aw where "aw = UCAST(64 signed \<rightarrow> 64) a"
  define t32 where "t32 = (ucast (aw * 58728449) :: 32 word)"
  have Arng: "- (2147483648 * 8380417) \<le> sint a \<and> sint a < 2147483648 * 8380417"
    using ok unfolding mont_input_ok_def MLDSA_NTT_Spec.q_def by simp
  have saw: "sint aw = sint a" unfolding aw_def by (rule sint_ucast_same64)
  have st: "sint t32 = sint tw"
    unfolding t32_def aw_def tw_def using t_word[of a] sint_ucast_same32 by metis
  have model: "sint (seq_to_word (montgomery_reduce (word_to_seq aw)))
             = (sint a - sint tw * 8380417) div 4294967296"
    unfolding model_word using red_value[of aw "t32"] Arng saw st unfolding t32_def by simp
  have ac2: "sint (SCAST(64 signed \<rightarrow> 32 signed) ((a - SCAST(32 signed \<rightarrow> 64 signed) tw * 0x7FE001) >>> 32))
           = (sint a - sint tw * 8380417) div 4294967296"
    using red_value_s Arng by blast
  have val: "SCAST(64 signed \<rightarrow> 32 signed) ((a - SCAST(32 signed \<rightarrow> 64 signed) tw * 0x7FE001) >>> 32)
           = UCAST(32 \<rightarrow> 32 signed) (seq_to_word (montgomery_reduce (word_to_seq aw)))"
    by (rule word32s_eq_by_sint) (simp add: ac2 model sint_ucast_same32')
  have t_lo: "(- 2147483648::int) \<le> sint tw" using sint_greater_eq[of tw] by simp
  have t_hi: "sint tw \<le> 2147483647" using sint_lt[of tw] by simp
  have tq_lo: "- 17996808470921216 \<le> sint tw * 8380417"
    using mult_right_mono[OF t_lo, of 8380417] by simp
  have tq_hi: "sint tw * 8380417 \<le> 17996808462540799"
    using mult_right_mono[OF t_hi, of 8380417] by simp
  have guard: "- (LONG_MAX + 1) \<le> sint a - sint (SCAST(32 signed \<rightarrow> 64 signed) tw) * 8380417
             \<and> sint a - sint (SCAST(32 signed \<rightarrow> 64 signed) tw) * 8380417 \<le> LONG_MAX
             \<and> - (LONG_MAX + 1) \<le> sint (SCAST(32 signed \<rightarrow> 64 signed) tw) * 8380417
             \<and> sint (SCAST(32 signed \<rightarrow> 64 signed) tw) * 8380417 \<le> LONG_MAX"
    using Arng tq_lo tq_hi by (simp add: sint_up_scast is_up LONG_MAX_def)
  have prod: "sint (SCAST(32 signed \<rightarrow> 64 signed) tw * 0x7FE001) = sint tw * 8380417"
  proof -
    have "sint (SCAST(32 signed \<rightarrow> 64 signed) tw * 0x7FE001)
        = signed_take_bit 63 (sint tw * 8380417)"
      by (simp add: sint_word_ariths sint_up_scast is_up)
    also have "\<dots> = sint tw * 8380417"
      using tq_lo tq_hi by (simp add: signed_take_bit_int_eq_self)
    finally show ?thesis .
  qed
  show ?thesis
    unfolding PQCLEAN_MLDSA44_CLEAN_montgomery_reduce'_def
    using guard val prod Arng tq_lo tq_hi unfolding tw_def aw_def
    by (simp add: sint_up_scast is_up oguard_def obind_def oreturn_def LONG_MAX_def K_def fun_eq_iff ucast_scast_id)
qed

text \<open>caddq: the model as an integer (steps of Assay_Equivalence.caddq_correct).\<close>
lemma caddq_model_int:
  fixes w :: "32 word"
  shows "sint (seq_to_word (caddq (word_to_seq w))) = sint w + (if sint w < 0 then 8380417 else 0)"
proof -
  have br: "seq_to_word (caddq (word_to_seq w)) = w + (sshiftr w 31 AND 0x7FE001)"
    unfolding caddq_def Q32_def by (simp add: word_seq_convs seq_to_word)
  have lo: "- 2147483648 \<le> sint w" and hi: "sint w < 2147483648"
    using sint_greater_eq[of w] sint_lt[of w] by simp_all
  have sel: "(sshiftr w 31 AND (0x7FE001 :: 32 word)) = (if sint w < 0 then 0x7FE001 else 0)"
    by (intro bit_word_eqI)
       (auto simp: bit_simps word_msb_sint[symmetric] msb_word_iff_bit not_le less_Suc0)
  show ?thesis
  proof (cases "sint w < 0")
    case True
    have b1: "- 2147483648 \<le> sint w + 8380417" using lo by simp
    have b2: "sint w + 8380417 < 2147483648" using True by simp
    have "sint (w + 0x7FE001) = sint (word_of_int (sint w + 8380417) :: 32 word)"
      by (metis of_int_add of_int_numeral of_int_sint)
    also have "\<dots> = sint w + 8380417"
      by (rule sint_of_int_eq) (use b1 b2 in simp)+
    finally show ?thesis using sel True br by simp
  next
    case False thus ?thesis using sel br by simp
  qed
qed

lemma sint_sshiftr31_32s:
  fixes x :: int
  assumes "- 2147483648 \<le> x" "x < 2147483648"
  shows "sint ((word_of_int x :: 32 signed word) >>> 31) = (if x < 0 then -1 else 0)"
proof -
  have sx: "sint (word_of_int x :: 32 signed word) = x"
    by (rule sint_of_int_eq) (use assms in simp)+
  have "sint ((word_of_int x :: 32 signed word) >>> 31) = x div 2147483648"
    using sx by (simp add: sshiftr_div_2n)
  also have "\<dots> = (if x < 0 then -1 else 0)"
    using assms by (auto simp: div_eq_minus1 div_pos_pos_trivial)
  finally show ?thesis .
qed

theorem caddq_ac2_model:
  fixes w :: "32 word"
  shows "PQCLEAN_MLDSA44_CLEAN_caddq' (sint w) = oreturn (sint (seq_to_word (caddq (word_to_seq w))))"
proof -
  have lo: "- 2147483648 \<le> sint w" and hi: "sint w < 2147483648"
    using sint_greater_eq[of w] sint_lt[of w] by simp_all
  have sh: "sint ((word_of_int (sint w) :: 32 signed word) >>> 31) = (if sint w < 0 then -1 else 0)"
    using sint_sshiftr31_32s[OF lo hi] .
  have andq: "(if sint w < 0 then -1 else 0) AND (8380417::int) = (if sint w < 0 then 8380417 else 0)"
    by simp
  show ?thesis
    unfolding PQCLEAN_MLDSA44_CLEAN_caddq'_def caddq_model_int
    using lo hi sh
    by (auto simp: oguard_def obind_def oreturn_def K_def fun_eq_iff INT_MAX_def)
qed

text \<open>reduce32: the model as an integer (the value step of Assay_Equivalence.reduce32_correct).\<close>
lemma reduce32_model_int:
  fixes a :: "(32, bool) seq"
  assumes dom: "reduce32_input_ok (sint_seq a)"
  shows "sint_seq (reduce32 a) = sint_seq a - ((sint_seq a + 4194304) div 8388608) * 8380417"
proof -
  define aw :: "32 word" where "aw = seq_to_word a"
  define a' :: int where "a' = sint aw"
  have A: "sint_seq a = a'" unfolding aw_def a'_def by (rule probe_sint_seq)
  have lo31: "- 2147483648 \<le> a'" and hi31: "a' < 2147483648"
    unfolding a'_def using sint_greater_eq[of aw] sint_lt[of aw] by simp_all
  have dom': "a' \<le> 2143289343" using dom A unfolding reduce32_input_ok_def by simp
  \<comment> \<open>the shifted addend does not overflow int32, so its signed value is exactly a' + 2^22\<close>
  have add_eq: "aw + 0x400000 = word_of_int (a' + 4194304)"
    unfolding a'_def by (metis of_int_add of_int_numeral of_int_sint)
  have sint_add: "sint (aw + 0x400000) = a' + 4194304"
    unfolding add_eq by (rule sint_of_int_eq) (use lo31 dom' in simp)+
  \<comment> \<open>the arithmetic shift is exactly floor-division by 2^23\<close>
  define t :: int where "t = (a' + 4194304) div 8388608"
  have sint_t: "sint (sshiftr (aw + 0x400000) 23) = t"
    unfolding t_def using sint_add by (simp add: sshiftr_div_2n)
  \<comment> \<open>quotient bounds from the input range\<close>
  have aplo: "- 2143289344 \<le> a' + 4194304" using lo31 by simp
  have aphi: "a' + 4194304 \<le> 2147483647" using dom' by simp
  have thi: "t \<le> 255"
  proof -
    have "(a' + 4194304) div 8388608 \<le> 2147483647 div 8388608"
      using aphi by (auto intro: zdiv_mono1)
    thus ?thesis unfolding t_def by simp
  qed
  have tlo: "- 256 \<le> t"
  proof -
    have "(- 2143289344 :: int) div 8388608 \<le> (a' + 4194304) div 8388608"
      using aplo by (auto intro: zdiv_mono1)
    thus ?thesis unfolding t_def by simp
  qed
  \<comment> \<open>the integer output bound (the hard interval fact)\<close>
  define s :: int where "s = (a' + 4194304) mod 8388608"
  have eqn: "a' + 4194304 = 8388608 * t + s"
    unfolding t_def s_def by simp
  have s0: "0 \<le> s" and s1: "s < 8388608" unfolding s_def by simp_all
  have rfix: "a' - t * 8380417 = 8191 * t + s - 4194304" using eqn by (simp add: algebra_simps)
  have BND: "- 6283009 \<le> a' - t * 8380417 \<and> a' - t * 8380417 \<le> 6283008"
  proof -
    have up: "8191 * t + s - 4194304 \<le> 6283008" using thi s1 by linarith
    have low: "- 6283009 \<le> 8191 * t + s - 4194304"
    proof (cases "t \<le> - 256")
      case True
      hence te: "t = - 256" using tlo by linarith
      show ?thesis using te eqn s0 lo31 by linarith
    next
      case False
      hence "- 255 \<le> t" by simp
      thus ?thesis using s0 by linarith
    qed
    show ?thesis using up low rfix by simp
  qed
  \<comment> \<open>collapse the word arithmetic to the integer value, using BND for the no-overflow fit\<close>
  have tw_eq: "sshiftr (aw + 0x400000) 23 = word_of_int t"
    using sint_t by (metis of_int_sint)
  have hom: "aw - sshiftr (aw + 0x400000) 23 * 0x7FE001 = word_of_int (a' - t * 8380417)"
    unfolding tw_eq a'_def
    by (metis of_int_diff of_int_mult of_int_numeral of_int_sint)
  have R: "sint_seq (reduce32 a) = a' - t * 8380417"
  proof -
    have "sint_seq (reduce32 a) = sint (aw - sshiftr (aw + 0x400000) 23 * 0x7FE001)"
      unfolding reduce32_def Q32_def aw_def
      by (simp add: probe_sint_seq word_seq_convs seq_to_word shl22)
    also have "\<dots> = sint (word_of_int (a' - t * 8380417) :: 32 word)"
      using hom by simp
    also have "\<dots> = a' - t * 8380417"
      by (rule sint_of_int_eq) (use BND in simp)+
    finally show ?thesis .
  qed
  show ?thesis using R A unfolding t_def by simp
qed

theorem reduce32_ac2_model:
  fixes w :: "32 word"
  assumes dom: "reduce32_input_ok (sint w)"
  shows "PQCLEAN_MLDSA44_CLEAN_reduce32' (sint w) = oreturn (sint (seq_to_word (reduce32 (word_to_seq w))))"
proof -
  have lo: "- 2147483648 \<le> sint w" and hi: "sint w < 2147483648"
    using sint_greater_eq[of w] sint_lt[of w] by simp_all
  have d: "sint w \<le> 2143289343" using dom unfolding reduce32_input_ok_def .
  have sw: "sint_seq (word_to_seq w) = sint w" by (simp add: probe_sint_seq word_seq_convs)
  have model: "sint (seq_to_word (reduce32 (word_to_seq w)))
             = sint w - ((sint w + 4194304) div 8388608) * 8380417"
    using reduce32_model_int[of "word_to_seq w"] dom sw by (simp add: probe_sint_seq)
  have addw: "(word_of_int (sint w) :: 32 signed word) + 0x400000 = word_of_int (sint w + 4194304)"
    by simp
  have sadd: "sint ((word_of_int (sint w) :: 32 signed word) + 0x400000) = sint w + 4194304"
    unfolding addw by (rule sint_of_int_eq) (use lo d in simp)+
  have sh: "sint ((word_of_int (sint w) :: 32 signed word) + 0x400000 >>> 23) = (sint w + 4194304) div 8388608"
    using sadd by (simp add: sshiftr_div_2n)
  define t where "t = (sint w + 4194304) div 8388608"
  have thi: "t \<le> 255"
  proof -
    have "(sint w + 4194304) div 8388608 \<le> 2147483647 div 8388608" using d by (auto intro: zdiv_mono1)
    thus ?thesis unfolding t_def by simp
  qed
  have tlo: "- 256 \<le> t"
  proof -
    have "(- 2143289344 :: int) div 8388608 \<le> (sint w + 4194304) div 8388608" using lo by (auto intro: zdiv_mono1)
    thus ?thesis unfolding t_def by simp
  qed
  show ?thesis
    unfolding PQCLEAN_MLDSA44_CLEAN_reduce32'_def model
    using lo hi d sh thi tlo unfolding t_def[symmetric]
    by (auto simp: oguard_def obind_def oreturn_def K_def fun_eq_iff INT_MAX_def t_def)
qed

theorem freeze_ac2_model:
  fixes w :: "32 word"
  assumes dom: "reduce32_input_ok (sint w)"
  shows "PQCLEAN_MLDSA44_CLEAN_freeze' (sint w) = oreturn (sint (seq_to_word (freeze (word_to_seq w))))"
proof -
  define r where "r = seq_to_word (reduce32 (word_to_seq w))"
  have rt: "word_to_seq r = reduce32 (word_to_seq w)" unfolding r_def by (simp add: word_seq_convs)
  show ?thesis
    unfolding PQCLEAN_MLDSA44_CLEAN_freeze'_def reduce32_ac2_model[OF dom] freeze_def
    using caddq_ac2_model[of r] rt unfolding r_def[symmetric]
    by (simp add: obind_def oreturn_def K_def fun_eq_iff)
qed

end
end
