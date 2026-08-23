(* Title:      MLDSA_Reduce/MLDSA_Reduce.thy
   Author:     Amar Akshat <amar.akshat@gmail.com>, 2026
   License:    BSD 3-clause

   Fixed-width implementations of the ML-DSA reduction layer, and their correctness against the
   contracts in MLDSA_Reduce_Spec.

   SCOPE: this entry relates the definitions below to the specifications, and nothing else. It makes
   no claim that any compiled binary computes these functions.

   The definitions mirror the arithmetic of the widely used reference implementation: Montgomery
   reduction takes the low 32 bits of a * QINV, multiplies by q, subtracts and shifts right by 32.
   Nothing here is generated; the definitions are written out so that a reader can compare them with
   the C by eye, which is the only comparison this entry supports. Establishing that a particular
   binary computes these functions is a separate activity and is not part of this entry. *)

theory MLDSA_Reduce
  imports
    MLDSA_Reduce_Spec
    "Word_Lib.Word_Lemmas"
    "Word_Lib.Bit_Shifts_Infix_Syntax"
    "Word_Lib.Most_significant_bit"
begin

unbundle bit_operations_syntax

section \<open>Montgomery reduction\<close>

text \<open>\<open>QINV\<close> is the inverse of \<open>q\<close> modulo \<open>2 ^ 32\<close>, as fixed by the reference implementation
\<^cite>\<open>"dilithium_ref"\<close>: \<open>QINV * q = 1 + 2 ^ 32 * 114592\<close>. That multiplier 114592 is what the
proof of the arithmetic core uses when it exhibits its witness.\<close>

definition QINV :: "64 word" where "QINV = 58728449"

definition montgomery_reduce :: "64 word \<Rightarrow> 32 word" where
  "montgomery_reduce a =
     (let t = (ucast (a * QINV) :: 32 word)
      in ucast (sshiftr (a - scast t * 8380417) 32))"

lemma sint_ucast_fit:
  fixes V :: "64 word"
  assumes "- 2147483648 \<le> sint V" and "sint V < 2147483648"
  shows "sint (ucast V :: 32 word) = sint V"
proof -
  have "sint (ucast V :: 32 word) = sint (scast V :: 32 word)"
    by (simp add: scast_ucast_down_same)
  also have "\<dots> = signed_take_bit 31 (sint V)"
    by (simp add: signed_scast_eq)
  also have "\<dots> = sint V" using assms by (simp add: signed_take_bit_int_eq_self)
  finally show ?thesis .
qed

lemma red_value:
  fixes aw :: "64 word" and t32 :: "32 word"
  assumes Alo: "- (2147483648 * 8380417) \<le> sint aw" and Ahi: "sint aw < 2147483648 * 8380417"
  shows "sint (ucast (sshiftr (aw - scast t32 * 8380417) 32) :: 32 word)
       = (sint aw - sint t32 * 8380417) div 4294967296"
proof -
  have e1: "(2147483648::int) * 8380417 = 17996808470921216" by simp
  have t_lo: "(- 2147483648::int) \<le> sint t32" using sint_greater_eq[of t32] by simp
  have t_hi: "sint t32 \<le> 2147483647" using sint_lt[of t32] by simp
  have tq_lo: "- 17996808470921216 \<le> sint t32 * 8380417"
    using mult_right_mono[OF t_lo, of 8380417] by simp
  have tq_hi: "sint t32 * 8380417 \<le> 17996808462540799"
    using mult_right_mono[OF t_hi, of 8380417] by simp
  have hom: "aw - scast t32 * 8380417 = (of_int (sint aw - sint t32 * 8380417) :: 64 word)"
    by (simp add: of_int_sint_scast)
  have fitX: "- 9223372036854775808 \<le> sint aw - sint t32 * 8380417
            \<and> sint aw - sint t32 * 8380417 < 9223372036854775808"
    using Alo Ahi tq_lo tq_hi e1 by linarith
  have sintX: "sint (aw - scast t32 * 8380417) = sint aw - sint t32 * 8380417"
    unfolding hom by (rule sint_of_int_eq; (use fitX in simp))
  have sh: "sint (sshiftr (aw - scast t32 * 8380417) 32) = (sint aw - sint t32 * 8380417) div 4294967296"
    using sintX by (simp add: sshiftr_div_2n)
  have ub: "sint aw - sint t32 * 8380417 < 35993616941842432" using Ahi tq_lo e1 by linarith
  have lb: "- 35993616941842432 \<le> sint aw - sint t32 * 8380417" using Alo tq_hi e1 by linarith
  have v_hi: "(sint aw - sint t32 * 8380417) div 4294967296 < 2147483648"
  proof -
    have "(sint aw - sint t32 * 8380417) div 4294967296 \<le> 35993616941842431 div 4294967296"
      using ub by (auto intro: zdiv_mono1)
    thus ?thesis by simp
  qed
  have v_lo: "- 2147483648 \<le> (sint aw - sint t32 * 8380417) div 4294967296"
  proof -
    have "(- 35993616941842432) div (4294967296::int) \<le> (sint aw - sint t32 * 8380417) div 4294967296"
      using lb by (auto intro: zdiv_mono1)
    thus ?thesis by simp
  qed
  have Vfit: "- 2147483648 \<le> sint (sshiftr (aw - scast t32 * 8380417) 32)
            \<and> sint (sshiftr (aw - scast t32 * 8380417) 32) < 2147483648"
    using v_lo v_hi unfolding sh by simp
  show ?thesis
    using sint_ucast_fit[OF conjunct1[OF Vfit] conjunct2[OF Vfit]] sh by simp
qed

lemma tcong:
  fixes aw :: "64 word"
  shows "(sint (ucast (aw * 58728449) :: 32 word) - sint aw * 58728449) mod 4294967296 = 0"
proof -
  have stb: "sint (ucast (aw * 58728449) :: 32 word) = signed_take_bit 31 (sint (aw * 58728449))"
  proof -
    have "sint (ucast (aw * 58728449) :: 32 word) = sint (scast (aw * 58728449) :: 32 word)"
      by (simp add: scast_ucast_down_same)
    thus ?thesis by (simp add: signed_scast_eq)
  qed
  have m1: "signed_take_bit 31 (sint (aw * 58728449)) mod 4294967296
          = sint (aw * 58728449) mod 4294967296"
    by (simp add: signed_take_bit_eq_take_bit_shift take_bit_eq_mod mod_diff_left_eq)
  have su: "\<And>y::64 word. sint y mod 4294967296 = uint y mod 4294967296"
  proof -
    fix y :: "64 word"
    have key: "(uint y - 18446744073709551616) mod 4294967296 = uint y mod 4294967296"
      using mod_mult_self1[of "uint y" "- 4294967296" 4294967296] by simp
    show "sint y mod 4294967296 = uint y mod 4294967296"
      using key by (simp add: word_sint_msb_eq size_word.rep_eq)
  qed
  have m2: "sint (aw * 58728449) mod 4294967296 = (sint aw * 58728449) mod 4294967296"
  proof -
    have "sint (aw * 58728449) mod 4294967296 = uint (aw * 58728449) mod 4294967296" by (rule su)
    also have "\<dots> = (uint aw * 58728449) mod 4294967296"
      by (simp add: uint_word_ariths(3) take_bit_eq_mod mod_mod_cancel)
    also have "\<dots> = (sint aw * 58728449) mod 4294967296"
      by (rule mod_mult_cong[OF su[of aw, symmetric] refl])
    finally show ?thesis .
  qed
  have "sint (ucast (aw * 58728449) :: 32 word) mod 4294967296 = (sint aw * 58728449) mod 4294967296"
    using stb m1 m2 by simp
  thus ?thesis by (simp add: mod_eq_dvd_iff)
qed

theorem montgomery_reduce_correct:
  fixes a :: "64 word"
  assumes A: "mont_input_ok (sint a)"
  shows "is_montgomery_reduction (sint a) (sint (montgomery_reduce a))"
proof -
  define t32 :: "32 word" where "t32 = (ucast (a * 58728449) :: 32 word)"
  have Arng: "- (2147483648 * 8380417) \<le> sint a \<and> sint a < 2147483648 * 8380417"
    using A unfolding mont_input_ok_def q_def by simp
  have rval: "sint (montgomery_reduce a) = (sint a - sint t32 * 8380417) div 4294967296"
    unfolding montgomery_reduce_def QINV_def t32_def Let_def
    by (rule red_value[OF conjunct1[OF Arng] conjunct2[OF Arng]])
  have Tcong: "(sint t32 - sint a * 58728449) mod 4294967296 = 0"
    unfolding t32_def by (rule tcong)
  have Trng: "- 2147483648 \<le> sint t32 \<and> sint t32 < 2147483648"
    using sint_greater_eq[of t32] sint_lt[of t32] by simp
  show ?thesis
    unfolding is_montgomery_reduction_def q_def rval
    using mont_core[OF Tcong conjunct1[OF Trng] conjunct2[OF Trng]
                       conjunct1[OF Arng] conjunct2[OF Arng]]
    by simp
qed

section \<open>The rest of the reduction layer\<close>

text \<open>\<open>caddq\<close> adds \<open>q\<close> exactly when its argument is negative, using the sign mask rather than a
branch. \<open>reduce32\<close> is the Barrett-style reduction of the reference implementation, and \<open>freeze\<close> is
their composition, giving the canonical representative in \<open>[0, q)\<close>. The definitions are written out so
that a reader can compare them with the reference implementation \<^cite>\<open>"dilithium_ref"\<close> line by
line; that comparison is the only one this entry supports, since nothing here concerns compiled
code.\<close>

definition caddq :: "32 word \<Rightarrow> 32 word" where
  "caddq a = a + (sshiftr a 31 AND 0x7FE001)"

definition reduce32 :: "32 word \<Rightarrow> 32 word" where
  "reduce32 a = a - sshiftr (a + 0x400000) 23 * 0x7FE001"

definition freeze :: "32 word \<Rightarrow> 32 word" where
  "freeze a = caddq (reduce32 a)"

theorem caddq_correct:
  fixes a :: "32 word"
  shows "is_caddq (sint a) (sint (caddq a))"
proof -
  define aw :: "32 word" where "aw = a"
  have A: "sint a = sint aw" unfolding aw_def by simp
  have br: "sint (caddq a) = sint (aw + (sshiftr aw 31 AND 0x7FE001))"
    unfolding caddq_def aw_def by simp
  have lo: "- 2147483648 \<le> sint aw" and hi: "sint aw < 2147483648"
    using sint_greater_eq[of aw] sint_lt[of aw] by simp_all
  \<comment> \<open>the shift-AND selects q iff aw is negative\<close>
  have sel: "(sshiftr aw 31 AND (0x7FE001 :: 32 word)) = (if sint aw < 0 then 0x7FE001 else 0)"
    by (intro bit_word_eqI)
       (auto simp: bit_simps word_msb_sint[symmetric] msb_word_iff_bit not_le less_Suc0)
  \<comment> \<open>sint of the sum: no int32 overflow either way\<close>
  have val: "sint (aw + (sshiftr aw 31 AND 0x7FE001)) = sint aw + (if sint aw < 0 then 8380417 else 0)"
  proof (cases "sint aw < 0")
    case True
    have b1: "- 2147483648 \<le> sint aw + 8380417" using lo by simp
    have b2: "sint aw + 8380417 < 2147483648" using True by simp
    have "sint (aw + 0x7FE001) = sint (word_of_int (sint aw + 8380417) :: 32 word)"
      by (metis of_int_add of_int_numeral of_int_sint)
    also have "\<dots> = sint aw + 8380417"
      by (rule sint_of_int_eq) (use b1 b2 in simp)+
    finally show ?thesis using sel True by simp
  next
    case False thus ?thesis using sel by simp
  qed
  show ?thesis
    unfolding is_caddq_def q_def A br val
    using lo hi by (auto simp: mod_add_self2)
qed

theorem reduce32_correct:
  fixes a :: "32 word"
  assumes dom: "reduce32_input_ok (sint a)"
  shows "is_reduce32 (sint a) (sint (reduce32 a))"
proof -
  define aw :: "32 word" where "aw = a"
  define a' :: int where "a' = sint aw"
  have A: "sint a = a'" unfolding aw_def a'_def by simp
  have lo31: "- 2147483648 \<le> a'" and hi31: "a' < 2147483648"
    unfolding a'_def using sint_greater_eq[of aw] sint_lt[of aw] by simp_all
  have dom': "a' \<le> 2143289343" using dom A unfolding reduce32_input_ok_def by simp
  \<comment> \<open>the shifted addend does not overflow a signed 32-bit word, so its signed value is exactly a' plus two-to-the-22\<close>
  have add_eq: "aw + 0x400000 = word_of_int (a' + 4194304)"
    unfolding a'_def by (metis of_int_add of_int_numeral of_int_sint)
  have sint_add: "sint (aw + 0x400000) = a' + 4194304"
    unfolding add_eq by (rule sint_of_int_eq) (use lo31 dom' in simp)+
  \<comment> \<open>the arithmetic shift is exactly floor division by two-to-the-23\<close>
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
  have R: "sint (reduce32 a) = a' - t * 8380417"
  proof -
    have "sint (reduce32 a) = sint (aw - sshiftr (aw + 0x400000) 23 * 0x7FE001)"
      unfolding reduce32_def aw_def by simp
    also have "\<dots> = sint (word_of_int (a' - t * 8380417) :: 32 word)"
      using hom by simp
    also have "\<dots> = a' - t * 8380417"
      by (rule sint_of_int_eq) (use BND in simp)+
    finally show ?thesis .
  qed
  \<comment> \<open>residue preservation: a' - t*Q is congruent to a' (mod Q)\<close>
  have cong: "(a' - t * 8380417) mod 8380417 = a' mod 8380417"
    using mod_mult_self1[of a' "- t" 8380417] by (simp add: algebra_simps)
  show ?thesis
    unfolding is_reduce32_def q_def A R
    using BND cong by simp
qed

theorem freeze_correct:
  fixes a :: "32 word"
  assumes dom: "reduce32_input_ok (sint a)"
  shows "is_freeze (sint a) (sint (freeze a))"
proof -
  have r32: "is_reduce32 (sint a) (sint (reduce32 a))"
    using dom by (rule reduce32_correct)
  have cad: "is_caddq (sint (reduce32 a)) (sint (caddq (reduce32 a)))"
    by (rule caddq_correct)
  have c1: "sint (reduce32 a) mod 8380417 = sint a mod 8380417"
   and b1: "- 6283009 \<le> sint (reduce32 a)" and b2: "sint (reduce32 a) \<le> 6283008"
    using r32 unfolding is_reduce32_def q_def by simp_all
  have c2: "sint (caddq (reduce32 a)) mod 8380417 = sint (reduce32 a) mod 8380417"
    using cad unfolding is_caddq_def q_def by simp
  have ante: "- 8380417 \<le> sint (reduce32 a) \<and> sint (reduce32 a) < 8380417"
    using b1 b2 by linarith
  have pos: "0 \<le> sint (caddq (reduce32 a)) \<and> sint (caddq (reduce32 a)) < 8380417"
    using cad ante unfolding is_caddq_def q_def by simp
  have fdef: "sint (freeze a) = sint (caddq (reduce32 a))"
    by (simp add: freeze_def)
  show ?thesis
    unfolding is_freeze_def q_def fdef
    using c1 c2 pos by simp
qed

end
