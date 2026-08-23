(* Title:      MLDSA_Reduce/MLDSA_Reduce.thy
   Author:     Amar Akshat <amar.akshat@gmail.com>, 2026
   License:    BSD 3-clause

   Fixed-width implementations of the ML-DSA reduction layer, and their correctness against the
   contracts in MLDSA_Reduce_Spec.

   SCOPE: this entry relates the definitions below to the specifications, and nothing else. It makes
   no claim that any compiled binary computes these functions.

   The definitions mirror the arithmetic of the widely used reference implementation: Montgomery
   reduction takes the low 32 bits of a * mldsa_QINV, multiplies by mldsa_q, subtracts and shifts right by 32.
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

text \<open>\<open>mldsa_QINV\<close> is the inverse of \<open>q\<close> modulo \<open>2 ^ 32\<close>, as fixed by the reference implementation
\<^cite>\<open>"pqclean_mldsa"\<close>. That is proved as \<open>qinv_inverts_q\<close> below rather than asserted here, and
the cofactor 114592 it exposes is the multiplier the arithmetic core uses for its witness.

The Montgomery step is modelled as the low 32 bits of the 64-bit product, which is how PQClean writes
it. The CRYSTALS-Dilithium reference \<^cite>\<open>"dilithium_ref"\<close>, from which PQClean's copy derives,
writes the same step as a signed product of the truncated input; the two agree on the low 32 bits, which
is all either uses.\<close>

definition mldsa_QINV :: "64 word" where "mldsa_QINV = 58728449"

lemma QINV_is_qinv: "mldsa_QINV = word_of_int mldsa_qinv"
  unfolding mldsa_QINV_def mldsa_qinv_def by simp

definition mldsa_montgomery_reduce :: "64 word \<Rightarrow> 32 word" where
  "mldsa_montgomery_reduce a =
     (let t = (ucast (a * mldsa_QINV) :: 32 word)
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

section \<open>The arithmetic core\<close>

text \<open>If \<open>T\<close> is congruent to \<open>A * mldsa_qinv\<close> modulo \<open>2 ^ 32\<close>, lies in the signed 32-bit range, and \<open>A\<close>
lies in the half-open domain, then \<open>(A - T * mldsa_q) / 2 ^ 32\<close> is a correct Montgomery reduction of \<open>A\<close>.
Every result below reduces to this. The bound on \<open>A\<close> is not optional: without it the conclusion fails
for large \<open>A\<close>.

First the fact that makes the whole layer work, machine-checked rather than asserted: \<open>mldsa_qinv\<close> really
does invert \<open>mldsa_q\<close> modulo \<open>2 ^ 32\<close>, and the cofactor is the multiplier the proof below exhibits.\<close>

lemma qinv_inverts_q: "mldsa_qinv * mldsa_q = 1 + 2 ^ 32 * 114592"
  unfolding mldsa_qinv_def mldsa_q_def by simp

lemma qinv_q_mod: "(mldsa_qinv * mldsa_q) mod (2 ^ 32) = 1"
  unfolding mldsa_qinv_def mldsa_q_def by simp

lemma mont_core_numerals:
  fixes A T :: int
  assumes Tc:  "(T - A * 58728449) mod 4294967296 = 0"
      and Tlo: "- 2147483648 \<le> T" and Thi: "T < 2147483648"
      and Alo: "- (2147483648 * 8380417) \<le> A" and Ahi: "A < 2147483648 * 8380417"
  shows "(4294967296 * ((A - T * 8380417) div 4294967296)) mod 8380417 = A mod 8380417
       \<and> - 8380417 < (A - T * 8380417) div 4294967296
       \<and> (A - T * 8380417) div 4294967296 < 8380417"
proof -
  from Tc have "(4294967296::int) dvd (T - A * 58728449)" by (simp add: mod_eq_0_iff_dvd)
  then obtain k where k: "T - A * 58728449 = 4294967296 * k" by (auto elim: dvdE)
  hence T_eq: "T = A * 58728449 + 4294967296 * k" by simp
  define r where "r = - (A * 114592 + k * 8380417)"
  have D_eq: "A - T * 8380417 = 4294967296 * r"
    unfolding r_def T_eq by (simp add: algebra_simps)
  hence r_is: "(A - T * 8380417) div 4294967296 = r" by simp
  \<comment> \<open>congruence: the reduced value times two-to-the-32 is congruent to A modulo Q, since Q divides T*Q. Note: presburger does not cope with a modulus this large\<close>
  have cong: "(4294967296 * r) mod 8380417 = A mod 8380417"
  proof -
    have eq: "4294967296 * r = A - T * 8380417" using D_eq by simp
    have "(A - T * 8380417) mod (8380417::int) = A mod 8380417"
      using mod_mult_self1[of A "- T" 8380417] by (simp add: algebra_simps)
    thus ?thesis using eq by simp
  qed
  \<comment> \<open>bounds: multiply the range hypotheses by Q, then divide the relation through. Evaluate the big
      numeral products up front so linarith only sees plain integers.\<close>
  have e1: "(2147483648::int) * 8380417 = 17996808470921216" by simp
  have e2: "(4294967296::int) * 8380417 = 35993616941842432" by simp
  have Tq_lo: "T * 8380417 \<ge> - 17996808470921216" using Tlo by (simp add: mult_right_mono)
  have Tq_hi: "T * 8380417 \<le> 17996808462540799" using Thi by (simp add: mult_right_mono)
  have Ahi': "A < 17996808470921216" using Ahi e1 by simp
  have Alo': "- 17996808470921216 \<le> A" using Alo e1 by simp
  have ub: "4294967296 * r < 35993616941842432" using D_eq Ahi' Tq_lo by linarith
  have lb: "- 35993616941842432 < 4294967296 * r" using D_eq Alo' Tq_hi by linarith
  from ub have rub: "r < 8380417" by simp
  from lb have rlb: "- 8380417 < r" by simp
  from cong rub rlb r_is show ?thesis by simp
qed

text \<open>The same statement in terms of the entry's own constants and its specification predicate, which
is the form the results below use.\<close>

theorem mont_core:
  fixes A T :: int
  assumes Tc:  "(T - A * mldsa_qinv) mod (2 ^ 32) = 0"
      and Tlo: "- (2 ^ 31) \<le> T" and Thi: "T < 2 ^ 31"
      and Adom: "mldsa_mont_input_ok A"
  shows "mldsa_is_montgomery_reduction A ((A - T * mldsa_q) div (2 ^ 32))"
proof -
  have "- (2147483648 * 8380417) \<le> A" and "A < 2147483648 * 8380417"
    using Adom unfolding mldsa_mont_input_ok_def mldsa_q_def by simp_all
  thus ?thesis
    using mont_core_numerals[OF Tc[unfolded mldsa_qinv_def, simplified]
                                Tlo[simplified] Thi[simplified]]
    unfolding mldsa_is_montgomery_reduction_def mldsa_q_def by simp
qed

theorem montgomery_reduce_correct:
  fixes a :: "64 word"
  assumes A: "mldsa_mont_input_ok (sint a)"
  shows "mldsa_is_montgomery_reduction (sint a) (sint (mldsa_montgomery_reduce a))"
proof -
  define t32 :: "32 word" where "t32 = (ucast (a * 58728449) :: 32 word)"
  have Arng: "- (2147483648 * 8380417) \<le> sint a \<and> sint a < 2147483648 * 8380417"
    using A unfolding mldsa_mont_input_ok_def mldsa_q_def by simp
  have rval: "sint (mldsa_montgomery_reduce a) = (sint a - sint t32 * 8380417) div 4294967296"
    unfolding mldsa_montgomery_reduce_def mldsa_QINV_def t32_def Let_def
    by (rule red_value[OF conjunct1[OF Arng] conjunct2[OF Arng]])
  have Tcong: "(sint t32 - sint a * mldsa_qinv) mod (2 ^ 32) = 0"
    unfolding t32_def mldsa_qinv_def using tcong by simp
  have Tlo: "- (2 ^ 31) \<le> sint t32" and Thi: "sint t32 < 2 ^ 31"
    using sint_greater_eq[of t32] sint_lt[of t32] by simp_all
  have "mldsa_is_montgomery_reduction (sint a) ((sint a - sint t32 * mldsa_q) div (2 ^ 32))"
    by (rule mont_core[OF Tcong Tlo Thi A])
  thus ?thesis unfolding rval mldsa_q_def by simp
qed

section \<open>The rest of the reduction layer\<close>

text \<open>\<open>mldsa_caddq\<close> adds \<open>q\<close> exactly when its argument is negative, using the sign mask rather than a
branch. \<open>mldsa_reduce32\<close> is the Barrett-style reduction of the reference implementation, and \<open>mldsa_freeze\<close> is
their composition, giving the canonical representative in \<open>[0, q)\<close>. The definitions are written out so
that a reader can compare them with the implementation being modelled, PQClean's ML-DSA-44 clean
\<^cite>\<open>"pqclean_mldsa"\<close>, line by line; that comparison is the only one this entry supports,
since nothing here concerns compiled code.\<close>

definition mldsa_caddq :: "32 word \<Rightarrow> 32 word" where
  "mldsa_caddq a = a + (sshiftr a 31 AND 0x7FE001)"

definition mldsa_reduce32 :: "32 word \<Rightarrow> 32 word" where
  "mldsa_reduce32 a = a - sshiftr (a + 0x400000) 23 * 0x7FE001"

definition mldsa_freeze :: "32 word \<Rightarrow> 32 word" where
  "mldsa_freeze a = mldsa_caddq (mldsa_reduce32 a)"

theorem caddq_value:
  fixes a :: "32 word"
  shows "sint (mldsa_caddq a) = sint a + (if sint a < 0 then mldsa_q else 0)"
proof -
  have lo: "- 2147483648 \<le> sint a" and hi: "sint a < 2147483648"
    using sint_greater_eq[of a] sint_lt[of a] by simp_all
  \<comment> \<open>the shift-AND selects \<open>mldsa_q\<close> exactly when a is negative\<close>
  have sel: "(sshiftr a 31 AND (0x7FE001 :: 32 word)) = (if sint a < 0 then 0x7FE001 else 0)"
    by (intro bit_word_eqI)
       (auto simp: bit_simps word_msb_sint[symmetric] msb_word_iff_bit not_le less_Suc0)
  \<comment> \<open>sint of the sum: no signed 32-bit overflow either way\<close>
  have val: "sint (a + (sshiftr a 31 AND 0x7FE001)) = sint a + (if sint a < 0 then 8380417 else 0)"
  proof (cases "sint a < 0")
    case True
    have b1: "- 2147483648 \<le> sint a + 8380417" using lo by simp
    have b2: "sint a + 8380417 < 2147483648" using True by simp
    have "sint (a + 0x7FE001) = sint (word_of_int (sint a + 8380417) :: 32 word)"
      by (metis of_int_add of_int_numeral of_int_sint)
    also have "\<dots> = sint a + 8380417"
      by (rule sint_of_int_eq) (use b1 b2 in simp)+
    finally show ?thesis using sel True by simp
  next
    case False thus ?thesis using sel by simp
  qed
  show ?thesis unfolding mldsa_caddq_def mldsa_q_def using val by simp
qed

theorem caddq_correct:
  fixes a :: "32 word"
  shows "mldsa_is_caddq (sint a) (sint (mldsa_caddq a))"
proof -
  have lo: "- 2147483648 \<le> sint a" and hi: "sint a < 2147483648"
    using sint_greater_eq[of a] sint_lt[of a] by simp_all
  show ?thesis
    unfolding mldsa_is_caddq_def mldsa_q_def caddq_value[unfolded mldsa_q_def]
    using lo hi by (auto simp: mod_add_self2)
qed

text \<open>As with \<open>mldsa_caddq\<close>, the value equation is the more reusable fact. It and the output bounds come
out of the same argument, so they are established together and then split.\<close>

lemma reduce32_value_and_bounds:
  fixes a :: "32 word"
  assumes dom: "mldsa_reduce32_input_ok (sint a)"
  shows "sint (mldsa_reduce32 a) = sint a - ((sint a + 4194304) div 8388608) * 8380417
       \<and> - 6283009 \<le> sint (mldsa_reduce32 a) \<and> sint (mldsa_reduce32 a) \<le> 6283008"
proof -
  define aw :: "32 word" where "aw = a"
  define a' :: int where "a' = sint aw"
  have A: "sint a = a'" unfolding aw_def a'_def by simp
  \<comment> \<open>both bounds come from the domain predicate now, not from the word type\<close>
  have lo31: "- 2147483648 \<le> a'" using dom A unfolding mldsa_reduce32_input_ok_def by simp
  have hi31: "a' < 2147483648"
    unfolding a'_def using sint_lt[of aw] by simp
  have dom': "a' \<le> 2143289343" using dom A unfolding mldsa_reduce32_input_ok_def by simp
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
  have R: "sint (mldsa_reduce32 a) = a' - t * 8380417"
  proof -
    have "sint (mldsa_reduce32 a) = sint (aw - sshiftr (aw + 0x400000) 23 * 0x7FE001)"
      unfolding mldsa_reduce32_def aw_def by simp
    also have "\<dots> = sint (word_of_int (a' - t * 8380417) :: 32 word)"
      using hom by simp
    also have "\<dots> = a' - t * 8380417"
      by (rule sint_of_int_eq) (use BND in simp)+
    finally show ?thesis .
  qed
  \<comment> \<open>residue preservation: a' - t*Q is congruent to a' (mod Q)\<close>
  have cong: "(a' - t * 8380417) mod 8380417 = a' mod 8380417"
    using mod_mult_self1[of a' "- t" 8380417] by (simp add: algebra_simps)
  have t_eq: "t = (sint a + 4194304) div 8388608" unfolding t_def using A by simp
  show ?thesis using R BND t_eq A by simp
qed

theorem reduce32_value:
  fixes a :: "32 word"
  assumes dom: "mldsa_reduce32_input_ok (sint a)"
  shows "sint (mldsa_reduce32 a) = sint a - ((sint a + 2 ^ 22) div 2 ^ 23) * mldsa_q"
  using reduce32_value_and_bounds[OF dom] unfolding mldsa_q_def by simp

theorem reduce32_correct:
  fixes a :: "32 word"
  assumes dom: "mldsa_reduce32_input_ok (sint a)"
  shows "mldsa_is_reduce32 (sint a) (sint (mldsa_reduce32 a))"
proof -
  have V: "sint (mldsa_reduce32 a) = sint a - ((sint a + 4194304) div 8388608) * 8380417"
   and B: "- 6283009 \<le> sint (mldsa_reduce32 a)" "sint (mldsa_reduce32 a) \<le> 6283008"
    using reduce32_value_and_bounds[OF dom] by simp_all
  have cong: "(sint a - ((sint a + 4194304) div 8388608) * 8380417) mod 8380417 = sint a mod 8380417"
    using mod_mult_self1[of "sint a" "- ((sint a + 4194304) div 8388608)" 8380417]
    by (simp add: algebra_simps)
  show ?thesis unfolding mldsa_is_reduce32_def mldsa_q_def using V B cong by simp
qed

text \<open>The output window in \<open>mldsa_is_reduce32\<close> is not a loose safe bound: both of its endpoints are
attained, and the lower one is the value that the reference implementation's own comment excludes. The
two witnesses are checked here rather than asserted in prose, so the claim that the interval is exact
travels with the entry.\<close>

lemma reduce32_lower_endpoint_attained:
  "sint (mldsa_reduce32 (word_of_int (-2143289344) :: 32 word)) = -6283009"
  by (simp add: mldsa_reduce32_def)

lemma reduce32_upper_endpoint_attained:
  "sint (mldsa_reduce32 (word_of_int 2143289343 :: 32 word)) = 6283008"
  by (simp add: mldsa_reduce32_def)

lemma reduce32_endpoints_in_domain:
  "mldsa_reduce32_input_ok (-2143289344)" "mldsa_reduce32_input_ok 2143289343"
  by (simp_all add: mldsa_reduce32_input_ok_def)

theorem freeze_correct:
  fixes a :: "32 word"
  assumes dom: "mldsa_reduce32_input_ok (sint a)"
  shows "mldsa_is_freeze (sint a) (sint (mldsa_freeze a))"
proof -
  have r32: "mldsa_is_reduce32 (sint a) (sint (mldsa_reduce32 a))"
    using dom by (rule reduce32_correct)
  have cad: "mldsa_is_caddq (sint (mldsa_reduce32 a)) (sint (mldsa_caddq (mldsa_reduce32 a)))"
    by (rule caddq_correct)
  have c1: "sint (mldsa_reduce32 a) mod 8380417 = sint a mod 8380417"
   and b1: "- 6283009 \<le> sint (mldsa_reduce32 a)" and b2: "sint (mldsa_reduce32 a) \<le> 6283008"
    using r32 unfolding mldsa_is_reduce32_def mldsa_q_def by simp_all
  have c2: "sint (mldsa_caddq (mldsa_reduce32 a)) mod 8380417 = sint (mldsa_reduce32 a) mod 8380417"
    using cad unfolding mldsa_is_caddq_def mldsa_q_def by simp
  have ante: "- 8380417 \<le> sint (mldsa_reduce32 a) \<and> sint (mldsa_reduce32 a) < 8380417"
    using b1 b2 by linarith
  have pos: "0 \<le> sint (mldsa_caddq (mldsa_reduce32 a)) \<and> sint (mldsa_caddq (mldsa_reduce32 a)) < 8380417"
    using cad ante unfolding mldsa_is_caddq_def mldsa_q_def by simp
  have fdef: "sint (mldsa_freeze a) = sint (mldsa_caddq (mldsa_reduce32 a))"
    by (simp add: mldsa_freeze_def)
  show ?thesis
    unfolding mldsa_is_freeze_def mldsa_q_def fdef
    using c1 c2 pos by simp
qed

end
