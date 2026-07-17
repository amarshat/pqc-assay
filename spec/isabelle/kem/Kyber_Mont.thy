(* Slice 3 (ML-KEM Tier-2), brick (a) arithmetic base: Montgomery-reduction
   correctness for the ML-KEM model, mirroring the ML-DSA `mont_core`
   (spec/isabelle/Assay_Equivalence.thy) at 16-bit width.

   ML-KEM constants: q = 3329, Montgomery factor R = 2^16 = 65536, and
   QINV = q^{-1} mod 2^16 in signed form = -3327 (the model stores
   `QINV = negate 0xcff`, 0xcff = 3327). The reference reduces
     t = (int16)(a * QINV);  r = (a - t*q) >> 16
   so that 2^16 * r == a (mod q) with -q < r < q on the documented input range.

   This file proves the INTEGER-LEVEL core (`mont_core_kem`), no bitvectors yet:
   given T == A*QINV (mod 2^16) and the int16 / mont_in_range bounds, the value
   r = (A - T*q) div 2^16 is congruent to A mod q and strictly bounded by q. The
   word/seq bridge onto the lifted `montgomery_reduce` is the next brick. *)
theory Kyber_Mont
  imports MLKEM_NTT
begin

text \<open>The Montgomery inverse identity at 16-bit width: \<open>QINV * q = 1 + (-169)*2^16\<close>,
  i.e. \<open>QINV*q \<equiv> 1 (mod 2^16)\<close> with \<open>QINV = -3327\<close>, \<open>q = 3329\<close>. Consequently
  \<open>1 + 3327*3329 = 169*2^16\<close>, the factor used to make the reduction division exact.\<close>
lemma kem_qinv_q: "(-3327::int) * 3329 = 1 + (-169) * 65536" by simp

lemma kem_qinv_factor: "(1::int) + 3327 * 3329 = 169 * 65536" by simp

text \<open>Integer core of ML-KEM Montgomery reduction. If \<open>T \<equiv> A*QINV (mod 2^16)\<close> and the
  int16 range on \<open>T\<close> and the \<open>mont_in_range\<close> bound on \<open>A\<close> hold, then
  \<open>r = (A - T*q) div 2^16\<close> satisfies \<open>2^16*r \<equiv> A (mod q)\<close> and \<open>-q < r < q\<close>.
  QINV is used in signed form (\<open>-3327\<close>). No solver on the big products: numerals are
  evaluated up front so only linarith sees plain integers (mirrors ML-DSA mont_core).\<close>
lemma mont_core_kem:
  fixes A T :: int
  assumes Tc:  "(T - A * (-3327)) mod 65536 = 0"
      and Tlo: "- 32768 \<le> T" and Thi: "T < 32768"
      and Alo: "- (32768 * 3329) \<le> A" and Ahi: "A < 32768 * 3329"
  shows "(65536 * ((A - T * 3329) div 65536)) mod 3329 = A mod 3329
       \<and> - 3329 < (A - T * 3329) div 65536
       \<and> (A - T * 3329) div 65536 < 3329"
proof -
  from Tc have "(65536::int) dvd (T - A * (-3327))" by (simp add: mod_eq_0_iff_dvd)
  then obtain k where k: "T - A * (-3327) = 65536 * k" by (auto elim: dvdE)
  hence T_eq: "T = A * (-3327) + 65536 * k" by simp
  define r where "r = 169 * A - 3329 * k"
  have D_eq: "A - T * 3329 = 65536 * r"
    unfolding r_def T_eq by (simp add: algebra_simps)
  hence r_is: "(A - T * 3329) div 65536 = r" by simp
  \<comment> \<open>congruence: 2^16*r = A - T*q \<equiv> A (mod q), since q dvd T*q\<close>
  have cong: "(65536 * r) mod 3329 = A mod 3329"
  proof -
    have "(65536 * r) mod 3329 = (A - T * 3329) mod 3329" using D_eq by simp
    also have "\<dots> = A mod 3329"
      using mod_mult_self1[of A "- T" 3329] by (simp add: algebra_simps)
    finally show ?thesis .
  qed
  \<comment> \<open>bounds: multiply the range hyps by q, then divide the 2^16*r relation. Big numeral
      products evaluated up front so linarith only sees plain integers.\<close>
  have e1: "(32768::int) * 3329 = 109084672" by simp
  have e2: "(65536::int) * 3329 = 218169344" by simp
  have Tq_lo: "T * 3329 \<ge> - 109084672" using Tlo by (simp add: mult_right_mono)
  have Tq_hi: "T * 3329 \<le> 109081343" using Thi by (simp add: mult_right_mono)
  have Ahi': "A < 109084672" using Ahi e1 by simp
  have Alo': "- 109084672 \<le> A" using Alo e1 by simp
  have ub: "65536 * r < 218169344" using D_eq Ahi' Tq_lo by linarith
  have lb: "- 218169344 < 65536 * r" using D_eq Alo' Tq_hi by linarith
  from ub have rub: "r < 3329" by simp
  from lb have rlb: "- 3329 < r" by simp
  from cong rub rlb r_is show ?thesis by simp
qed

section \<open>Word-level bridge lemmas (pure Word_Lib, no model defs yet)\<close>

text \<open>Down-cast 32->16 preserves the signed value when it fits in int16. ML-KEM analogue
  of the ML-DSA \<open>sint_ucast_fit\<close> (64->32).\<close>
lemma sint_ucast_fit_16:
  fixes V :: "32 word"
  assumes "- 32768 \<le> sint V" and "sint V < 32768"
  shows "sint (ucast V :: 16 word) = sint V"
proof -
  have "sint (ucast V :: 16 word) = sint (scast V :: 16 word)"
    by (simp add: scast_ucast_down_same)
  also have "\<dots> = signed_take_bit 15 (sint V)"
    by (simp add: signed_scast_eq)
  also have "\<dots> = sint V" using assms by (simp add: signed_take_bit_int_eq_self)
  finally show ?thesis .
qed

text \<open>The reduction body computes \<open>(A - t*q) div 2^16\<close> exactly as a signed value. Here
  \<open>A = sint aw\<close> (int32 input) and \<open>t = sint t16\<close> (int16). The subtraction and the final
  down-cast do not overflow on the documented input range. ML-KEM analogue of \<open>red_value\<close>.\<close>
lemma red_value_kem:
  fixes aw :: "32 word" and t16 :: "16 word"
  assumes Alo: "- (32768 * 3329) \<le> sint aw" and Ahi: "sint aw < 32768 * 3329"
  shows "sint (ucast (sshiftr (aw - scast t16 * 3329) 16) :: 16 word)
       = (sint aw - sint t16 * 3329) div 65536"
proof -
  have t_lo: "(- 32768::int) \<le> sint t16" using sint_greater_eq[of t16] by simp
  have t_hi: "sint t16 \<le> 32767" using sint_lt[of t16] by simp
  have tq_lo: "- 109084672 \<le> sint t16 * 3329"
    using mult_right_mono[OF t_lo, of 3329] by simp
  have tq_hi: "sint t16 * 3329 \<le> 109081343"
    using mult_right_mono[OF t_hi, of 3329] by simp
  have Alo': "- 109084672 \<le> sint aw" using Alo by simp
  have Ahi': "sint aw < 109084672" using Ahi by simp
  have hom: "aw - scast t16 * 3329 = (of_int (sint aw - sint t16 * 3329) :: 32 word)"
    by (simp add: of_int_sint_scast)
  have fitX: "- 2147483648 \<le> sint aw - sint t16 * 3329
            \<and> sint aw - sint t16 * 3329 < 2147483648"
    using Alo' Ahi' tq_lo tq_hi by linarith
  have sintX: "sint (aw - scast t16 * 3329) = sint aw - sint t16 * 3329"
    unfolding hom by (rule sint_of_int_eq; (use fitX in simp))
  have sh: "sint (sshiftr (aw - scast t16 * 3329) 16) = (sint aw - sint t16 * 3329) div 65536"
    using sintX by (simp add: sshiftr_div_2n)
  have ub: "sint aw - sint t16 * 3329 < 218169344" using Ahi' tq_lo by linarith
  have lb: "- 218169344 \<le> sint aw - sint t16 * 3329" using Alo' tq_hi by linarith
  have v_hi: "(sint aw - sint t16 * 3329) div 65536 < 32768"
  proof -
    have "(sint aw - sint t16 * 3329) div 65536 \<le> 218169343 div 65536"
      using ub by (auto intro: zdiv_mono1)
    thus ?thesis by simp
  qed
  have v_lo: "- 32768 \<le> (sint aw - sint t16 * 3329) div 65536"
  proof -
    have "(- 218169344) div (65536::int) \<le> (sint aw - sint t16 * 3329) div 65536"
      using lb by (auto intro: zdiv_mono1)
    thus ?thesis by simp
  qed
  have Vfit: "- 32768 \<le> sint (sshiftr (aw - scast t16 * 3329) 16)
            \<and> sint (sshiftr (aw - scast t16 * 3329) 16) < 32768"
    using v_lo v_hi unfolding sh by simp
  show ?thesis
    using sint_ucast_fit_16[OF conjunct1[OF Vfit] conjunct2[OF Vfit]] sh by simp
qed

text \<open>The low-16 product \<open>t = (low16 a) * QINV\<close> satisfies \<open>t \<equiv> a*QINV (mod 2^16)\<close>, with
  \<open>QINV = 62209 = -3327 (mod 2^16)\<close>. ML-KEM analogue of \<open>tcong\<close>; the int16 multiply only
  depends on the low 16 bits of \<open>a\<close>, so multiplying \<open>low16 a\<close> or (signed) \<open>a\<close> agrees mod 2^16.\<close>
lemma sint_uint_mod16: "sint (y :: 16 word) mod 65536 = uint y mod 65536"
proof -
  have key: "(uint y - 65536) mod 65536 = uint y mod 65536"
    using mod_mult_self1[of "uint y" "- 1" 65536] by simp
  show ?thesis using key by (simp add: word_sint_msb_eq size_word.rep_eq)
qed

lemma sint_uint_mod32_16: "sint (aw :: 32 word) mod 65536 = uint aw mod 65536"
proof -
  have key: "(uint aw - 4294967296) mod 65536 = uint aw mod 65536"
    using mod_mult_self1[of "uint aw" "- 65536" 65536] by simp
  show ?thesis using key by (simp add: word_sint_msb_eq size_word.rep_eq)
qed

lemma tcong_kem:
  fixes aw :: "32 word"
  shows "(sint ((ucast aw :: 16 word) * 62209) - sint aw * (-3327)) mod 65536 = 0"
proof -
  have lhs: "sint ((ucast aw :: 16 word) * 62209) mod 65536 = (uint aw * 62209) mod 65536"
  proof -
    have "sint ((ucast aw :: 16 word) * 62209) mod 65536
        = uint ((ucast aw :: 16 word) * 62209) mod 65536" by (rule sint_uint_mod16)
    also have "\<dots> = (uint (ucast aw :: 16 word) * 62209) mod 65536"
      by (simp add: uint_word_ariths(3) take_bit_eq_mod mod_mod_cancel)
    also have "\<dots> = (uint aw mod 65536 * 62209) mod 65536"
      by (simp add: unsigned_ucast_eq take_bit_eq_mod)
    also have "\<dots> = (uint aw * 62209) mod 65536"
      by (simp add: mod_mult_left_eq)
    finally show ?thesis .
  qed
  have rhs: "(sint aw * (-3327)) mod 65536 = (uint aw * 62209) mod 65536"
  proof -
    have "(sint aw * (-3327)) mod 65536 = (uint aw * (-3327)) mod 65536"
      by (rule mod_mult_cong[OF sint_uint_mod32_16 refl])
    also have "\<dots> = (uint aw * 62209) mod 65536"
    proof -
      have "(- 3327::int) mod 65536 = 62209" by simp
      thus ?thesis by (metis mod_mult_right_eq)
    qed
    finally show ?thesis .
  qed
  have "sint ((ucast aw :: 16 word) * 62209) mod 65536 = (sint aw * (-3327)) mod 65536"
    using lhs rhs by simp
  thus ?thesis by (simp add: mod_eq_dvd_iff)
qed

end
