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

end
