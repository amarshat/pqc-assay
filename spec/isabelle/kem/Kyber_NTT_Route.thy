(* Slice 3 (ML-KEM Tier-2), brick (b) foundation: turn the Montgomery-reduction
   correctness (brick a, Kyber_Mont.montgomery_reduce_correct_kem) into the butterfly
   facts the 7-layer Cooley-Tukey routing proof needs.

   The ML-KEM butterfly multiply is fqmul z x = montgomery_reduce (sext32 z * sext32 x).
   Here we prove, all at 16/32-bit width (mirroring the ML-DSA Assay_Equivalence butterfly
   lemmas at 64/32-bit):
     - sint_sext32_mult    : sint_seq (sext32 z * sext32 x) = sint_seq z * sint_seq x
                             (the int32 product does not overflow: |int16 * int16| <= 2^30 < 2^31).
     - mont_butterfly_bound_kem / fqmul_cong_kem : on the documented product range, fqmul is a
                             Montgomery product, -q < fqmul z x < q and 2^16 * fqmul z x == z*x (mod q).
     - zeta_bound_kem      : every twiddle |zetas[n]| <= 1665 (< q/2), by evaluation over the table.
     - mont_input_ok_of_bounds_kem : |zeta|<=1665, |coeff|<=B, B<=32767 gives the montgomery precondition
                             -2^15*q <= zeta*coeff < 2^15*q. *)
theory Kyber_NTT_Route
  imports Kyber_Mont "Cryptol.SeqOOB"
begin

section \<open>Generic: a total bound from a list_all over the elements (incl. OOB accesses)\<close>

text \<open>Any indexed access is a list member (in-bounds element, or the last element on OOB).
  Ported verbatim from ML-DSA Assay_Equivalence.\<close>
lemma nth_list_in_set: "xs \<noteq> [] \<Longrightarrow> nth_list xs n \<in> set xs"
  by (cases "n < length xs")
     (auto simp: nth_list_def oob_list_elem_end_def last_in_set intro: nth_mem)

lemma nth_seq_in_set:
  fixes a :: "('n::len, 'a) seq"
  assumes "0 < LEN('n)"
  shows "nth_seq a n \<in> set (seq_to_list a)"
proof -
  have ne: "seq_to_list a \<noteq> []" using assms by simp
  have "nth_seq a n = nth_list (seq_to_list a) n" by (simp add: seq_to_list)
  thus ?thesis using nth_list_in_set[OF ne] by simp
qed

lemma nth_seq_bounded:
  fixes a :: "('n::len, 'a) seq"
  assumes "0 < LEN('n)" and "list_all P (seq_to_list a)"
  shows "P (nth_seq a n)"
  using nth_seq_in_set[OF assms(1), of a n] assms(2) by (simp add: list_all_iff)

context includes cryptol_syntax begin

section \<open>The signed int32 product of two sign-extended int16 values does not overflow\<close>

lemma sint_sext32_mult:
  fixes z x :: "[16]"
  shows "sint_seq (sext32 z * sext32 x) = sint_seq z * sint_seq x"
proof -
  define zw :: "16 word" where "zw = seq_to_word z"
  define xw :: "16 word" where "xw = seq_to_word x"
  have zb: "- 32768 \<le> sint zw" "sint zw < 32768"
    using sint_greater_eq[of zw] sint_lt[of zw] by simp_all
  have xb: "- 32768 \<le> sint xw" "sint xw < 32768"
    using sint_greater_eq[of xw] sint_lt[of xw] by simp_all
  have prodb: "- 2147483648 \<le> sint zw * sint xw \<and> sint zw * sint xw < 2147483648"
  proof -
    have az: "\<bar>sint zw\<bar> \<le> 32768" using zb by linarith
    have ax: "\<bar>sint xw\<bar> \<le> 32768" using xb by linarith
    have "\<bar>sint zw * sint xw\<bar> \<le> 32768 * 32768"
      unfolding abs_mult using az ax by (intro mult_mono) auto
    then have "- 1073741824 \<le> sint zw * sint xw \<and> sint zw * sint xw \<le> 1073741824"
      by (simp add: abs_le_iff)
    thus ?thesis by linarith
  qed
  have w: "seq_to_word (sext32 z * sext32 x) = (scast zw * scast xw :: 32 word)"
    unfolding zw_def xw_def by (simp add: word_seq_convs seq_to_word probe_sext32)
  have hom: "(scast zw * scast xw :: 32 word) = word_of_int (sint zw * sint xw)"
    by (metis of_int_mult scast_eq)
  have "sint_seq (sext32 z * sext32 x) = sint (scast zw * scast xw :: 32 word)"
    using w by (simp add: probe_sint_seq_kem)
  also have "\<dots> = sint zw * sint xw"
    unfolding hom by (rule sint_of_int_eq) (use prodb in simp)+
  finally show ?thesis
    unfolding zw_def xw_def by (simp add: probe_sint_seq_kem)
qed

section \<open>fqmul is a correct Montgomery product on the documented range\<close>

text \<open>The butterfly's montgomery term is strictly bounded by q, given its product input is within
  the (half-open) montgomery domain. Reuses montgomery_reduce_correct_kem.\<close>
lemma mont_butterfly_bound_kem:
  fixes z x :: "[16]"
  assumes "- (32768 * 3329) \<le> sint_seq z * sint_seq x"
      and "sint_seq z * sint_seq x < 32768 * 3329"
  shows "- 3329 < sint_seq (fqmul z x) \<and> sint_seq (fqmul z x) < 3329"
proof -
  have ok1: "- (32768 * 3329) \<le> sint_seq (sext32 z * sext32 x)"
    using assms(1) by (simp add: sint_sext32_mult)
  have ok2: "sint_seq (sext32 z * sext32 x) < 32768 * 3329"
    using assms(2) by (simp add: sint_sext32_mult)
  show ?thesis
    unfolding fqmul_def
    using montgomery_reduce_correct_kem[OF ok1 ok2] by simp
qed

text \<open>And the congruence the routing needs: 2^16 * fqmul z x == z*x (mod q).\<close>
lemma fqmul_cong_kem:
  fixes z x :: "[16]"
  assumes "- (32768 * 3329) \<le> sint_seq z * sint_seq x"
      and "sint_seq z * sint_seq x < 32768 * 3329"
  shows "(65536 * sint_seq (fqmul z x)) mod 3329 = (sint_seq z * sint_seq x) mod 3329"
proof -
  have ok1: "- (32768 * 3329) \<le> sint_seq (sext32 z * sext32 x)"
    using assms(1) by (simp add: sint_sext32_mult)
  have ok2: "sint_seq (sext32 z * sext32 x) < 32768 * 3329"
    using assms(2) by (simp add: sint_sext32_mult)
  have "(65536 * sint_seq (fqmul z x)) mod 3329 = sint_seq (sext32 z * sext32 x) mod 3329"
    unfolding fqmul_def using montgomery_reduce_correct_kem[OF ok1 ok2] by simp
  thus ?thesis by (simp add: sint_sext32_mult)
qed

section \<open>Twiddle-table bound and the montgomery precondition\<close>

text \<open>Every montgomery-domain twiddle satisfies |zetas[n]| <= 1665 (< q/2 = 1664.5), incl. OOB
  accesses. Discharged by evaluation over the concrete 128-entry table.\<close>
lemma zeta_bound_kem:
  "- 1665 \<le> sint_seq (nth_seq zetas n) \<and> sint_seq (nth_seq zetas n) \<le> 1665"
proof (rule nth_seq_bounded)
  show "(0::nat) < LEN(128)" by simp
  show "list_all (\<lambda>x. - 1665 \<le> sint_seq x \<and> sint_seq x \<le> 1665) (seq_to_list zetas)"
    unfolding zetas_def by eval
qed

text \<open>The montgomery precondition follows from the coefficient/zeta bounds: |zeta|<=1665, |coeff|<=B,
  B<=32767, so |zeta*coeff| <= 1665*32767 < 2^15*q = 109084672.\<close>
lemma mont_input_ok_of_bounds_kem:
  fixes z x :: int
  assumes zlo: "- 1665 \<le> z" and zhi: "z \<le> 1665"
      and xlo: "- B \<le> x" and xhi: "x \<le> B" and Bhi: "B \<le> 32767"
  shows "- (32768 * 3329) \<le> z * x \<and> z * x < 32768 * 3329"
proof -
  have az: "\<bar>z\<bar> \<le> 1665" using zlo zhi by (simp add: abs_le_iff)
  have ax: "\<bar>x\<bar> \<le> B" using xlo xhi by (simp add: abs_le_iff)
  have "\<bar>z * x\<bar> \<le> 1665 * B" unfolding abs_mult using az ax by (intro mult_mono) auto
  also have "\<dots> \<le> 1665 * 32767" using Bhi by simp
  finally have "\<bar>z * x\<bar> \<le> 54557055" by simp
  thus ?thesis by (simp add: abs_le_iff)
qed

end

end
