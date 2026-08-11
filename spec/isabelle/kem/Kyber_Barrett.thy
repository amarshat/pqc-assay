(* Slice 4 (ML-KEM inverse NTT), arithmetic base: Barrett-reduction correctness for the
   ML-KEM model, needed because invntt's low leg re-reduces through barrett_reduce every
   level (unlike montgomery_reduce, which the forward proof already covers in Kyber_Mont).

   ML-KEM's barrett_reduce is a round-to-nearest Barrett reduction, structurally different
   from the conditional-subtract Barrett already proven for RustCrypto's wider domain
   (spec/isabelle/tier2/barrett/Barrett_Core.thy, escape2_core-style with M*q slightly below
   2^S) -- that lemma is NOT reused here. The C/model: with V = 20159, q = 3329,

     t1 = (V*a + 2^25) >>$ 26      -- arithmetic shift = floor division by 2^26
     t2 = drop16(t1) * q            -- int16 narrowing, but see the bound lemma below: t1 is
                                     -- always tiny (|t1| <= 10), so this narrowing is the
                                     -- identity, never an actual wraparound
     r  = a - t2

   for EVERY int16 a (no precondition, matching the SAW proof's unconditional spec), giving
   the centered representative: r == a (mod q), -1664 <= r <= 1664.

   Bound strategy: rather than a hand interval-bound derivation (as `reduce32_correct` in
   Assay_Equivalence.thy needed for a much wider, symbolic domain), int16 is a small enough
   finite domain (65536 values) that the bound is checked by `eval` (Isabelle's code
   generator enumerating the range), the same "finite domain, check it" move already used
   elsewhere in this codebase for the zeta-table bound. *)
theory Kyber_Barrett
  imports MLKEM_NTT Kyber_Mont
begin

text \<open>The real content: for every int16 \<open>a\<close>, \<open>r = a - t1*q\<close> (with \<open>t1\<close> the Barrett quotient)
  is bounded to the centered range \<open>[-1664, 1664]\<close>. Checked by enumeration over the finite
  65536-value domain rather than an algebraic interval derivation -- the congruence half is
  true by construction for ANY \<open>t1\<close> (see \<open>barrett_core_kem\<close> below), so this lemma carries
  all the actual work.\<close>
lemma barrett_r_bound_kem:
  "\<forall>a \<in> {-32768..32767::int}.
     let t1 = (20159 * a + 33554432) div 67108864; r = a - t1 * 3329
     in - 1664 \<le> r \<and> r \<le> 1664"
  by eval

text \<open>Integer core of ML-KEM Barrett reduction: for every int16 \<open>A\<close>, \<open>r = A - t1*q\<close> is the
  centered representative of \<open>A\<close> mod \<open>q\<close>: \<open>r \<equiv> A (mod q)\<close> (true by construction, any \<open>t1\<close>)
  and \<open>-1664 \<le> r \<le> 1664\<close> (from \<open>barrett_r_bound_kem\<close>).\<close>
lemma barrett_core_kem:
  fixes A :: int
  assumes Alo: "- 32768 \<le> A" and Ahi: "A \<le> 32767"
  shows "let t1 = (20159 * A + 33554432) div 67108864; r = A - t1 * 3329
         in (r - A) mod 3329 = 0 \<and> - 1664 \<le> r \<and> r \<le> 1664"
proof -
  have Amem: "A \<in> {-32768..32767::int}" using Alo Ahi by simp
  have rb: "let t1 = (20159 * A + 33554432) div 67108864; r = A - t1 * 3329
            in - 1664 \<le> r \<and> r \<le> 1664"
    using barrett_r_bound_kem Amem by blast
  have cong: "let t1 = (20159 * A + 33554432) div 67108864; r = A - t1 * 3329
              in (r - A) mod 3329 = 0"
    by (simp add: Let_def mod_eq_0_iff_dvd algebra_simps)
  show ?thesis using rb cong unfolding Let_def by simp
qed

text \<open>The quotient itself is tiny (\<open>|t1| \<le> 10\<close>), so the C's 32-to-16 truncation
  (\<open>drop\<close>) never actually wraps -- it is the identity on \<open>t1\<close>'s value. Also by
  enumeration, same domain as \<open>barrett_r_bound_kem\<close>.\<close>
lemma barrett_t1_bound_kem:
  "\<forall>a \<in> {-32768..32767::int}. let t1 = (20159 * a + 33554432) div 67108864
                                in - 10 \<le> t1 \<and> t1 \<le> 10"
  by eval

section \<open>Word-level bridge onto the C's exact bit operations\<close>

text \<open>The shift-and-add in word form: \<open>sint\<close> of the 32-bit \<open>V*a + 2^25\<close> equals the integer
  value, no overflow (magnitude well under \<open>2^31\<close> for any int16 \<open>a\<close>). ML-KEM analogue of the
  additive step inside \<open>red_value_kem\<close>.\<close>
lemma barrett_sum_word:
  fixes aw :: "16 word"
  shows "sint ((0x4EBF * scast aw + 0x2000000 :: 32 word)) = 20159 * sint aw + 33554432"
proof -
  have alo: "(- 32768::int) \<le> sint aw" using sint_greater_eq[of aw] by simp
  have ahi: "sint aw \<le> 32767" using sint_lt[of aw] by simp
  have hom: "(0x4EBF * scast aw + 0x2000000 :: 32 word)
           = (of_int (20159 * sint aw + 33554432) :: 32 word)"
    by (simp add: of_int_sint_scast)
  have fit: "- 2147483648 \<le> 20159 * sint aw + 33554432 \<and> 20159 * sint aw + 33554432 < 2147483648"
    using alo ahi by linarith
  show ?thesis unfolding hom by (rule sint_of_int_eq; (use fit in simp))
qed

text \<open>The lifted quotient \<open>ucast (sshiftr (V*aw + 2^25) 26) :: 16 word\<close> equals the integer
  Barrett quotient, and (by \<open>barrett_t1_bound_kem\<close>) that quotient is small enough for the
  32-to-16 \<open>ucast\<close> to preserve its value exactly (\<open>sint_ucast_fit_16\<close>, from Kyber_Mont).
  ML-KEM analogue of \<open>red_value_kem\<close>.\<close>
lemma red_value_barrett_kem:
  fixes aw :: "16 word"
  shows "sint (ucast (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26) :: 16 word)
       = (20159 * sint aw + 33554432) div 67108864"
proof -
  have sumv: "sint (0x4EBF * scast aw + 0x2000000 :: 32 word) = 20159 * sint aw + 33554432"
    by (rule barrett_sum_word)
  have sh: "sint (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26)
          = (20159 * sint aw + 33554432) div 67108864"
    unfolding sumv[symmetric] by (simp add: sshiftr_div_2n)
  have alo: "(- 32768::int) \<le> sint aw" using sint_greater_eq[of aw] by simp
  have ahi: "sint aw \<le> 32767" using sint_lt[of aw] by simp
  have amem: "sint aw \<in> {-32768..32767::int}" using alo ahi by simp
  have tb: "let t1 = (20159 * sint aw + 33554432) div 67108864
            in - 10 \<le> t1 \<and> t1 \<le> 10"
    using barrett_t1_bound_kem amem by blast
  have tbnd: "- 10 \<le> (20159 * sint aw + 33554432) div 67108864
            \<and> (20159 * sint aw + 33554432) div 67108864 \<le> 10"
    using tb unfolding Let_def by simp
  have Vfit: "- 32768 \<le> sint (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26)
            \<and> sint (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26) < 32768"
    using tbnd unfolding sh by simp
  show ?thesis
    using sint_ucast_fit_16[OF conjunct1[OF Vfit] conjunct2[OF Vfit]] sh by simp
qed

section \<open>Seq-level bridge onto the lifted model, and the assembled correctness theorem\<close>

context includes cryptol_syntax begin

text \<open>Lower the lifted \<open>barrett_reduce\<close> (seq form) to the clean word computation. Mirrors
  \<open>bval_kem\<close>: unfold the model definition and rewrite seq arithmetic to word arithmetic via
  the standard conversion set.\<close>
lemma bval_barrett_kem:
  "sint_seq (barrett_reduce a)
     = sint (seq_to_word a
             - ucast (sshiftr (0x4EBF * scast (seq_to_word a) + 0x2000000 :: 32 word) 26 :: 32 word)
               * 3329 :: 16 word)"
  unfolding barrett_reduce_def
  by (simp add: word_seq_convs V16_def Q16_def probe_sext32 seq_to_word
                ucast_up_ucast take_bit_length_eq' is_up unsigned_take_bit_eq)

text \<open>Assembled: the lifted ML-KEM \<open>barrett_reduce\<close> is a correct Barrett reduction for EVERY
  int16 input (no precondition, matching the SAW proof): \<open>r \<equiv> a (mod q)\<close> and the centered
  bound \<open>-1664 \<le> r \<le> 1664\<close>, where \<open>r = sint_seq\<close> of the result and \<open>a = sint_seq\<close> of the
  input. Stated over \<open>sint_seq\<close>, as \<open>montgomery_reduce_correct_kem\<close>. Chains
  bval_barrett_kem -> red_value_barrett_kem -> barrett_core_kem.\<close>
theorem barrett_reduce_correct_kem:
  fixes a :: "(16, bool) seq"
  shows "(sint_seq (barrett_reduce a) - sint_seq a) mod 3329 = 0
       \<and> - 1664 \<le> sint_seq (barrett_reduce a)
       \<and> sint_seq (barrett_reduce a) \<le> 1664"
proof -
  define aw :: "16 word" where "aw = seq_to_word a"
  have A_eq: "sint_seq a = sint aw" unfolding aw_def by (rule probe_sint_seq_kem)
  have bval: "sint_seq (barrett_reduce a)
            = sint (aw - ucast (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26 :: 32 word)
                          * 3329 :: 16 word)"
    unfolding aw_def by (rule bval_barrett_kem)
  have t1w: "sint (ucast (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26) :: 16 word)
           = (20159 * sint aw + 33554432) div 67108864"
    by (rule red_value_barrett_kem)
  have alo: "(- 32768::int) \<le> sint aw" using sint_greater_eq[of aw] by simp
  have ahi: "sint aw \<le> 32767" using sint_lt[of aw] by simp
  \<comment> \<open>the subtraction \<open>aw - t1w*3329\<close> is a plain 16-bit wraparound; but the RESULT is bounded
      to \<open>[-1664,1664]\<close> by \<open>barrett_core_kem\<close>, which fits int16 with room to spare, so the
      wraparound is never exercised and \<open>sint\<close> of the word subtraction equals the integer
      subtraction. Established the same way \<open>red_value_kem\<close> handles the 32-bit case: rewrite
      the word op to \<open>of_int\<close> of the integer value, then show it fits before invoking
      \<open>sint_of_int_eq\<close>.\<close>
  define t1 :: int where "t1 = (20159 * sint aw + 33554432) div 67108864"
  have t1w' : "sint (ucast (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26) :: 16 word) = t1"
    unfolding t1_def using t1w .
  have core: "(aw_val - t1 * 3329 - aw_val) mod 3329 = 0
            \<and> - 1664 \<le> aw_val - t1 * 3329 \<and> aw_val - t1 * 3329 \<le> 1664"
    if aw_val_def: "aw_val = sint aw" for aw_val
    using barrett_core_kem[OF alo ahi] unfolding t1_def aw_val_def Let_def by simp
  have hom: "(aw - ucast (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26 :: 32 word) * 3329 :: 16 word)
           = (of_int (sint aw - t1 * 3329) :: 16 word)"
    unfolding t1w'[symmetric] by (simp add: of_int_sint_scast)
  have rb: "- 1664 \<le> sint aw - t1 * 3329 \<and> sint aw - t1 * 3329 \<le> 1664"
    using core[OF refl] by simp
  have fit: "- 32768 \<le> sint aw - t1 * 3329 \<and> sint aw - t1 * 3329 < 32768" using rb by linarith
  have sintR: "sint (aw - ucast (sshiftr (0x4EBF * scast aw + 0x2000000 :: 32 word) 26 :: 32 word) * 3329 :: 16 word)
             = sint aw - t1 * 3329"
    unfolding hom by (rule sint_of_int_eq; (use fit in simp))
  show ?thesis
    unfolding bval sintR A_eq
    using core[OF refl] by simp
qed

end

end
