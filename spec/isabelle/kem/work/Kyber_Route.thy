theory Kyber_Route
  imports "Kem_Base.Kyber_NTT_Route"
begin

context includes cryptol_syntax begin

section \<open>The model foldl over the 7 level indices unfolds to the explicit 7-level composition\<close>

lemma ntt_unfold:
  "ntt a0 =
     nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3
     (nttLevel 2 (nttLevel 1 (nttLevel 0 a0))))))"
  unfolding ntt_def Let_def
  by (simp add: foldl_seq.rep_eq)

section \<open>Signed 16-bit add/sub compute integer add/sub when the result fits in int16\<close>

text \<open>The model's butterfly combines coefficients with plain int16 \<open>+\<close>/\<open>-\<close> (no per-op
  reduction). As long as the true integer result stays in \<open>[-2^15, 2^15)\<close>, the word
  operation does not wrap, so the signed reading is the integer add/sub. Same
  word/seq route as \<open>sint_sext32_mult\<close>.\<close>
lemma sint_add16:
  fixes a b :: "[16]"
  assumes "- 32768 \<le> sint_seq a + sint_seq b" and "sint_seq a + sint_seq b < 32768"
  shows "sint_seq (a + b) = sint_seq a + sint_seq b"
proof -
  define aw :: "16 word" where "aw = seq_to_word a"
  define bw :: "16 word" where "bw = seq_to_word b"
  have w: "seq_to_word (a + b) = (aw + bw :: 16 word)"
    unfolding aw_def bw_def by (simp add: word_seq_convs seq_to_word)
  have hom: "(aw + bw :: 16 word) = word_of_int (sint aw + sint bw)"
    by (metis of_int_add scast_eq scast_id)
  have "sint_seq (a + b) = sint (aw + bw :: 16 word)"
    using w by (simp add: probe_sint_seq_kem)
  also have "\<dots> = sint aw + sint bw"
    unfolding hom by (rule sint_of_int_eq)
       (use assms in \<open>simp_all add: aw_def bw_def probe_sint_seq_kem\<close>)
  finally show ?thesis
    unfolding aw_def bw_def by (simp add: probe_sint_seq_kem)
qed

lemma sint_sub16:
  fixes a b :: "[16]"
  assumes "- 32768 \<le> sint_seq a - sint_seq b" and "sint_seq a - sint_seq b < 32768"
  shows "sint_seq (a - b) = sint_seq a - sint_seq b"
proof -
  define aw :: "16 word" where "aw = seq_to_word a"
  define bw :: "16 word" where "bw = seq_to_word b"
  have w: "seq_to_word (a - b) = (aw - bw :: 16 word)"
    unfolding aw_def bw_def by (simp add: word_seq_convs seq_to_word)
  have hom: "(aw - bw :: 16 word) = word_of_int (sint aw - sint bw)"
    by (metis of_int_diff scast_eq scast_id)
  have "sint_seq (a - b) = sint (aw - bw :: 16 word)"
    using w by (simp add: probe_sint_seq_kem)
  also have "\<dots> = sint aw - sint bw"
    unfolding hom by (rule sint_of_int_eq)
       (use assms in \<open>simp_all add: aw_def bw_def probe_sint_seq_kem\<close>)
  finally show ?thesis
    unfolding aw_def bw_def by (simp add: probe_sint_seq_kem)
qed

section \<open>Packaged butterfly law: twiddle-times-coefficient on the documented range\<close>

text \<open>Combining the foundation lemmas (twiddle-table bound, montgomery precondition,
  montgomery product bound and congruence): for any table index \<open>k\<close> and coefficient
  \<open>x\<close> with \<open>|x| <= B <= 32767\<close>, the montgomery butterfly term \<open>fqmul zetas[k] x\<close> is a
  correct normal-domain product: strictly bounded by \<open>q\<close>, and \<open>2^16\<close> times it is the
  twiddle times the coefficient mod \<open>q\<close>. This is the per-op seam the 7-level routing
  consumes, the ML-KEM analogue of Bridge_Word.red_mul.\<close>
lemma butterfly_law_kem:
  fixes x :: "[16]" and B :: int
  assumes xlo: "- B \<le> sint_seq x" and xhi: "sint_seq x \<le> B" and Bhi: "B \<le> 32767"
  shows "- 3329 < sint_seq (fqmul (nth_seq zetas k) x)
       \<and> sint_seq (fqmul (nth_seq zetas k) x) < 3329
       \<and> (65536 * sint_seq (fqmul (nth_seq zetas k) x)) mod 3329
           = (sint_seq (nth_seq zetas k) * sint_seq x) mod 3329"
proof -
  have zlo: "- 1665 \<le> sint_seq (nth_seq zetas k)"
   and zhi: "sint_seq (nth_seq zetas k) \<le> 1665" using zeta_bound_kem by auto
  have rng: "- (32768 * 3329) \<le> sint_seq (nth_seq zetas k) * sint_seq x
           \<and> sint_seq (nth_seq zetas k) * sint_seq x < 32768 * 3329"
    using mont_input_ok_of_bounds_kem[OF zlo zhi xlo xhi Bhi] .
  show ?thesis
    using mont_butterfly_bound_kem[OF conjunct1[OF rng] conjunct2[OF rng]]
          fqmul_cong_kem[OF conjunct1[OF rng] conjunct2[OF rng]]
    by simp
qed

section \<open>Index arithmetic for the per-level unfold (level 0: len=128, twolen=256)\<close>

text \<open>The model indexes coefficient and twiddle sequences with \<open>[16]\<close> words: \<open>a @ m\<close> is
  \<open>nth_seq a (pos_nat m)\<close>, and the level butterfly builds \<open>m\<close> from \<open>fromTo 0 255\<close>. These
  helpers reduce the \<open>[16]\<close>-word index computations to plain \<open>nat\<close> facts for \<open>n < 256\<close>,
  the ML-KEM analogue of the ML-DSA \<open>idx_*\<close> lemmas (there at 64/8-bit width).\<close>

text \<open>Recovering the \<open>nat\<close> index from the \<open>[16]\<close> word, in bounds. Same route as the
  ML-DSA \<open>idx_val\<close>, minus the zext (here the index word is already \<open>[16]\<close>).\<close>
lemma to_nat_from_nat16:
  assumes "n < 65536"
  shows "to_nat (from_nat n :: [16]) = n"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_of_nat)
  done

lemma pos_nat_from_nat16:
  assumes "n < 65536"
  shows "pos_nat (from_nat n :: [16]) = n"
proof -
  have "to_int (from_nat n :: [16]) \<ge> 0"
    by (simp add: to_int_word_def word_seq_convs cryptol_prim_defs)
  thus ?thesis using to_nat_from_nat16[OF assms] by (simp add: pos_nat_def)
qed

end

end
