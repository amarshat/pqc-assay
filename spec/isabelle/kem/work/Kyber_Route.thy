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

text \<open>The model's \<open>a @ m = nth_seq a (pos_nat m)\<close> access rewrites \<open>pos_nat\<close> to \<open>to_nat\<close>
  on non-negative words (\<open>pos_nat_simps\<close>), so the index helpers below are stated over
  \<open>to_nat\<close>, the form the level unfold actually produces.\<close>

text \<open>Lower-leg partner index \<open>m + len\<close> (len = 0x80 = 128): \<open>to_nat (m + 128) = n + 128\<close>.\<close>
lemma to_nat_plus128:
  assumes "n < 128"
  shows "to_nat ((from_nat n :: [16]) + 0x80) = n + 128"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

text \<open>Upper-leg index \<open>m - len\<close>: \<open>to_nat (m - 128) = n - 128\<close> for \<open>128 <= n < 256\<close>.\<close>
lemma to_nat_minus128:
  assumes "128 \<le> n" and "n < 256"
  shows "to_nat ((from_nat n :: [16]) - 0x80) = n - 128"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

text \<open>Twiddle index for the lower leg: \<open>base + m div twolen = 1 + n div 256 = 1\<close> (n < 256).\<close>
lemma to_nat_zidx_lo0:
  assumes "n < 256"
  shows "to_nat ((0x1 :: [16]) + (from_nat n :: [16]) div 0x100) = 1"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_of_nat)
  done

text \<open>Twiddle index for the upper leg: \<open>base + (m - len) div twolen = 1 + (n-128) div 256 = 1\<close>.\<close>
lemma to_nat_zidx_hi0:
  assumes "128 \<le> n" and "n < 256"
  shows "to_nat ((0x1 :: [16]) + ((from_nat n :: [16]) - 0x80) div 0x100) = 1"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_sub_if' unat_of_nat word_le_nat_alt)
  done

text \<open>The half-test \<open>m mod twolen < len\<close> is \<open>n < 128\<close> for \<open>n < 256\<close>.\<close>
lemma half_test0:
  assumes "n < 256"
  shows "(((from_nat n :: [16]) mod 0x100 < 0x80)) = (n < 128)"
  using assms
  apply (simp add: from_nat_def from_int_word_def word_seq_convs cryptol_prim_defs)
  apply (simp add: word_less_nat_alt unat_mod unat_of_nat)
  done

section \<open>Level-0 coefficient access laws (len=128, twolen=256, base=1, twiddle zetas[1])\<close>

text \<open>Level 0 is the ML-KEM analogue of ML-DSA \<open>layer1\<close>: stride 128, single twiddle
  \<open>zetas[1]\<close>. The lower half is the additive leg, the upper half the subtractive leg.
  These are plain \<open>[16]\<close>-word equalities (the model does no per-op reduction); the value
  bridge to the sint recurrence is a later step.\<close>
lemma level0_lo:
  fixes a :: "[256][16]"
  assumes n: "n < 128"
  shows "nth_seq (nttLevel 0 a) n
       = (nth_seq a n) + fqmul (nth_seq zetas 1) (nth_seq a (n + 128))"
proof -
  have n256: "n < 256" using n by simp
  have n65: "n < 65536" using n by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def map_seq_nth nth_seq_conv seq_to_list n256)
    apply (simp add: half_test0[OF n256] n n256
                     to_nat_from_nat16[OF n65] to_nat_plus128[OF n] to_nat_zidx_lo0[OF n256])
    done
qed

lemma level0_hi:
  fixes a :: "[256][16]"
  assumes n1: "128 \<le> n" and n2: "n < 256"
  shows "nth_seq (nttLevel 0 a) n
       = (nth_seq a (n - 128)) - fqmul (nth_seq zetas 1) (nth_seq a n)"
proof -
  have n65: "n < 65536" using n2 by simp
  have nlt: "\<not> n < 128" using n1 by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test0[OF n2] nlt n2
                     to_nat_from_nat16[OF n65] to_nat_minus128[OF n1 n2] to_nat_zidx_hi0[OF n1 n2])
    done
qed

text \<open>Level-0 coefficient law: at every output position the model's \<open>nttLevel 0\<close> is the
  ML-KEM forward butterfly with twiddle \<open>zetas[1]\<close>. Lower half additive, upper half
  subtractive. Word-exact (no proof holes); the ML-KEM analogue of Bridge_Word.layer1_coeff.\<close>
lemma level0_coeff:
  fixes a :: "[256][16]"
  assumes n: "n < 256"
  shows "nth_seq (nttLevel 0 a) n
       = (if n < 128
          then (nth_seq a n) + fqmul (nth_seq zetas 1) (nth_seq a (n + 128))
          else (nth_seq a (n - 128)) - fqmul (nth_seq zetas 1) (nth_seq a n))"
proof (cases "n < 128")
  case True
  thus ?thesis using level0_lo[OF True] by simp
next
  case False
  hence "128 \<le> n" by simp
  thus ?thesis using level0_hi[OF _ n] False by simp
qed

end

end
