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

section \<open>Level-1 coefficient law (len=64, twolen=128, base=2, twiddle zetas[2 + n div 128])\<close>

text \<open>Levels \<open>i >= 1\<close> carry non-trivial shifts in their length/base constants:
  \<open>len = 0x80 >> i\<close>, \<open>twolen = 0x100 >> i\<close>, \<open>base = 0x1 << i\<close>. The level-0 narrow
  unfold does not evaluate these (level 0 was shift-by-0 = identity). These three
  reductions collapse each constant to its literal \<open>[16]\<close> value by \<open>eval\<close>, so they can
  be fed to the SAME narrow first simp used at level 0 (no broad \<open>cryptol_prim_defs\<close>
  unfold, which would otherwise break the \<open>to_nat\<close> helper matching).\<close>
lemma amt1:      "bl_to_bin (seq_to_list (1::[16])) = 1" by eval
lemma len1_op:   "right_shift (0x80  :: [16]) 1 = (0x40 :: [16])" by eval
lemma twolen1_op: "right_shift (0x100 :: [16]) 1 = (0x80 :: [16])" by eval
lemma base1_op:  "left_shift  (0x1   :: [16]) 1 = (0x2  :: [16])" by eval

text \<open>Level 1 has stride 64 and two twiddle blocks: the twiddle index is \<open>base + m div twolen
  = 2 + n div 128\<close>, so positions in \<open>[0,128)\<close> use \<open>zetas[2]\<close> and \<open>[128,256)\<close> use \<open>zetas[3]\<close>.\<close>

lemma to_nat_plus64:
  assumes "n < 65472"
  shows "to_nat ((from_nat n :: [16]) + 0x40) = n + 64"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

lemma to_nat_minus64:
  assumes "64 \<le> n" and "n < 65536"
  shows "to_nat ((from_nat n :: [16]) - 0x40) = n - 64"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma to_nat_zidx1_lo:
  assumes "n < 65536"
  shows "to_nat ((0x2 :: [16]) + (from_nat n :: [16]) div 0x80) = 2 + n div 128"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_of_nat)
  done

lemma to_nat_zidx1_hi:
  assumes "64 \<le> n" and "n < 65536"
  shows "to_nat ((0x2 :: [16]) + ((from_nat n :: [16]) - 0x40) div 0x80) = 2 + (n - 64) div 128"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma half_test1:
  assumes "n < 65536"
  shows "(((from_nat n :: [16]) mod 0x80 < 0x40)) = (n mod 128 < 64)"
  using assms
  apply (simp add: from_nat_def from_int_word_def word_seq_convs cryptol_prim_defs)
  apply (simp add: word_less_nat_alt unat_mod unat_of_nat)
  done

lemma level1_lo:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and lo: "n mod 128 < 64"
  shows "nth_seq (nttLevel 1 a) n
       = (nth_seq a n) + fqmul (nth_seq zetas (2 + n div 128)) (nth_seq a (n + 64))"
proof -
  have n65: "n < 65536" using n2 by simp
  have np: "n < 65472" using n2 by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt1 len1_op twolen1_op base1_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test1[OF n65] lo n2
                     to_nat_from_nat16[OF n65] to_nat_plus64[OF np] to_nat_zidx1_lo[OF n65])
    done
qed

lemma level1_hi:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and hi: "\<not> n mod 128 < 64"
  shows "nth_seq (nttLevel 1 a) n
       = (nth_seq a (n - 64)) - fqmul (nth_seq zetas (2 + (n - 64) div 128)) (nth_seq a n)"
proof -
  have n65: "n < 65536" using n2 by simp
  have n1: "64 \<le> n" using hi by (cases "n < 64") auto
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt1 len1_op twolen1_op base1_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test1[OF n65] hi n2
                     to_nat_from_nat16[OF n65] to_nat_minus64[OF n1 n65] to_nat_zidx1_hi[OF n1 n65])
    done
qed

text \<open>Level-1 coefficient law. The twiddle index is the block index \<open>base + m div twolen\<close>;
  the upper leg reads it at \<open>m - len\<close>, which stays in the same 128-block, so \<open>2 + (n-64) div
  128 = 2 + n div 128\<close> (not re-proved here: the two legs are stated in the form each produces).\<close>
lemma level1_coeff:
  fixes a :: "[256][16]"
  assumes n: "n < 256"
  shows "nth_seq (nttLevel 1 a) n
       = (if n mod 128 < 64
          then (nth_seq a n) + fqmul (nth_seq zetas (2 + n div 128)) (nth_seq a (n + 64))
          else (nth_seq a (n - 64)) - fqmul (nth_seq zetas (2 + (n - 64) div 128)) (nth_seq a n))"
proof (cases "n mod 128 < 64")
  case True
  thus ?thesis using level1_lo[OF n True] by simp
next
  case False
  thus ?thesis using level1_hi[OF n False] by simp
qed

section \<open>Level-2 coefficient law (len=32, twolen=64, base=4, twiddle zetas[4 + n div 64])\<close>

lemma amt2:       "bl_to_bin (seq_to_list (2::[16])) = 2" by eval
lemma len2_op:    "right_shift (0x80  :: [16]) 2 = (0x20 :: [16])" by eval
lemma twolen2_op: "right_shift (0x100 :: [16]) 2 = (0x40 :: [16])" by eval
lemma base2_op:   "left_shift  (0x1   :: [16]) 2 = (0x4  :: [16])" by eval

lemma to_nat_plus32:
  assumes "n < 65504"
  shows "to_nat ((from_nat n :: [16]) + 0x20) = n + 32"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

lemma to_nat_minus32:
  assumes "32 \<le> n" and "n < 65536"
  shows "to_nat ((from_nat n :: [16]) - 0x20) = n - 32"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma to_nat_zidx2_lo:
  assumes "n < 65536"
  shows "to_nat ((0x4 :: [16]) + (from_nat n :: [16]) div 0x40) = 4 + n div 64"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_of_nat)
  done

lemma to_nat_zidx2_hi:
  assumes "32 \<le> n" and "n < 65536"
  shows "to_nat ((0x4 :: [16]) + ((from_nat n :: [16]) - 0x20) div 0x40) = 4 + (n - 32) div 64"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma half_test2:
  assumes "n < 65536"
  shows "(((from_nat n :: [16]) mod 0x40 < 0x20)) = (n mod 64 < 32)"
  using assms
  apply (simp add: from_nat_def from_int_word_def word_seq_convs cryptol_prim_defs)
  apply (simp add: word_less_nat_alt unat_mod unat_of_nat)
  done

lemma level2_lo:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and lo: "n mod 64 < 32"
  shows "nth_seq (nttLevel 2 a) n
       = (nth_seq a n) + fqmul (nth_seq zetas (4 + n div 64)) (nth_seq a (n + 32))"
proof -
  have n65: "n < 65536" using n2 by simp
  have np: "n < 65504" using n2 by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt2 len2_op twolen2_op base2_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test2[OF n65] lo n2
                     to_nat_from_nat16[OF n65] to_nat_plus32[OF np] to_nat_zidx2_lo[OF n65])
    done
qed

lemma level2_hi:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and hi: "\<not> n mod 64 < 32"
  shows "nth_seq (nttLevel 2 a) n
       = (nth_seq a (n - 32)) - fqmul (nth_seq zetas (4 + (n - 32) div 64)) (nth_seq a n)"
proof -
  have n65: "n < 65536" using n2 by simp
  have n1: "32 \<le> n" using hi by (cases "n < 32") auto
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt2 len2_op twolen2_op base2_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test2[OF n65] hi n2
                     to_nat_from_nat16[OF n65] to_nat_minus32[OF n1 n65] to_nat_zidx2_hi[OF n1 n65])
    done
qed

lemma level2_coeff:
  fixes a :: "[256][16]"
  assumes n: "n < 256"
  shows "nth_seq (nttLevel 2 a) n
       = (if n mod 64 < 32
          then (nth_seq a n) + fqmul (nth_seq zetas (4 + n div 64)) (nth_seq a (n + 32))
          else (nth_seq a (n - 32)) - fqmul (nth_seq zetas (4 + (n - 32) div 64)) (nth_seq a n))"
proof (cases "n mod 64 < 32")
  case True
  thus ?thesis using level2_lo[OF n True] by simp
next
  case False
  thus ?thesis using level2_hi[OF n False] by simp
qed

section \<open>Level-3 coefficient law (len=16, twolen=32, base=8, twiddle zetas[8 + n div 32])\<close>

lemma amt3:       "bl_to_bin (seq_to_list (3::[16])) = 3" by eval
lemma len3_op:    "right_shift (0x80  :: [16]) 3 = (0x10 :: [16])" by eval
lemma twolen3_op: "right_shift (0x100 :: [16]) 3 = (0x20 :: [16])" by eval
lemma base3_op:   "left_shift  (0x1   :: [16]) 3 = (0x8  :: [16])" by eval

lemma to_nat_plus16:
  assumes "n < 65520"
  shows "to_nat ((from_nat n :: [16]) + 0x10) = n + 16"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

lemma to_nat_minus16:
  assumes "16 \<le> n" and "n < 65536"
  shows "to_nat ((from_nat n :: [16]) - 0x10) = n - 16"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma to_nat_zidx3_lo:
  assumes "n < 65536"
  shows "to_nat ((0x8 :: [16]) + (from_nat n :: [16]) div 0x20) = 8 + n div 32"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_of_nat)
  done

lemma to_nat_zidx3_hi:
  assumes "16 \<le> n" and "n < 65536"
  shows "to_nat ((0x8 :: [16]) + ((from_nat n :: [16]) - 0x10) div 0x20) = 8 + (n - 16) div 32"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma half_test3:
  assumes "n < 65536"
  shows "(((from_nat n :: [16]) mod 0x20 < 0x10)) = (n mod 32 < 16)"
  using assms
  apply (simp add: from_nat_def from_int_word_def word_seq_convs cryptol_prim_defs)
  apply (simp add: word_less_nat_alt unat_mod unat_of_nat)
  done

lemma level3_lo:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and lo: "n mod 32 < 16"
  shows "nth_seq (nttLevel 3 a) n
       = (nth_seq a n) + fqmul (nth_seq zetas (8 + n div 32)) (nth_seq a (n + 16))"
proof -
  have n65: "n < 65536" using n2 by simp
  have np: "n < 65520" using n2 by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt3 len3_op twolen3_op base3_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test3[OF n65] lo n2
                     to_nat_from_nat16[OF n65] to_nat_plus16[OF np] to_nat_zidx3_lo[OF n65])
    done
qed

lemma level3_hi:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and hi: "\<not> n mod 32 < 16"
  shows "nth_seq (nttLevel 3 a) n
       = (nth_seq a (n - 16)) - fqmul (nth_seq zetas (8 + (n - 16) div 32)) (nth_seq a n)"
proof -
  have n65: "n < 65536" using n2 by simp
  have n1: "16 \<le> n" using hi by (cases "n < 16") auto
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt3 len3_op twolen3_op base3_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test3[OF n65] hi n2
                     to_nat_from_nat16[OF n65] to_nat_minus16[OF n1 n65] to_nat_zidx3_hi[OF n1 n65])
    done
qed

lemma level3_coeff:
  fixes a :: "[256][16]"
  assumes n: "n < 256"
  shows "nth_seq (nttLevel 3 a) n
       = (if n mod 32 < 16
          then (nth_seq a n) + fqmul (nth_seq zetas (8 + n div 32)) (nth_seq a (n + 16))
          else (nth_seq a (n - 16)) - fqmul (nth_seq zetas (8 + (n - 16) div 32)) (nth_seq a n))"
proof (cases "n mod 32 < 16")
  case True
  thus ?thesis using level3_lo[OF n True] by simp
next
  case False
  thus ?thesis using level3_hi[OF n False] by simp
qed

section \<open>Level-4 coefficient law (len=8, twolen=16, base=16, twiddle zetas[16 + n div 16])\<close>

lemma amt4:       "bl_to_bin (seq_to_list (4::[16])) = 4" by eval
lemma len4_op:    "right_shift (0x80  :: [16]) 4 = (0x8  :: [16])" by eval
lemma twolen4_op: "right_shift (0x100 :: [16]) 4 = (0x10 :: [16])" by eval
lemma base4_op:   "left_shift  (0x1   :: [16]) 4 = (0x10 :: [16])" by eval

lemma to_nat_plus8:
  assumes "n < 65528"
  shows "to_nat ((from_nat n :: [16]) + 0x8) = n + 8"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

lemma to_nat_minus8:
  assumes "8 \<le> n" and "n < 65536"
  shows "to_nat ((from_nat n :: [16]) - 0x8) = n - 8"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma to_nat_zidx4_lo:
  assumes "n < 65536"
  shows "to_nat ((0x10 :: [16]) + (from_nat n :: [16]) div 0x10) = 16 + n div 16"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_of_nat)
  done

lemma to_nat_zidx4_hi:
  assumes "8 \<le> n" and "n < 65536"
  shows "to_nat ((0x10 :: [16]) + ((from_nat n :: [16]) - 0x8) div 0x10) = 16 + (n - 8) div 16"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma half_test4:
  assumes "n < 65536"
  shows "(((from_nat n :: [16]) mod 0x10 < 0x8)) = (n mod 16 < 8)"
  using assms
  apply (simp add: from_nat_def from_int_word_def word_seq_convs cryptol_prim_defs)
  apply (simp add: word_less_nat_alt unat_mod unat_of_nat)
  done

lemma level4_lo:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and lo: "n mod 16 < 8"
  shows "nth_seq (nttLevel 4 a) n
       = (nth_seq a n) + fqmul (nth_seq zetas (16 + n div 16)) (nth_seq a (n + 8))"
proof -
  have n65: "n < 65536" using n2 by simp
  have np: "n < 65528" using n2 by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt4 len4_op twolen4_op base4_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test4[OF n65] lo n2
                     to_nat_from_nat16[OF n65] to_nat_plus8[OF np] to_nat_zidx4_lo[OF n65])
    done
qed

lemma level4_hi:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and hi: "\<not> n mod 16 < 8"
  shows "nth_seq (nttLevel 4 a) n
       = (nth_seq a (n - 8)) - fqmul (nth_seq zetas (16 + (n - 8) div 16)) (nth_seq a n)"
proof -
  have n65: "n < 65536" using n2 by simp
  have n1: "8 \<le> n" using hi by (cases "n < 8") auto
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt4 len4_op twolen4_op base4_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test4[OF n65] hi n2
                     to_nat_from_nat16[OF n65] to_nat_minus8[OF n1 n65] to_nat_zidx4_hi[OF n1 n65])
    done
qed

lemma level4_coeff:
  fixes a :: "[256][16]"
  assumes n: "n < 256"
  shows "nth_seq (nttLevel 4 a) n
       = (if n mod 16 < 8
          then (nth_seq a n) + fqmul (nth_seq zetas (16 + n div 16)) (nth_seq a (n + 8))
          else (nth_seq a (n - 8)) - fqmul (nth_seq zetas (16 + (n - 8) div 16)) (nth_seq a n))"
proof (cases "n mod 16 < 8")
  case True
  thus ?thesis using level4_lo[OF n True] by simp
next
  case False
  thus ?thesis using level4_hi[OF n False] by simp
qed

section \<open>Level-5 coefficient law (len=4, twolen=8, base=32, twiddle zetas[32 + n div 8])\<close>

lemma amt5:       "bl_to_bin (seq_to_list (5::[16])) = 5" by eval
lemma len5_op:    "right_shift (0x80  :: [16]) 5 = (0x4  :: [16])" by eval
lemma twolen5_op: "right_shift (0x100 :: [16]) 5 = (0x8  :: [16])" by eval
lemma base5_op:   "left_shift  (0x1   :: [16]) 5 = (0x20 :: [16])" by eval

lemma to_nat_plus4:
  assumes "n < 65532"
  shows "to_nat ((from_nat n :: [16]) + 0x4) = n + 4"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

lemma to_nat_minus4:
  assumes "4 \<le> n" and "n < 65536"
  shows "to_nat ((from_nat n :: [16]) - 0x4) = n - 4"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma to_nat_zidx5_lo:
  assumes "n < 65536"
  shows "to_nat ((0x20 :: [16]) + (from_nat n :: [16]) div 0x8) = 32 + n div 8"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_of_nat)
  done

lemma to_nat_zidx5_hi:
  assumes "4 \<le> n" and "n < 65536"
  shows "to_nat ((0x20 :: [16]) + ((from_nat n :: [16]) - 0x4) div 0x8) = 32 + (n - 4) div 8"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma half_test5:
  assumes "n < 65536"
  shows "(((from_nat n :: [16]) mod 0x8 < 0x4)) = (n mod 8 < 4)"
  using assms
  apply (simp add: from_nat_def from_int_word_def word_seq_convs cryptol_prim_defs)
  apply (simp add: word_less_nat_alt unat_mod unat_of_nat)
  done

lemma level5_lo:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and lo: "n mod 8 < 4"
  shows "nth_seq (nttLevel 5 a) n
       = (nth_seq a n) + fqmul (nth_seq zetas (32 + n div 8)) (nth_seq a (n + 4))"
proof -
  have n65: "n < 65536" using n2 by simp
  have np: "n < 65532" using n2 by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt5 len5_op twolen5_op base5_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test5[OF n65] lo n2
                     to_nat_from_nat16[OF n65] to_nat_plus4[OF np] to_nat_zidx5_lo[OF n65])
    done
qed

lemma level5_hi:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and hi: "\<not> n mod 8 < 4"
  shows "nth_seq (nttLevel 5 a) n
       = (nth_seq a (n - 4)) - fqmul (nth_seq zetas (32 + (n - 4) div 8)) (nth_seq a n)"
proof -
  have n65: "n < 65536" using n2 by simp
  have n1: "4 \<le> n" using hi by (cases "n < 4") auto
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt5 len5_op twolen5_op base5_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test5[OF n65] hi n2
                     to_nat_from_nat16[OF n65] to_nat_minus4[OF n1 n65] to_nat_zidx5_hi[OF n1 n65])
    done
qed

lemma level5_coeff:
  fixes a :: "[256][16]"
  assumes n: "n < 256"
  shows "nth_seq (nttLevel 5 a) n
       = (if n mod 8 < 4
          then (nth_seq a n) + fqmul (nth_seq zetas (32 + n div 8)) (nth_seq a (n + 4))
          else (nth_seq a (n - 4)) - fqmul (nth_seq zetas (32 + (n - 4) div 8)) (nth_seq a n))"
proof (cases "n mod 8 < 4")
  case True
  thus ?thesis using level5_lo[OF n True] by simp
next
  case False
  thus ?thesis using level5_hi[OF n False] by simp
qed

section \<open>Level-6 coefficient law (len=2, twolen=4, base=64, twiddle zetas[64 + n div 4])\<close>

text \<open>Final level, stride 2. The ML-KEM NTT stops here (128 degree-2 residues), so unlike
  the ML-DSA layer schedule there is no stride-1 level and no \<open>mod 2 < 1\<close> collapse. The
  partner index is the word literal \<open>+ 0x2\<close> / \<open>- 0x2\<close>, so the same helper form as level 5
  applies (no nat-level \<open>Suc\<close>-tower normalisation).\<close>

lemma amt6:       "bl_to_bin (seq_to_list (6::[16])) = 6" by eval
lemma len6_op:    "right_shift (0x80  :: [16]) 6 = (0x2  :: [16])" by eval
lemma twolen6_op: "right_shift (0x100 :: [16]) 6 = (0x4  :: [16])" by eval
lemma base6_op:   "left_shift  (0x1   :: [16]) 6 = (0x40 :: [16])" by eval

lemma to_nat_plus2:
  assumes "n < 65534"
  shows "to_nat ((from_nat n :: [16]) + 0x2) = n + 2"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

lemma to_nat_minus2:
  assumes "2 \<le> n" and "n < 65536"
  shows "to_nat ((from_nat n :: [16]) - 0x2) = n - 2"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma to_nat_zidx6_lo:
  assumes "n < 65536"
  shows "to_nat ((0x40 :: [16]) + (from_nat n :: [16]) div 0x4) = 64 + n div 4"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_of_nat)
  done

lemma to_nat_zidx6_hi:
  assumes "2 \<le> n" and "n < 65536"
  shows "to_nat ((0x40 :: [16]) + ((from_nat n :: [16]) - 0x2) div 0x4) = 64 + (n - 2) div 4"
  using assms
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def
                   word_seq_convs cryptol_prim_defs)
  apply (simp add: unat_word_ariths unat_div unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma half_test6:
  assumes "n < 65536"
  shows "(((from_nat n :: [16]) mod 0x4 < 0x2)) = (n mod 4 < 2)"
  using assms
  apply (simp add: from_nat_def from_int_word_def word_seq_convs cryptol_prim_defs)
  apply (simp add: word_less_nat_alt unat_mod unat_of_nat)
  done

lemma level6_lo:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and lo: "n mod 4 < 2"
  shows "nth_seq (nttLevel 6 a) n
       = (nth_seq a n) + fqmul (nth_seq zetas (64 + n div 4)) (nth_seq a (n + 2))"
proof -
  have n65: "n < 65536" using n2 by simp
  have np: "n < 65534" using n2 by simp
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt6 len6_op twolen6_op base6_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test6[OF n65] lo n2
                     to_nat_from_nat16[OF n65] to_nat_plus2[OF np] to_nat_zidx6_lo[OF n65])
    done
qed

lemma level6_hi:
  fixes a :: "[256][16]"
  assumes n2: "n < 256" and hi: "\<not> n mod 4 < 2"
  shows "nth_seq (nttLevel 6 a) n
       = (nth_seq a (n - 2)) - fqmul (nth_seq zetas (64 + (n - 2) div 4)) (nth_seq a n)"
proof -
  have n65: "n < 65536" using n2 by simp
  have n1: "2 \<le> n" using hi by (cases "n < 2") auto
  show ?thesis
    apply (simp add: nttLevel_def Let_def amt6 len6_op twolen6_op base6_op
                     map_seq_nth nth_seq_conv seq_to_list n2)
    apply (simp add: half_test6[OF n65] hi n2
                     to_nat_from_nat16[OF n65] to_nat_minus2[OF n1 n65] to_nat_zidx6_hi[OF n1 n65])
    done
qed

lemma level6_coeff:
  fixes a :: "[256][16]"
  assumes n: "n < 256"
  shows "nth_seq (nttLevel 6 a) n
       = (if n mod 4 < 2
          then (nth_seq a n) + fqmul (nth_seq zetas (64 + n div 4)) (nth_seq a (n + 2))
          else (nth_seq a (n - 2)) - fqmul (nth_seq zetas (64 + (n - 2) div 4)) (nth_seq a n))"
proof (cases "n mod 4 < 2")
  case True
  thus ?thesis using level6_lo[OF n True] by simp
next
  case False
  thus ?thesis using level6_hi[OF n False] by simp
qed

section \<open>Normal-domain twiddle value and the per-butterfly normal congruence\<close>

text \<open>The montgomery-domain twiddle table stores \<open>zeta * 2^16 mod q\<close> (signed). The
  normal twiddle value is recovered by multiplying by the inverse of \<open>2^16\<close> mod \<open>q\<close>,
  which is \<open>169\<close> (\<open>65536 * 169 = 3329 * 3327 + 1\<close>). We keep it reduced into \<open>[0, q)\<close>.
  This is the ML-KEM analogue of the ML-DSA normal table \<open>zetabrv\<close> (there the C table
  is \<open>zeta * 2^32\<close> and the inverse factor is baked into a separate literal table); here
  the montgomery table is the only concrete twiddle data, so the normal value is defined
  from it directly. Brick (c) will later identify \<open>zntt (base + blk)\<close> with the FIPS-203
  closed form \<open>17^(2*brv7 i + 1) mod q\<close> by evaluation.\<close>
definition zntt :: "nat \<Rightarrow> int" where
  "zntt k = (169 * sint_seq (nth_seq zetas k)) mod 3329"

lemma zntt_bound: "0 \<le> zntt k \<and> zntt k < 3329"
  unfolding zntt_def by simp

text \<open>The defining relation: \<open>2^16 * zntt k \<equiv> sint(zetas[k]) (mod q)\<close>, i.e. \<open>zntt\<close> is the
  montgomery table pulled back out of the montgomery domain. Since \<open>65536 * 169 \<equiv> 1 (mod q)\<close>
  the factor cancels.\<close>
lemma zntt_rel:
  "(65536 * zntt k) mod 3329 = sint_seq (nth_seq zetas k) mod 3329"
proof -
  define s where "s = sint_seq (nth_seq zetas k)"
  have step1: "(65536 * zntt k) mod 3329 = (11075584 * s) mod 3329"
  proof -
    have "(65536 * zntt k) mod 3329
        = (65536 * ((169 * s) mod 3329)) mod 3329"
      unfolding zntt_def s_def by simp
    also have "\<dots> = (65536 * (169 * s)) mod 3329"
      by (simp add: mod_mult_right_eq)
    also have "\<dots> = (11075584 * s) mod 3329"
      by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  have base: "[(11075584::int) = 1] (mod 3329)" by (simp add: cong_def)
  have r: "[s = s] (mod 3329)" by (simp add: cong_def)
  have "[11075584 * s = 1 * s] (mod 3329)" using cong_mult[OF base r] .
  hence "[11075584 * s = s] (mod 3329)" by simp
  hence "(11075584 * s) mod 3329 = s mod 3329" by (simp add: cong_def)
  thus ?thesis using step1 unfolding s_def by simp
qed

text \<open>Per-butterfly normal congruence: the montgomery butterfly term \<open>fqmul zetas[k] x\<close> is,
  modulo \<open>q\<close>, the normal-domain product \<open>zntt k * x\<close>. Combines \<open>butterfly_law_kem\<close> (the fqmul
  congruence \<open>2^16 * fqmul \<equiv> sint(zetas[k]) * x\<close>) with \<open>zntt_rel\<close>, cancelling the montgomery
  factor \<open>2^16\<close> (coprime to the prime \<open>q\<close>). ML-KEM analogue of ML-DSA \<open>butterfly_cong\<close>.\<close>
lemma bfly_cong_kem:
  fixes x :: "[16]" and B :: int
  assumes xlo: "- B \<le> sint_seq x" and xhi: "sint_seq x \<le> B" and Bhi: "B \<le> 32767"
  shows "sint_seq (fqmul (nth_seq zetas k) x) mod 3329 = (zntt k * sint_seq x) mod 3329"
proof -
  have cong: "(65536 * sint_seq (fqmul (nth_seq zetas k) x)) mod 3329
            = (sint_seq (nth_seq zetas k) * sint_seq x) mod 3329"
    using conjunct2[OF conjunct2[OF butterfly_law_kem[OF xlo xhi Bhi]]] .
  have e: "(sint_seq (nth_seq zetas k) * sint_seq x) mod 3329
         = (65536 * (zntt k * sint_seq x)) mod 3329"
  proof -
    have "(sint_seq (nth_seq zetas k) * sint_seq x) mod 3329
        = ((sint_seq (nth_seq zetas k) mod 3329) * sint_seq x) mod 3329"
      by (simp add: mod_mult_left_eq)
    also have "\<dots> = (((65536 * zntt k) mod 3329) * sint_seq x) mod 3329"
      by (simp add: zntt_rel)
    also have "\<dots> = ((65536 * zntt k) * sint_seq x) mod 3329"
      by (simp add: mod_mult_left_eq)
    also have "\<dots> = (65536 * (zntt k * sint_seq x)) mod 3329"
      by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  have comb: "(65536 * sint_seq (fqmul (nth_seq zetas k) x)) mod 3329
            = (65536 * (zntt k * sint_seq x)) mod 3329"
    using cong e by simp
  have cop: "coprime (65536::int) 3329"
  proof -
    have "gcd (65536::int) 3329 = 1" by eval
    thus ?thesis by (simp add: coprime_iff_gcd_eq_1)
  qed
  have "[65536 * sint_seq (fqmul (nth_seq zetas k) x) = 65536 * (zntt k * sint_seq x)] (mod 3329)"
    using comb by (simp add: cong_def)
  hence "[sint_seq (fqmul (nth_seq zetas k) x) = zntt k * sint_seq x] (mod 3329)"
    using cop by (simp add: cong_mult_lcancel)
  thus ?thesis by (simp add: cong_def)
qed

end

end
