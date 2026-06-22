(* Tier-2 word-level bridge (WIP): reason on the SAW-anchored lifted transform
   nttFwdAllRef. First brick: the lifted foldl over the 8 (len,iter,m0) tuples
   unfolds to the explicit 8-layer composition. *)
theory Bridge_Word
  imports "Tier2_Base.fips204_ntt_lift" "Tier2_Base.Bitrev" "Tier2_Base.Negacyclic_NTT"
begin

context includes cryptol_syntax begin

lemma fwd_unfold:
  "nttFwdAllRef w =
     nttLayerFwd 1 128 127 (nttLayerFwd 2 64 63 (nttLayerFwd 4 32 31
     (nttLayerFwd 8 16 15 (nttLayerFwd 16 8 7 (nttLayerFwd 32 4 3
     (nttLayerFwd 64 2 1 (nttLayerFwd 128 1 0 w)))))))"
  unfolding nttFwdAllRef_def fwdParamsRef_def Let_def
  by (simp add: foldl_seq.rep_eq)

end

text \<open>Per-op seam: the lifted forward-butterfly add (\<open>w[j] = (w[j] + t) mod q\<close>,
  done in 64-bit then truncated to 32) computes integer addition mod q, for
  coefficients already in \<open>[0,q)\<close>. Word-level via the v1 \<open>word_seq_convs\<close> route.\<close>
text \<open>The no-overflow integer fact behind the 64-bit add-then-reduce.\<close>
lemma add_mod_aux:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "take_bit 32 ((take_bit 64 A + take_bit 64 B) mod 18446744073709551616 mod 8380417)
         = (A + B) mod 8380417"
proof -
  have tA: "take_bit 64 A = A" using assms by (simp add: take_bit_int_eq_self)
  have tB: "take_bit 64 B = B" using assms by (simp add: take_bit_int_eq_self)
  have s: "(A + B) mod 18446744073709551616 = A + B"
    using assms by (simp add: mod_pos_pos_trivial)
  have lt: "(A + B) mod 8380417 < 2 ^ 32"
    using pos_mod_bound[of 8380417 "A + B"] by simp
  have ge: "0 \<le> (A + B) mod 8380417" by simp
  show ?thesis using tA tB s lt ge by (simp add: take_bit_int_eq_self)
qed

text \<open>Variant for op_add_hi: only the first summand carries a \<open>take_bit 64\<close>
  (it comes from a \<open>zext\<close>); the second is an already-64-bit reduced value.\<close>
lemma add_mod_aux2:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "take_bit 32 ((take_bit 64 A + B) mod 18446744073709551616 mod 8380417)
         = (A + B) mod 8380417"
proof -
  have tA: "take_bit 64 A = A" using assms by (simp add: take_bit_int_eq_self)
  have s: "(A + B) mod 18446744073709551616 = A + B"
    using assms by (simp add: mod_pos_pos_trivial)
  have lt: "(A + B) mod 8380417 < 2 ^ 32"
    using pos_mod_bound[of 8380417 "A + B"] by simp
  have ge: "0 \<le> (A + B) mod 8380417" by simp
  show ?thesis using tA s lt ge by (simp add: take_bit_int_eq_self)
qed

text \<open>Variant where neither summand carries a \<open>take_bit 64\<close>: the lower butterfly
  output \<open>(w[j] + (z*w[j+len] mod q)) mod q\<close> after the twiddle term is reduced.\<close>
lemma add_mod_aux3:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "take_bit 32 ((A + B) mod 18446744073709551616 mod 8380417)
         = (A + B) mod 8380417"
proof -
  have s: "(A + B) mod 18446744073709551616 = A + B"
    using assms by (simp add: mod_pos_pos_trivial)
  have lt: "(A + B) mod 8380417 < 2 ^ 32"
    using pos_mod_bound[of 8380417 "A + B"] by simp
  have ge: "0 \<le> (A + B) mod 8380417" by simp
  show ?thesis using s lt ge by (simp add: take_bit_int_eq_self)
qed

text \<open>No-overflow integer fact behind the 64-bit multiply-then-reduce: the
  product of two coefficients in \<open>[0,q)\<close> is below \<open>q^2 < 2^64\<close>, so the 64-bit
  multiply never wraps.\<close>
lemma mul_mod_aux:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "A * B mod 18446744073709551616 mod 8380417 = (A * B) mod 8380417"
proof -
  have "A * B < 8380417 * 8380417" using assms by (intro mult_strict_mono) auto
  hence "A * B < 18446744073709551616" by simp
  moreover have "0 \<le> A * B" using assms by simp
  ultimately have "A * B mod 18446744073709551616 = A * B"
    by (simp add: mod_pos_pos_trivial)
  thus ?thesis by simp
qed

text \<open>No-overflow integer fact behind the 64-bit subtract (computed as
  \<open>(x + q - y) mod q\<close> to stay non-negative): \<open>x + q < 2q < 2^64\<close>.\<close>
lemma sub_mod_aux:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "take_bit 32 ((A + 8380417 - B) mod 18446744073709551616 mod 8380417)
         = (A + 8380417 - B) mod 8380417"
proof -
  have c0: "0 \<le> A + 8380417 - B" using assms by simp
  have c1: "A + 8380417 - B < 18446744073709551616" using assms by simp
  from c0 c1 have m: "(A + 8380417 - B) mod 18446744073709551616 = A + 8380417 - B"
    by (simp add: mod_pos_pos_trivial)
  have lt: "(A + 8380417 - B) mod 8380417 < 2 ^ 32"
    using pos_mod_bound[of 8380417 "A + 8380417 - B"] by simp
  have ge: "0 \<le> (A + 8380417 - B) mod 8380417" by simp
  show ?thesis using m lt ge by (simp add: take_bit_int_eq_self)
qed

context includes cryptol_translation_syntax begin

lemma idx_val:
  assumes "n < (256::nat)"
  shows "to_nat (zext`{64,8} (from_nat n :: [8]) :: [64]) = n"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs)
  apply (simp add: to_nat_def to_int_word_def from_nat_def from_int_word_def)
  apply (subst unat_ucast_up_simp)
   apply simp
  apply (simp add: unat_of_nat)
  done

lemma idx_div0:
  assumes "n < (256::nat)"
  shows "(zext`{64,8} (from_nat n :: [8]) :: W) div 0x100 = 0"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small)
  apply (simp add: unat_arith_simps unat_word_ariths unat_of_nat)
  done

lemma idx_modlt:
  assumes "n < (256::nat)"
  shows "((zext`{64,8} (from_nat n :: [8]) :: W) mod 0x100 < 0x80) = (n < 128)"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small)
  apply (simp add: unat_arith_simps unat_word_ariths unat_of_nat)
  done

lemma idx_plus:
  assumes "n < (128::nat)"
  shows "to_nat ((zext`{64,8} (from_nat n :: [8]) :: W) + 0x80) = n + 128"
  using assms
  apply (simp add: to_nat_def to_int_word_def cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small)
  apply (simp add: unat_word_ariths unat_of_nat)
  done

lemma idx_minus:
  assumes "128 \<le> n" and "n < (256::nat)"
  shows "to_nat ((zext`{64,8} (from_nat n :: [8]) :: W) - 0x80) = n - 128"
  using assms
  apply (simp add: to_nat_def to_int_word_def cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small)
  apply (simp add: unat_sub_if' unat_of_nat word_le_nat_alt)
  done

lemma zext_uint:
  fixes a :: "[32]"
  shows "uint_seq (zext`{64,32} a) = uint_seq a"
  apply (simp add: cryptol_prim_defs word_seq_convs)
  apply (simp add: uint_up_ucast is_up)
  done

lemma drop_uint:
  fixes v :: "W"
  assumes "uint_seq v < 4294967296"
  shows "uint_seq (drop`{32,32,Bit} v) = uint_seq v"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs)
  apply (simp add: unsigned_ucast_eq unsigned_take_bit_eq take_bit_int_eq_self)
  done

lemma red_sub:
  fixes x y :: "W"
  assumes "uint_seq x < 8380417" and "uint_seq y < 8380417"
  shows "uint_seq (drop`{32,32,Bit}
            (((x +`{[64]} q) -`{[64]} y) %`{[64]} q))
         = (uint_seq x + 8380417 - uint_seq y) mod 8380417"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs q_def)
  apply (simp add: unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                   uint_mod_distrib uint_word_ariths)
  apply (rule sub_mod_aux)
  apply simp_all
  done

text \<open>Per-position unfold (recipe, demonstrated): with @{term "n < 256"},
  \<open>simp add: nttLayerFwd_def fromTo_def map_seq_nth upto_seq_nth\<close> reduces
  \<open>nth_seq (nttLayerFwd len iter m0 w) n\<close> to the let-bound butterfly body
  (blk/off/z, the \<open>iter \<le> blk\<close> untouched branch, and the lower/upper add/mul/sub
  branches that op_add/red_mul/red_sub bridge). Assembling this into a clean
  coefficient lemma needs the index arithmetic (to_nat/pos_nat/zext, div/mod on
  [64] words) and is the next step toward the CT routing.\<close>

lemma red_mul:
  fixes x y :: "W"
  assumes "uint_seq x < 8380417" and "uint_seq y < 8380417"
  shows "uint_seq ((x *`{[64]} y) %`{[64]} q) = (uint_seq x * uint_seq y) mod 8380417"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs q_def)
  apply (simp add: uint_mod_distrib uint_word_ariths)
  apply (rule mul_mod_aux)
  apply simp_all
  done

lemma op_add:
  fixes a b :: "[32]"
  assumes "uint_seq a < 8380417" and "uint_seq b < 8380417"
  shows "uint_seq (drop`{32,32,Bit}
            (((zext`{64,32} a) +`{[64]} (zext`{64,32} b)) %`{[64]} q))
         = (uint_seq a + uint_seq b) mod 8380417"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs q_def)
  apply (simp add: unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                   uint_mod_distrib uint_word_ariths)
  apply (rule add_mod_aux)
  apply simp_all
  done

text \<open>Add variant where the second summand is already a 64-bit reduced value
  (the butterfly twiddle term \<open>t\<close>), not a \<open>zext\<close> of a 32-bit coefficient.\<close>
lemma op_add_hi:
  fixes a :: "[32]" and B :: "W"
  assumes "uint_seq a < 8380417" and "uint_seq B < 8380417"
  shows "uint_seq (drop`{32,32,Bit}
            (((zext`{64,32} a) +`{[64]} B) %`{[64]} q))
         = (uint_seq a + uint_seq B) mod 8380417"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs q_def)
  apply (simp add: unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                   uint_mod_distrib uint_word_ariths)
  apply (rule add_mod_aux2)
  apply simp_all
  done

text \<open>A 64-bit value reduced mod q is below q (the twiddle term \<open>t\<close> is such).\<close>
lemma mod_q_lt:
  fixes v :: "W"
  shows "uint_seq (v %`{[64]} q) < 8380417"
  apply (simp add: cryptol_prim_defs word_seq_convs q_def)
  apply (simp add: uint_mod_distrib)
  done

text \<open>The first-layer twiddle factor \<open>zetabrv[1]\<close> is a valid coefficient (\<open>< q\<close>).\<close>
lemma zeta_bound_1:
  shows "uint_seq (nth_seq zetabrv 1) < 8380417"
  by (simp add: zetabrv_def uint_seq_conv word_seq_convs)

text \<open>Every twiddle factor in the bit-reversed table is a valid coefficient.
  Needed once \<open>z\<close> ranges over \<open>m0+blk+1\<close> in layers beyond the first.\<close>
lemma zeta_bound:
  assumes "j < 256"
  shows "uint_seq (nth_seq zetabrv j) < 8380417"
proof -
  have "\<forall>i<256. uint_seq (nth_seq zetabrv i) < 8380417" by eval
  thus ?thesis using assms by blast
qed

lemma layer1_lo:
  fixes w :: "[256][32]"
  assumes n: "n < (128::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 128 1 0 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv 1)
            * uint_seq (nth_seq w (n + 128)) mod 8380417) mod 8380417"
proof -
  have n256: "n < 256" using n by simp
  have np: "n + 128 < 256" using n by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n256] by (simp add: uint_seq_conv)
  have bn128: "uint (seq_to_word (nth_seq w (n + 128))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (Suc 0))) < 8380417"
    using zeta_bound_1 by (simp add: uint_seq_conv)
  have e1: "n mod 18446744073709551616 = n" using n by simp
  have e2: "n mod 256 = n" using n by simp
  have e3: "n div 256 = 0" using n by simp
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using n
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n256)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n256 uint_seq_conv)
    apply (simp add: n word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 e3)
    apply (simp add: tb bn bn128 bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer1_hi:
  fixes w :: "[256][32]"
  assumes n: "128 \<le> n" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 128 1 0 w) n)
       = (uint_seq (nth_seq w (n - 128)) + 8380417
          - uint_seq (nth_seq zetabrv 1)
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nm: "n - 128 < 256" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 128))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (Suc 0))) < 8380417"
    using zeta_bound_1 by (simp add: uint_seq_conv)
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "n mod 256 = n" using n2 by simp
  have e3: "n div 256 = 0" using n2 by simp
  have es: "unat (word_of_nat n - (0x80::64 word)) = n - 128"
    using n n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - 128))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - 128))) + 8380417"
    using bnm uint_seq_conv by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using n n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 e3 es)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

text \<open>Layer-1 (\<open>len=128, iter=1, m0=0\<close>) coefficient law: every output position is
  the FIPS-204 forward butterfly on the input coefficients, with twiddle
  \<open>zetabrv[1]\<close>. Lower half (\<open>n<128\<close>) is the additive leg, upper half the
  subtractive leg. Both legs proven word-exact (no proof holes, no \<open>smt\<close>).\<close>
lemma layer1_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 128 1 0 w) n)
       = (if n < 128
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv 1)
                  * uint_seq (nth_seq w (n + 128)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 128)) + 8380417
                - uint_seq (nth_seq zetabrv 1)
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
proof (cases "n < 128")
  case True
  thus ?thesis using layer1_lo[OF True bw] by simp
next
  case False
  hence "128 \<le> n" by simp
  thus ?thesis using layer1_hi[OF _ n bw] False by simp
qed

lemma layer2_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 128 < 64" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 64 2 1 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv (n div 128 + 2))
            * uint_seq (nth_seq w (n + 64)) mod 8380417) mod 8380417"
proof -
  have np: "n + 64 < 256" using hlo n2 by presburger
  have nd: "n div 128 + 2 < 256" using n2 by linarith
  have ndlt: "n div 128 < 2" using n2 by linarith
  have ndle: "\<not> 2 \<le> n div 128" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 64) mod 18446744073709551616 = n + 64" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bn64: "uint (seq_to_word (nth_seq w (n + 64))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (Suc (Suc (n div 128))))) < 8380417"
    using zeta_bound[of "n div 128 + 2"] nd by (simp add: uint_seq_conv)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt ndle)
    apply (simp add: tb bn bn64 bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer2_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 128 < 64" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 64 2 1 w) n)
       = (uint_seq (nth_seq w (n - 64)) + 8380417
          - uint_seq (nth_seq zetabrv (n div 128 + 2))
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nge: "64 \<le> n" using hhi by (cases "n < 64") auto
  have nm: "n - 64 < 256" using n2 by simp
  have nd: "n div 128 + 2 < 256" using n2 by linarith
  have ndle: "\<not> 2 \<le> n div 128" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 64))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (Suc (Suc (n div 128))))) < 8380417"
    using zeta_bound[of "n div 128 + 2"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x40::64 word)) = n - 64"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - 64))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - 64))) + 8380417"
    using bnm by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndle es)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

lemma layer2_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 64 2 1 w) n)
       = (if n mod 128 < 64
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv (n div 128 + 2))
                  * uint_seq (nth_seq w (n + 64)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 64)) + 8380417
                - uint_seq (nth_seq zetabrv (n div 128 + 2))
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
  using layer2_lo[OF _ n bw] layer2_hi[OF _ n bw] by simp

lemma layer3_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 64 < 32" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 32 4 3 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv (n div 64 + 4))
            * uint_seq (nth_seq w (n + 32)) mod 8380417) mod 8380417"
proof -
  have np: "n + 32 < 256" using hlo n2 by presburger
  have nd: "n div 64 + 4 < 256" using n2 by linarith
  have ndle: "\<not> 4 \<le> n div 64" using n2 by linarith
  have zc: "(4::nat) + n div 64 = n div 64 + 4" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 32) mod 18446744073709551616 = n + 32" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bn32: "uint (seq_to_word (nth_seq w (n + 32))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 64 + 4))) < 8380417"
    using zeta_bound[of "n div 64 + 4"] nd by (simp add: uint_seq_conv)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndle zc)
    apply (simp add: tb bn bn32 bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer3_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 64 < 32" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 32 4 3 w) n)
       = (uint_seq (nth_seq w (n - 32)) + 8380417
          - uint_seq (nth_seq zetabrv (n div 64 + 4))
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nge: "32 \<le> n" using hhi by (cases "n < 32") auto
  have nm: "n - 32 < 256" using n2 by simp
  have nd: "n div 64 + 4 < 256" using n2 by linarith
  have ndle: "\<not> 4 \<le> n div 64" using n2 by linarith
  have zc: "(4::nat) + n div 64 = n div 64 + 4" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 32))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 64 + 4))) < 8380417"
    using zeta_bound[of "n div 64 + 4"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x20::64 word)) = n - 32"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - 32))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - 32))) + 8380417"
    using bnm by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndle es zc)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

lemma layer3_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 32 4 3 w) n)
       = (if n mod 64 < 32
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv (n div 64 + 4))
                  * uint_seq (nth_seq w (n + 32)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 32)) + 8380417
                - uint_seq (nth_seq zetabrv (n div 64 + 4))
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
  using layer3_lo[OF _ n bw] layer3_hi[OF _ n bw] by simp

lemma layer_16_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 32 < 16" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 16 8 7 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv (n div 32 + 8))
            * uint_seq (nth_seq w (n + 16)) mod 8380417) mod 8380417"
proof -
  have np: "n + 16 < 256" using hlo n2 by presburger
  have nd: "n div 32 + 8 < 256" using n2 by linarith
  have ndle: "\<not> 8 \<le> n div 32" using n2 by linarith
  have zc: "(8::nat) + n div 32 = n div 32 + 8" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 16) mod 18446744073709551616 = n + 16" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnl: "uint (seq_to_word (nth_seq w (n + 16))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 32 + 8))) < 8380417"
    using zeta_bound[of "n div 32 + 8"] nd by (simp add: uint_seq_conv)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndle zc)
    apply (simp add: tb bn bnl bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer_16_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 32 < 16" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 16 8 7 w) n)
       = (uint_seq (nth_seq w (n - 16)) + 8380417
          - uint_seq (nth_seq zetabrv (n div 32 + 8))
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nge: "16 \<le> n" using hhi by (cases "n < 16") auto
  have nm: "n - 16 < 256" using n2 by simp
  have nd: "n div 32 + 8 < 256" using n2 by linarith
  have ndle: "\<not> 8 \<le> n div 32" using n2 by linarith
  have zc: "(8::nat) + n div 32 = n div 32 + 8" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 16))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 32 + 8))) < 8380417"
    using zeta_bound[of "n div 32 + 8"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x10::64 word)) = n - 16"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - 16))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - 16))) + 8380417"
    using bnm by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndle es zc)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

lemma layer_16_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 16 8 7 w) n)
       = (if n mod 32 < 16
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv (n div 32 + 8))
                  * uint_seq (nth_seq w (n + 16)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 16)) + 8380417
                - uint_seq (nth_seq zetabrv (n div 32 + 8))
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
  using layer_16_lo[OF _ n bw] layer_16_hi[OF _ n bw] by simp

lemma layer_8_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 16 < 8" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 8 16 15 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv (n div 16 + 16))
            * uint_seq (nth_seq w (n + 8)) mod 8380417) mod 8380417"
proof -
  have np: "n + 8 < 256" using hlo n2 by presburger
  have nd: "n div 16 + 16 < 256" using n2 by linarith
  have ndle: "\<not> 16 \<le> n div 16" using n2 by linarith
  have zc: "(16::nat) + n div 16 = n div 16 + 16" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 8) mod 18446744073709551616 = n + 8" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnl: "uint (seq_to_word (nth_seq w (n + 8))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 16 + 16))) < 8380417"
    using zeta_bound[of "n div 16 + 16"] nd by (simp add: uint_seq_conv)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndle zc)
    apply (simp add: tb bn bnl bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer_8_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 16 < 8" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 8 16 15 w) n)
       = (uint_seq (nth_seq w (n - 8)) + 8380417
          - uint_seq (nth_seq zetabrv (n div 16 + 16))
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nge: "8 \<le> n" using hhi by (cases "n < 8") auto
  have nm: "n - 8 < 256" using n2 by simp
  have nd: "n div 16 + 16 < 256" using n2 by linarith
  have ndle: "\<not> 16 \<le> n div 16" using n2 by linarith
  have zc: "(16::nat) + n div 16 = n div 16 + 16" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 8))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 16 + 16))) < 8380417"
    using zeta_bound[of "n div 16 + 16"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x8::64 word)) = n - 8"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - 8))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - 8))) + 8380417"
    using bnm by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndle es zc)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

lemma layer_8_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 8 16 15 w) n)
       = (if n mod 16 < 8
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv (n div 16 + 16))
                  * uint_seq (nth_seq w (n + 8)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 8)) + 8380417
                - uint_seq (nth_seq zetabrv (n div 16 + 16))
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
  using layer_8_lo[OF _ n bw] layer_8_hi[OF _ n bw] by simp

lemma layer_4_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 8 < 4" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 4 32 31 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv (n div 8 + 32))
            * uint_seq (nth_seq w (n + 4)) mod 8380417) mod 8380417"
proof -
  have np: "n + 4 < 256" using hlo n2 by presburger
  have nd: "n div 8 + 32 < 256" using n2 by linarith
  have ndle: "\<not> 32 \<le> n div 8" using n2 by linarith
  have zc: "(32::nat) + n div 8 = n div 8 + 32" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 4) mod 18446744073709551616 = n + 4" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnl: "uint (seq_to_word (nth_seq w (n + 4))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 8 + 32))) < 8380417"
    using zeta_bound[of "n div 8 + 32"] nd by (simp add: uint_seq_conv)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndle zc)
    apply (simp add: tb bn bnl bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer_4_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 8 < 4" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 4 32 31 w) n)
       = (uint_seq (nth_seq w (n - 4)) + 8380417
          - uint_seq (nth_seq zetabrv (n div 8 + 32))
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nge: "4 \<le> n" using hhi by (cases "n < 4") auto
  have nm: "n - 4 < 256" using n2 by simp
  have nd: "n div 8 + 32 < 256" using n2 by linarith
  have ndle: "\<not> 32 \<le> n div 8" using n2 by linarith
  have zc: "(32::nat) + n div 8 = n div 8 + 32" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 4))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 8 + 32))) < 8380417"
    using zeta_bound[of "n div 8 + 32"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x4::64 word)) = n - 4"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - 4))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - 4))) + 8380417"
    using bnm by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndle es zc)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

lemma layer_4_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 4 32 31 w) n)
       = (if n mod 8 < 4
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv (n div 8 + 32))
                  * uint_seq (nth_seq w (n + 4)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 4)) + 8380417
                - uint_seq (nth_seq zetabrv (n div 8 + 32))
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
  using layer_4_lo[OF _ n bw] layer_4_hi[OF _ n bw] by simp

lemma layer_2_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 4 < 2" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 2 64 63 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv (n div 4 + 64))
            * uint_seq (nth_seq w (n + 2)) mod 8380417) mod 8380417"
proof -
  have np: "n + 2 < 256" using hlo n2 by presburger
  have nd: "n div 4 + 64 < 256" using n2 by linarith
  have ndle: "\<not> 64 \<le> n div 4" using n2 by linarith
  have zc: "(64::nat) + n div 4 = n div 4 + 64" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "Suc (Suc n) mod 18446744073709551616 = Suc (Suc n)" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnl: "uint (seq_to_word (nth_seq w (Suc (Suc n)))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 4 + 64))) < 8380417"
    using zeta_bound[of "n div 4 + 64"] nd by (simp add: uint_seq_conv)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndle zc)
    apply (simp add: tb bn bnl bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer_2_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 4 < 2" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 2 64 63 w) n)
       = (uint_seq (nth_seq w (n - 2)) + 8380417
          - uint_seq (nth_seq zetabrv (n div 4 + 64))
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nge: "2 \<le> n" using hhi by (cases "n < 2") auto
  have nm: "n - 2 < 256" using n2 by simp
  have nd: "n div 4 + 64 < 256" using n2 by linarith
  have ndle: "\<not> 64 \<le> n div 4" using n2 by linarith
  have zc: "(64::nat) + n div 4 = n div 4 + 64" by simp
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 2))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 4 + 64))) < 8380417"
    using zeta_bound[of "n div 4 + 64"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x2::64 word)) = n - 2"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - 2))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - 2))) + 8380417"
    using bnm by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndle es zc)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

lemma layer_2_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 2 64 63 w) n)
       = (if n mod 4 < 2
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv (n div 4 + 64))
                  * uint_seq (nth_seq w (n + 2)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 2)) + 8380417
                - uint_seq (nth_seq zetabrv (n div 4 + 64))
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
  using layer_2_lo[OF _ n bw] layer_2_hi[OF _ n bw] by simp

lemma layer_1_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 2 < 1" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 1 128 127 w) n)
       = (uint_seq (nth_seq w n)
          + uint_seq (nth_seq zetabrv (n div 2 + 128))
            * uint_seq (nth_seq w (n + 1)) mod 8380417) mod 8380417"
proof -
  have np: "n + 1 < 256" using hlo n2 by presburger
  have nd: "n div 2 + 128 < 256" using n2 by linarith
  have ndle: "\<not> 128 \<le> n div 2" using n2 by linarith
  have zc: "(128::nat) + n div 2 = n div 2 + 128" by simp
  have wc: "(word_of_nat n mod 2 = (0::64 word)) = (n mod 2 = 0)"
    using n2 by (simp add: unat_arith_simps unat_of_nat)
  have wc2: "(word_of_nat n mod 2 = (1::64 word)) = (n mod 2 = 1)"
    using n2 by (simp add: unat_arith_simps unat_of_nat)
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "Suc n mod 18446744073709551616 = Suc n" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnl: "uint (seq_to_word (nth_seq w (Suc n))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 2 + 128))) < 8380417"
    using zeta_bound[of "n div 2 + 128"] nd by (simp add: uint_seq_conv)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndle zc wc wc2)
    apply (simp add: tb bn bnl bz mul_mod_aux)
    apply (simp add: add_mod_aux3 bn)
    done
qed

lemma layer_1_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 2 < 1" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 1 128 127 w) n)
       = (uint_seq (nth_seq w (n - 1)) + 8380417
          - uint_seq (nth_seq zetabrv (n div 2 + 128))
            * uint_seq (nth_seq w n) mod 8380417) mod 8380417"
proof -
  have nge: "1 \<le> n" using hhi by (cases "n < 1") auto
  have nm: "n - Suc 0 < 256" using n2 by simp
  have nd: "n div 2 + 128 < 256" using n2 by linarith
  have ndle: "\<not> 128 \<le> n div 2" using n2 by linarith
  have zc: "(128::nat) + n div 2 = n div 2 + 128" by simp
  have wc: "(word_of_nat n mod 2 = (0::64 word)) = (n mod 2 = 0)"
    using n2 by (simp add: unat_arith_simps unat_of_nat)
  have wc2: "(word_of_nat n mod 2 = (1::64 word)) = (n mod 2 = 1)"
    using n2 by (simp add: unat_arith_simps unat_of_nat)
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - Suc 0))) < 8380417"
    using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (n div 2 + 128))) < 8380417"
    using zeta_bound[of "n div 2 + 128"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x1::64 word)) = n - Suc 0"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em: "(uint (seq_to_word (nth_seq w (n - Suc 0))) + 8380417) mod 18446744073709551616
            = uint (seq_to_word (nth_seq w (n - Suc 0))) + 8380417"
    using bnm by (simp add: mod_pos_pos_trivial)
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerFwd_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndle es zc wc wc2)
    apply (simp add: tb bn bnm bz mul_mod_aux)
    apply (simp add: em sub_mod_aux bnm)
    done
qed

lemma layer_1_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerFwd 1 128 127 w) n)
       = (if n mod 2 < 1
          then (uint_seq (nth_seq w n)
                + uint_seq (nth_seq zetabrv (n div 2 + 128))
                  * uint_seq (nth_seq w (n + 1)) mod 8380417) mod 8380417
          else (uint_seq (nth_seq w (n - 1)) + 8380417
                - uint_seq (nth_seq zetabrv (n div 2 + 128))
                  * uint_seq (nth_seq w n) mod 8380417) mod 8380417)"
  using layer_1_lo[OF _ n bw] layer_1_hi[OF _ n bw] by simp

end
end
