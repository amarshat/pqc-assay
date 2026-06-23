(* Tier-2 model bridge (WIP): connect the SAW-checked montgomery NTT model
   (Assay.MLDSA_NTT.ntt, the function SAW proves the PQClean C equal to under
   -fwrapv) to the Tier-2 normal-domain model nttFwdAllRef, mod q.

   Goal:  sint_seq (ntt w @ k) == cf (nttFwdAllRef w) k   (mod q)
   chained with fwd_ntt_correct gives the SAW-checked model == FIPS-204 forward
   transform (mod q), closing the last gap in the C -> FIPS chain.

   This file is currently an ARCHITECTURE SPIKE: it only checks that the Assay
   session (montgomery_reduce_correct) and the Tier-2 session (fwd_ntt_correct)
   can be imported together. *)
theory Mont_Bridge
  imports Negacyclic_Bridge "Assay.Assay_Equivalence"
begin

text \<open>Foundation: the montgomery-domain twiddle table (Assay model \<open>zetas\<close>, stored
  signed) and the normal-domain table (Tier-2 \<open>zetabrv\<close>) agree at every index up
  to the Montgomery factor: \<open>sint(zetas[k]) \<equiv> 2^32 \<cdot> zetabrv[k] (mod q)\<close>. Both are
  the same primitive root \<open>\<zeta>=1753\<close> at bit-reversed index \<open>k\<close>; the C table is the
  Montgomery form. Proven by evaluation over the two concrete 256-entry tables.\<close>
text \<open>Index 0 is never an actual twiddle (the NTT accesses \<open>zetas[2^i + blk]\<close>, always
  \<open>\<ge> 1\<close>): there the montgomery table holds the dummy \<open>0\<close> while the normal table holds
  \<open>1\<close>, so the relation is stated for \<open>0 < k\<close>. Evaluated over the two tables' tails.\<close>
lemma zeta_rel:
  assumes k0: "0 < k" and k: "k < 256"
  shows "sint_seq (nth_seq zetas k) mod 8380417
       = (4294967296 * uint_seq (nth_seq zetabrv k)) mod 8380417"
proof -
  have L: "list_all (\<lambda>p. sint_seq (fst p) mod 8380417
                        = (4294967296 * uint_seq (snd p)) mod 8380417)
              (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)))"
    unfolding zetas_def zetabrv_def by eval
  have lz: "length (seq_to_list zetas) = 256" unfolding zetas_def by eval
  have lb: "length (seq_to_list zetabrv) = 256" unfolding zetabrv_def by eval
  define j where "j = k - 1"
  have jlt: "j < 255" using k0 k j_def by simp
  have ldz: "length (drop 1 (seq_to_list zetas)) = 255" using lz by simp
  have ldb: "length (drop 1 (seq_to_list zetabrv)) = 255" using lb by simp
  have lzip: "length (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv))) = 255"
    using ldz ldb by simp
  have app: "sint_seq (fst (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j)) mod 8380417
           = (4294967296 * uint_seq (snd (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j))) mod 8380417"
    using L jlt lzip by (simp add: list_all_length)
  have zk: "zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j
          = (drop 1 (seq_to_list zetas) ! j, drop 1 (seq_to_list zetabrv) ! j)"
    using jlt ldz ldb by (simp add: nth_zip)
  have dz: "drop 1 (seq_to_list zetas) ! j = seq_to_list zetas ! k"
    using k0 j_def by (simp add: nth_drop)
  have db: "drop 1 (seq_to_list zetabrv) ! j = seq_to_list zetabrv ! k"
    using k0 j_def by (simp add: nth_drop)
  have fz: "fst (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j)
          = seq_to_list zetas ! k"
    by (simp del: One_nat_def add: zk dz)
  have sz: "snd (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j)
          = seq_to_list zetabrv ! k"
    by (simp del: One_nat_def add: zk db)
  have core: "sint_seq (seq_to_list zetas ! k) mod 8380417
            = (4294967296 * uint_seq (seq_to_list zetabrv ! k)) mod 8380417"
    using app by (simp del: One_nat_def add: fz sz)
  have nz: "nth_seq zetas k = seq_to_list zetas ! k" using k lz by (simp add: seq_to_list)
  have nb: "nth_seq zetabrv k = seq_to_list zetabrv ! k" using k lb by (simp add: seq_to_list)
  show ?thesis using core nz nb by simp
qed

text \<open>Brick (b): the montgomery_reduce mod-q property, as a congruence usable by the
  bridge. This is the first conjunct of \<open>is_montgomery_reduction\<close> (proven in the Assay
  session as \<open>montgomery_reduce_correct\<close>): the reduced value scaled by the Montgomery
  factor \<open>2^32\<close> is congruent to the input modulo \<open>q\<close>.\<close>
lemma mont_mod_q:
  fixes a :: "(64, bool) seq"
  assumes "mont_input_ok (sint_seq a)"
  shows "(4294967296 * sint_seq (montgomery_reduce a)) mod 8380417 = sint_seq a mod 8380417"
proof -
  have "is_montgomery_reduction (sint_seq a) (sint_seq (montgomery_reduce a))"
    using assms by (rule montgomery_reduce_correct)
  thus ?thesis
    unfolding is_montgomery_reduction_def MLDSA_NTT_Spec.q_def by simp
qed

text \<open>Brick (c): the per-butterfly congruence. The montgomery butterfly term computed
  by the C model with the Montgomery twiddle \<open>zetas[i]\<close> is congruent, modulo \<open>q\<close>, to the
  normal-domain product \<open>zetabrv[i] \<cdot> x\<close> used by the Tier-2 model. Combines (a) \<open>zeta_rel\<close>
  with (b) \<open>mont_mod_q\<close> and cancels the Montgomery factor \<open>2^32\<close> (coprime to the prime
  \<open>q\<close>). The bound hypothesis \<open>mont_input_ok\<close> is discharged per-layer in brick (d) from a
  coefficient-size invariant.\<close>
lemma butterfly_cong:
  fixes x :: "(32, bool) seq"
  assumes i0: "0 < i" and i: "i < 256"
      and ok: "mont_input_ok (sint_seq (nth_seq zetas i) * sint_seq x)"
  shows "sint_seq (montgomery_reduce (sext64 (nth_seq zetas i) * sext64 x)) mod 8380417
       = (uint_seq (nth_seq zetabrv i) * sint_seq x) mod 8380417"
proof -
  define z  where "z  = nth_seq zetas i"
  define zb where "zb = uint_seq (nth_seq zetabrv i)"
  define sx where "sx = sint_seq x"
  define mr where "mr = sint_seq (montgomery_reduce (sext64 z * sext64 x))"
  \<comment> \<open>goal is now: \<open>mr mod 8380417 = (zb * sx) mod 8380417\<close>\<close>
  have ok2: "mont_input_ok (sint_seq (sext64 z * sext64 x))"
    using ok by (simp add: z_def sx_def sint_sext64_mult)
  have b: "(4294967296 * mr) mod 8380417 = (sint_seq z * sx) mod 8380417"
    using mont_mod_q[OF ok2] by (simp add: mr_def sx_def sint_sext64_mult)
  have zr: "sint_seq z mod 8380417 = (4294967296 * zb) mod 8380417"
    using zeta_rel[OF i0 i] by (simp add: z_def zb_def)
  have e: "(sint_seq z * sx) mod 8380417 = (4294967296 * (zb * sx)) mod 8380417"
  proof -
    have "(sint_seq z * sx) mod 8380417 = ((sint_seq z mod 8380417) * sx) mod 8380417"
      by (simp add: mod_mult_left_eq)
    also have "\<dots> = (((4294967296 * zb) mod 8380417) * sx) mod 8380417"
      by (simp add: zr)
    also have "\<dots> = ((4294967296 * zb) * sx) mod 8380417"
      by (simp add: mod_mult_left_eq)
    also have "\<dots> = (4294967296 * (zb * sx)) mod 8380417"
      by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  have comb: "(4294967296 * mr) mod 8380417 = (4294967296 * (zb * sx)) mod 8380417"
    using b e by simp
  have cop: "coprime (4294967296::int) 8380417"
  proof -
    have "gcd (4294967296::int) 8380417 = 1" by eval
    thus ?thesis by (simp add: coprime_iff_gcd_eq_1)
  qed
  have cong1: "[4294967296 * mr = 4294967296 * (zb * sx)] (mod 8380417)"
    using comb by (simp add: cong_def)
  have "[mr = zb * sx] (mod 8380417)"
    using cong1 cop by (simp add: cong_mult_lcancel)
  thus "mr mod 8380417 = (zb * sx) mod 8380417"
    by (simp add: cong_def)
qed

text \<open>Brick (d), part 1: the per-position unfolds of the montgomery model layers, plus the
  per-layer congruence to the abstract CT butterfly. The cryptol notation context is needed
  for the \<open>[256][32]\<close> types; coercion is disabled so the pure nat/int arithmetic (presburger
  would hang) goes through \<open>linarith\<close>.\<close>

context includes cryptol_syntax begin

declare [[coercion_enabled = false]]

text \<open>Sub-leg twiddle-block stability: on the upper half (\<open>n mod 2L \<ge> L\<close>) shifting the index
  down by the stride \<open>L\<close> leaves the block index \<open>n div 2L\<close> unchanged.\<close>
lemma sub_div_eq:
  fixes L n :: nat
  assumes b: "L \<le> n mod (2*L)" and n: "L \<le> n" and L: "0 < L"
  shows "(n - L) div (2*L) = n div (2*L)"
proof -
  have tl0: "0 < 2 * L" using L by simp
  have dec: "n div (2*L) * (2*L) + n mod (2*L) = n" by (rule div_mult_mod_eq)
  have m2L: "n mod (2 * L) < 2 * L" using tl0 by (rule mod_less_divisor)
  have lt: "n mod (2*L) - L < 2*L" using m2L by linarith
  have e: "n - L = (n mod (2*L) - L) + n div (2*L) * (2*L)"
    using dec b n by linarith
  have "(n - L) div (2*L) = ((n mod (2*L) - L) + n div (2*L) * (2*L)) div (2*L)"
    using e by simp
  also have "\<dots> = (n mod (2*L) - L) div (2*L) + n div (2*L)"
    using tl0 by (simp add: div_mult_self1 div_mult_self2 div_mult_self3 div_mult_self4)
  also have "\<dots> = n div (2*L)" using lt by simp
  finally show ?thesis .
qed

text \<open>No-overflow lifts of the int32 add/sub: when the signed sum/difference stays in int32
  range the word op agrees with integer arithmetic (extracted from \<open>butterfly_add_bound\<close>).\<close>
lemma sint_seq_add_eq:
  fixes x y :: "[32]"
  assumes "- 2147483648 \<le> sint_seq x + sint_seq y" "sint_seq x + sint_seq y < 2147483648"
  shows "sint_seq (x + y) = sint_seq x + sint_seq y"
proof -
  have "sint_seq (x + y) = sint (seq_to_word x + seq_to_word y)"
    by (simp add: probe_sint_seq word_seq_convs seq_to_word)
  also have "\<dots> = sint (seq_to_word x) + sint (seq_to_word y)"
    by (rule sint_add_inrange) (use assms in \<open>simp add: probe_sint_seq\<close>)+
  also have "\<dots> = sint_seq x + sint_seq y" by (simp add: probe_sint_seq)
  finally show ?thesis .
qed

lemma sint_seq_sub_eq:
  fixes x y :: "[32]"
  assumes "- 2147483648 \<le> sint_seq x - sint_seq y" "sint_seq x - sint_seq y < 2147483648"
  shows "sint_seq (x - y) = sint_seq x - sint_seq y"
proof -
  have "sint_seq (x - y) = sint (seq_to_word x - seq_to_word y)"
    by (simp add: probe_sint_seq word_seq_convs seq_to_word)
  also have "\<dots> = sint (seq_to_word x) - sint (seq_to_word y)"
    by (rule sint_sub_inrange) (use assms in \<open>simp add: probe_sint_seq\<close>)+
  also have "\<dots> = sint_seq x - sint_seq y" by (simp add: probe_sint_seq)
  finally show ?thesis .
qed

text \<open>Montgomery model, level 0 (stride 128). Output position \<open>n\<close> is the FIPS butterfly with
  the single montgomery twiddle \<open>zetas[1]\<close>; lower half additive, upper half subtractive. The
  montgomery_reduce term and coefficients are kept symbolic (their value congruence is
  \<open>butterfly_cong\<close>); only the seq-comprehension and [16] index arithmetic are resolved.\<close>
lemma mlevel0_lo:
  fixes a :: "[256][32]"
  assumes n: "n < (128::nat)"
  shows "nth_seq (nttLevel 0 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128)))"
proof -
  have n256: "n < 256" using n by simp
  have e1: "n mod 65536 = n" using n by simp
  have e2: "n mod 256 = n" using n by simp
  have e3: "n div 256 = 0" using n by simp
  show ?thesis
    using n
    apply (simp add: nttLevel_def fromTo_def Let_def n256)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 e3)
    done
qed

lemma mlevel0_hi:
  fixes a :: "[256][32]"
  assumes n: "128 \<le> n" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 0 a) n
       = nth_seq a (n - 128) - montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n))"
proof -
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "n mod 256 = n" using n2 by simp
  have e3: "n div 256 = 0" using n2 by simp
  have e3b: "(n - 128) div 256 = 0" using n2 by simp
  have es: "unat (word_of_nat n - (0x80::16 word)) = n - 128"
    using n n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  show ?thesis
    using n n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 e3 e3b es)
    done
qed

lemma mlevel0_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 0 a) n
       = (if n < 128
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128)))
          else nth_seq a (n - 128) - montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n)))"
proof (cases "n < 128")
  case True thus ?thesis using mlevel0_lo[OF True] by simp
next
  case False thus ?thesis using mlevel0_hi[OF _ n] n by simp
qed

text \<open>Montgomery model, level 1 (stride 64), twiddle \<open>zetas[n div 128 + 2]\<close>.\<close>
lemma mlevel1_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 128 < 64" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 1 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 128 + 2)) * sext64 (nth_seq a (n + 64)))"
proof -
  have dec: "128 * (n div 128) + n mod 128 = n" by simp
  have ndlt: "n div 128 < 2" using n2 by linarith
  have np: "n + 64 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "(n + 64) mod 65536 = n + 64" using np by simp
  have sh: "unat ((0x100::16 word) >> 1) = 128" "unat ((0x80::16 word) >> 1) = 64"
           "unat ((1::16 word) << 1) = 2" "((0x80::16 word) >> 1) = 0x40" by eval+
  show ?thesis
    using hlo n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma mlevel1_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 128 < 64" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 1 a) n
       = nth_seq a (n - 64) - montgomery_reduce (sext64 (nth_seq zetas (n div 128 + 2)) * sext64 (nth_seq a n))"
proof -
  have nge: "64 \<le> n" using hhi by (cases "n < 64") auto
  have e1: "n mod 65536 = n" using n2 by simp
  have ndlt: "n div 128 < 2" using n2 by linarith
  have e3b: "(n - 64) div 128 = n div 128" using sub_div_eq[of 64 n] hhi nge by simp
  have es: "unat (word_of_nat n - (0x40::16 word)) = n - 64"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have em1: "n div 128 mod 65536 = n div 128" using ndlt by simp
  have em2: "Suc (Suc (n div 128)) mod 65536 = Suc (Suc (n div 128))" using ndlt by simp
  have sh: "unat ((0x100::16 word) >> 1) = 128" "unat ((0x80::16 word) >> 1) = 64"
           "unat ((1::16 word) << 1) = 2" "((0x80::16 word) >> 1) = 0x40" by eval+
  show ?thesis
    using hhi n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt e3b es sh em1 em2)
    done
qed

lemma mlevel1_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 1 a) n
       = (if n mod 128 < 64
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 128 + 2)) * sext64 (nth_seq a (n + 64)))
          else nth_seq a (n - 64) - montgomery_reduce (sext64 (nth_seq zetas (n div 128 + 2)) * sext64 (nth_seq a n)))"
  using mlevel1_lo[OF _ n] mlevel1_hi[OF _ n] by simp

(* levels 2-7, regenerated with uniform robust fact set *)

lemma mlevel2_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 64 < 32" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 2 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 64 + 4)) * sext64 (nth_seq a (n + 32)))"
proof -
  have ndlt: "n div 64 < 4" using n2 by linarith
  have np: "n + 32 < 256" using hlo ndlt div_mult_mod_eq[of n 64] by linarith
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "(n + 32) mod 65536 = n + 32" using np by simp
  have emi: "n div 64 mod 65536 = n div 64" using ndlt by simp
  have emo: "(n div 64 + 4) mod 65536 = n div 64 + 4" using ndlt by simp
  have ec: "4 + n div 64 = n div 64 + 4" by simp
  have sh: "unat ((0x100::16 word) >> 2) = 64" "unat ((0x80::16 word) >> 2) = 32"
           "unat ((1::16 word) << 2) = 4" "((0x80::16 word) >> 2) = 0x20" by eval+
  show ?thesis using hlo n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 e2 hlo ndlt sh emi emo ec)
    done
qed

lemma mlevel2_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 64 < 32" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 2 a) n
       = nth_seq a (n - 32) - montgomery_reduce (sext64 (nth_seq zetas (n div 64 + 4)) * sext64 (nth_seq a n))"
proof -
  have nge: "32 \<le> n" using hhi by (cases "n < 32") auto
  have e1: "n mod 65536 = n" using n2 by simp
  have ndlt: "n div 64 < 4" using n2 by linarith
  have e3b: "(n - 32) div 64 = n div 64" using sub_div_eq[of 32 n] hhi nge by simp
  have es: "unat (word_of_nat n - (0x20::16 word)) = n - 32" using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have emi: "n div 64 mod 65536 = n div 64" using ndlt by simp
  have emo: "(n div 64 + 4) mod 65536 = n div 64 + 4" using ndlt by simp
  have ec: "4 + n div 64 = n div 64 + 4" by simp
  have sh: "unat ((0x100::16 word) >> 2) = 64" "unat ((0x80::16 word) >> 2) = 32"
           "unat ((1::16 word) << 2) = 4" "((0x80::16 word) >> 2) = 0x20" by eval+
  show ?thesis using hhi n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 hhi ndlt e3b es sh emi emo ec)
    done
qed

lemma mlevel2_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 2 a) n
       = (if n mod 64 < 32
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 64 + 4)) * sext64 (nth_seq a (n + 32)))
          else nth_seq a (n - 32) - montgomery_reduce (sext64 (nth_seq zetas (n div 64 + 4)) * sext64 (nth_seq a n)))"
  using mlevel2_lo[OF _ n] mlevel2_hi[OF _ n] by simp

lemma mlevel3_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 32 < 16" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 3 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 32 + 8)) * sext64 (nth_seq a (n + 16)))"
proof -
  have ndlt: "n div 32 < 8" using n2 by linarith
  have np: "n + 16 < 256" using hlo ndlt div_mult_mod_eq[of n 32] by linarith
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "(n + 16) mod 65536 = n + 16" using np by simp
  have emi: "n div 32 mod 65536 = n div 32" using ndlt by simp
  have emo: "(n div 32 + 8) mod 65536 = n div 32 + 8" using ndlt by simp
  have ec: "8 + n div 32 = n div 32 + 8" by simp
  have sh: "unat ((0x100::16 word) >> 3) = 32" "unat ((0x80::16 word) >> 3) = 16"
           "unat ((1::16 word) << 3) = 8" "((0x80::16 word) >> 3) = 0x10" by eval+
  show ?thesis using hlo n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 e2 hlo ndlt sh emi emo ec)
    done
qed

lemma mlevel3_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 32 < 16" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 3 a) n
       = nth_seq a (n - 16) - montgomery_reduce (sext64 (nth_seq zetas (n div 32 + 8)) * sext64 (nth_seq a n))"
proof -
  have nge: "16 \<le> n" using hhi by (cases "n < 16") auto
  have e1: "n mod 65536 = n" using n2 by simp
  have ndlt: "n div 32 < 8" using n2 by linarith
  have e3b: "(n - 16) div 32 = n div 32" using sub_div_eq[of 16 n] hhi nge by simp
  have es: "unat (word_of_nat n - (0x10::16 word)) = n - 16" using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have emi: "n div 32 mod 65536 = n div 32" using ndlt by simp
  have emo: "(n div 32 + 8) mod 65536 = n div 32 + 8" using ndlt by simp
  have ec: "8 + n div 32 = n div 32 + 8" by simp
  have sh: "unat ((0x100::16 word) >> 3) = 32" "unat ((0x80::16 word) >> 3) = 16"
           "unat ((1::16 word) << 3) = 8" "((0x80::16 word) >> 3) = 0x10" by eval+
  show ?thesis using hhi n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 hhi ndlt e3b es sh emi emo ec)
    done
qed

lemma mlevel3_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 3 a) n
       = (if n mod 32 < 16
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 32 + 8)) * sext64 (nth_seq a (n + 16)))
          else nth_seq a (n - 16) - montgomery_reduce (sext64 (nth_seq zetas (n div 32 + 8)) * sext64 (nth_seq a n)))"
  using mlevel3_lo[OF _ n] mlevel3_hi[OF _ n] by simp

lemma mlevel4_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 16 < 8" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 4 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 16 + 16)) * sext64 (nth_seq a (n + 8)))"
proof -
  have ndlt: "n div 16 < 16" using n2 by linarith
  have np: "n + 8 < 256" using hlo ndlt div_mult_mod_eq[of n 16] by linarith
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "(n + 8) mod 65536 = n + 8" using np by simp
  have emi: "n div 16 mod 65536 = n div 16" using ndlt by simp
  have emo: "(n div 16 + 16) mod 65536 = n div 16 + 16" using ndlt by simp
  have ec: "16 + n div 16 = n div 16 + 16" by simp
  have sh: "unat ((0x100::16 word) >> 4) = 16" "unat ((0x80::16 word) >> 4) = 8"
           "unat ((1::16 word) << 4) = 16" "((0x80::16 word) >> 4) = 0x8" by eval+
  show ?thesis using hlo n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 e2 hlo ndlt sh emi emo ec)
    done
qed

lemma mlevel4_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 16 < 8" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 4 a) n
       = nth_seq a (n - 8) - montgomery_reduce (sext64 (nth_seq zetas (n div 16 + 16)) * sext64 (nth_seq a n))"
proof -
  have nge: "8 \<le> n" using hhi by (cases "n < 8") auto
  have e1: "n mod 65536 = n" using n2 by simp
  have ndlt: "n div 16 < 16" using n2 by linarith
  have e3b: "(n - 8) div 16 = n div 16" using sub_div_eq[of 8 n] hhi nge by simp
  have es: "unat (word_of_nat n - (0x8::16 word)) = n - 8" using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have emi: "n div 16 mod 65536 = n div 16" using ndlt by simp
  have emo: "(n div 16 + 16) mod 65536 = n div 16 + 16" using ndlt by simp
  have ec: "16 + n div 16 = n div 16 + 16" by simp
  have sh: "unat ((0x100::16 word) >> 4) = 16" "unat ((0x80::16 word) >> 4) = 8"
           "unat ((1::16 word) << 4) = 16" "((0x80::16 word) >> 4) = 0x8" by eval+
  show ?thesis using hhi n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 hhi ndlt e3b es sh emi emo ec)
    done
qed

lemma mlevel4_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 4 a) n
       = (if n mod 16 < 8
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 16 + 16)) * sext64 (nth_seq a (n + 8)))
          else nth_seq a (n - 8) - montgomery_reduce (sext64 (nth_seq zetas (n div 16 + 16)) * sext64 (nth_seq a n)))"
  using mlevel4_lo[OF _ n] mlevel4_hi[OF _ n] by simp

lemma mlevel5_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 8 < 4" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 5 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 8 + 32)) * sext64 (nth_seq a (n + 4)))"
proof -
  have ndlt: "n div 8 < 32" using n2 by linarith
  have np: "n + 4 < 256" using hlo ndlt div_mult_mod_eq[of n 8] by linarith
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "(n + 4) mod 65536 = n + 4" using np by simp
  have emi: "n div 8 mod 65536 = n div 8" using ndlt by simp
  have emo: "(n div 8 + 32) mod 65536 = n div 8 + 32" using ndlt by simp
  have ec: "32 + n div 8 = n div 8 + 32" by simp
  have sh: "unat ((0x100::16 word) >> 5) = 8" "unat ((0x80::16 word) >> 5) = 4"
           "unat ((1::16 word) << 5) = 32" "((0x80::16 word) >> 5) = 0x4" by eval+
  show ?thesis using hlo n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 e2 hlo ndlt sh emi emo ec)
    done
qed

lemma mlevel5_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 8 < 4" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 5 a) n
       = nth_seq a (n - 4) - montgomery_reduce (sext64 (nth_seq zetas (n div 8 + 32)) * sext64 (nth_seq a n))"
proof -
  have nge: "4 \<le> n" using hhi by (cases "n < 4") auto
  have e1: "n mod 65536 = n" using n2 by simp
  have ndlt: "n div 8 < 32" using n2 by linarith
  have e3b: "(n - 4) div 8 = n div 8" using sub_div_eq[of 4 n] hhi nge by simp
  have es: "unat (word_of_nat n - (0x4::16 word)) = n - 4" using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have emi: "n div 8 mod 65536 = n div 8" using ndlt by simp
  have emo: "(n div 8 + 32) mod 65536 = n div 8 + 32" using ndlt by simp
  have ec: "32 + n div 8 = n div 8 + 32" by simp
  have sh: "unat ((0x100::16 word) >> 5) = 8" "unat ((0x80::16 word) >> 5) = 4"
           "unat ((1::16 word) << 5) = 32" "((0x80::16 word) >> 5) = 0x4" by eval+
  show ?thesis using hhi n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 hhi ndlt e3b es sh emi emo ec)
    done
qed

lemma mlevel5_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 5 a) n
       = (if n mod 8 < 4
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 8 + 32)) * sext64 (nth_seq a (n + 4)))
          else nth_seq a (n - 4) - montgomery_reduce (sext64 (nth_seq zetas (n div 8 + 32)) * sext64 (nth_seq a n)))"
  using mlevel5_lo[OF _ n] mlevel5_hi[OF _ n] by simp

lemma mlevel6_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 4 < 2" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 6 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 4 + 64)) * sext64 (nth_seq a (n + 2)))"
proof -
  have ndlt: "n div 4 < 64" using n2 by linarith
  have np: "n + 2 < 256" using hlo ndlt div_mult_mod_eq[of n 4] by linarith
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "(Suc (Suc n)) mod 65536 = Suc (Suc n)" using np by simp
  have emi: "n div 4 mod 65536 = n div 4" using ndlt by simp
  have emo: "(n div 4 + 64) mod 65536 = n div 4 + 64" using ndlt by simp
  have ec: "64 + n div 4 = n div 4 + 64" by simp
  have sh: "unat ((0x100::16 word) >> 6) = 4" "unat ((0x80::16 word) >> 6) = 2"
           "unat ((1::16 word) << 6) = 64" "((0x80::16 word) >> 6) = 0x2" by eval+
  show ?thesis using hlo n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 e2 hlo ndlt sh emi emo ec)
    done
qed

lemma mlevel6_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 4 < 2" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 6 a) n
       = nth_seq a (n - 2) - montgomery_reduce (sext64 (nth_seq zetas (n div 4 + 64)) * sext64 (nth_seq a n))"
proof -
  have nge: "2 \<le> n" using hhi by (cases "n < 2") auto
  have e1: "n mod 65536 = n" using n2 by simp
  have ndlt: "n div 4 < 64" using n2 by linarith
  have e3b: "(n - 2) div 4 = n div 4" using sub_div_eq[of 2 n] hhi nge by simp
  have es: "unat (word_of_nat n - (0x2::16 word)) = n - 2" using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have emi: "n div 4 mod 65536 = n div 4" using ndlt by simp
  have emo: "(n div 4 + 64) mod 65536 = n div 4 + 64" using ndlt by simp
  have ec: "64 + n div 4 = n div 4 + 64" by simp
  have sh: "unat ((0x100::16 word) >> 6) = 4" "unat ((0x80::16 word) >> 6) = 2"
           "unat ((1::16 word) << 6) = 64" "((0x80::16 word) >> 6) = 0x2" by eval+
  show ?thesis using hhi n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 hhi ndlt e3b es sh emi emo ec)
    done
qed

lemma mlevel6_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 6 a) n
       = (if n mod 4 < 2
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 4 + 64)) * sext64 (nth_seq a (n + 2)))
          else nth_seq a (n - 2) - montgomery_reduce (sext64 (nth_seq zetas (n div 4 + 64)) * sext64 (nth_seq a n)))"
  using mlevel6_lo[OF _ n] mlevel6_hi[OF _ n] by simp

lemma mlevel7_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 2 < 1" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 7 a) n
       = nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 2 + 128)) * sext64 (nth_seq a (n + 1)))"
proof -
  have ndlt: "n div 2 < 128" using n2 by linarith
  have np: "n + 1 < 256" using hlo ndlt div_mult_mod_eq[of n 2] by linarith
  have e1: "n mod 65536 = n" using n2 by simp
  have e2: "(Suc n) mod 65536 = Suc n" using np by simp
  have emi: "n div 2 mod 65536 = n div 2" using ndlt by simp
  have emo: "(n div 2 + 128) mod 65536 = n div 2 + 128" using ndlt by simp
  have ec: "128 + n div 2 = n div 2 + 128" by simp
  have hlo0: "n mod 2 = 0" using hlo by simp
  have wc: "(word_of_nat n mod (2::16 word) = 0) = (n mod 2 = 0)"
    by (simp add: unat_arith_simps unat_of_nat mod_mod_cancel)
  have wc1: "(word_of_nat n mod (2::16 word) = 1) = (n mod 2 = 1)"
    by (simp add: unat_arith_simps unat_of_nat mod_mod_cancel)
  have sh: "unat ((0x100::16 word) >> 7) = 2" "unat ((0x80::16 word) >> 7) = 1"
           "unat ((1::16 word) << 7) = 128" "((0x80::16 word) >> 7) = 0x1"
           "((0x100::16 word) >> 7) = 2" by eval+
  show ?thesis using hlo n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 e2 hlo ndlt sh emi emo ec wc wc1 hlo0)
    done
qed

lemma mlevel7_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 2 < 1" and n2: "n < (256::nat)"
  shows "nth_seq (nttLevel 7 a) n
       = nth_seq a (n - 1) - montgomery_reduce (sext64 (nth_seq zetas (n div 2 + 128)) * sext64 (nth_seq a n))"
proof -
  have nge: "1 \<le> n" using hhi by (cases "n < 1") auto
  have e1: "n mod 65536 = n" using n2 by simp
  have ndlt: "n div 2 < 128" using n2 by linarith
  have e3b: "(n - Suc 0) div 2 = n div 2" using sub_div_eq[of 1 n] hhi nge by simp
  have es: "unat (word_of_nat n - (0x1::16 word)) = n - Suc 0" using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have emi: "n div 2 mod 65536 = n div 2" using ndlt by simp
  have emo: "(n div 2 + 128) mod 65536 = n div 2 + 128" using ndlt by simp
  have ec: "128 + n div 2 = n div 2 + 128" by simp
  have hhi1: "n mod 2 = 1" using hhi by (simp add: not_mod_2_eq_0_eq_1)
  have wc: "(word_of_nat n mod (2::16 word) = 0) = (n mod 2 = 0)"
    by (simp add: unat_arith_simps unat_of_nat mod_mod_cancel)
  have wc1: "(word_of_nat n mod (2::16 word) = 1) = (n mod 2 = 1)"
    by (simp add: unat_arith_simps unat_of_nat mod_mod_cancel)
  have sh: "unat ((0x100::16 word) >> 7) = 2" "unat ((0x80::16 word) >> 7) = 1"
           "unat ((1::16 word) << 7) = 128" "((0x80::16 word) >> 7) = 0x1"
           "((0x100::16 word) >> 7) = 2" by eval+
  show ?thesis using hhi n2
    apply (simp add: nttLevel_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat e1 hhi ndlt e3b es sh emi emo ec wc wc1 hhi1)
    done
qed

lemma mlevel7_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (nttLevel 7 a) n
       = (if n mod 2 < 1
          then nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas (n div 2 + 128)) * sext64 (nth_seq a (n + 1)))
          else nth_seq a (n - 1) - montgomery_reduce (sext64 (nth_seq zetas (n div 2 + 128)) * sext64 (nth_seq a n)))"
  using mlevel7_lo[OF _ n] mlevel7_hi[OF _ n] by simp


text \<open>Signed int-coefficient view of the montgomery model (cf. \<open>cf\<close> for the normal model).\<close>
definition sf :: "[256][32] \<Rightarrow> nat \<Rightarrow> int" where
  "sf a n = sint_seq (nth_seq a n)"

text \<open>The abstract CT layer respects pointwise mod-q congruence of its coefficient function.\<close>
lemma bflyLayer_cong_g:
  fixes g g' :: "nat \<Rightarrow> int"
  assumes "\<And>m. g m mod 8380417 = g' m mod 8380417"
  shows "bflyLayer L M0 g n mod 8380417 = bflyLayer L M0 g' n mod 8380417"
proof -
  have add: "(g n + zt i * g (n + L) mod 8380417) mod 8380417
           = (g' n + zt i * g' (n + L) mod 8380417) mod 8380417" for i
  proof -
    have "(g n + zt i * g (n + L) mod 8380417) mod 8380417 = (g n + zt i * g (n + L)) mod 8380417"
      by (simp add: mod_add_right_eq)
    also have "\<dots> = (g' n + zt i * g' (n + L)) mod 8380417"
      by (rule mod_add_cong[OF assms mod_mult_cong[OF refl assms]])
    also have "\<dots> = (g' n + zt i * g' (n + L) mod 8380417) mod 8380417"
      by (simp add: mod_add_right_eq)
    finally show ?thesis .
  qed
  have sub: "(g (n - L) + 8380417 - zt i * g n mod 8380417) mod 8380417
           = (g' (n - L) + 8380417 - zt i * g' n mod 8380417) mod 8380417" for i
  proof -
    have "(g (n - L) + 8380417 - zt i * g n mod 8380417) mod 8380417
        = (g (n - L) + 8380417 - zt i * g n) mod 8380417"
      by (simp add: mod_diff_right_eq)
    also have "\<dots> = (g' (n - L) + 8380417 - zt i * g' n) mod 8380417"
      by (rule mod_diff_cong[OF mod_add_cong[OF assms refl] mod_mult_cong[OF refl assms]])
    also have "\<dots> = (g' (n - L) + 8380417 - zt i * g' n mod 8380417) mod 8380417"
      by (simp add: mod_diff_right_eq)
    finally show ?thesis .
  qed
  show ?thesis unfolding bflyLayer_def using add sub by simp
qed

text \<open>Brick (d), part 2 (level 0): the montgomery model's signed output coefficient at position
  \<open>n\<close> is congruent mod q to one abstract CT butterfly layer on the montgomery sint-view. This
  composes the level-0 unfold, the per-butterfly value congruence (\<open>butterfly_cong\<close>), the
  no-overflow lifts, and the normal-model twiddle table (\<open>zt\<close>). Validates the full per-layer
  method end to end; the remaining 7 levels and the foldl induction follow the same shape.\<close>
lemma mbfly0:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 2139103230" and n: "n < 256"
  shows "sf (nttLevel 0 a) n mod 8380417 = bflyLayer 128 0 (sf a) n mod 8380417"
proof (cases "n < 128")
  case True
  have aP: "- B \<le> sint_seq (nth_seq a n)" "sint_seq (nth_seq a n) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have aR: "- B \<le> sint_seq (nth_seq a (n + 128))" "sint_seq (nth_seq a (n + 128)) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have zQ: "- 4194304 \<le> sint_seq (nth_seq zetas 1)" "sint_seq (nth_seq zetas 1) \<le> 4194304"
    using Assay_Equivalence.zeta_bound by auto
  have ok: "mont_input_ok (sint_seq (nth_seq zetas 1) * sint_seq (nth_seq a (n + 128)))"
    by (rule mont_input_ok_of_bounds[OF zQ(1) zQ(2) aR(1) aR(2) Bhi])
  have mb: "- 8380417 < sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128))))"
           "sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128)))) < 8380417"
    using mont_butterfly_bound[OF ok] by simp_all
  have noov: "sint_seq (nth_seq a n + montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128))))
            = sint_seq (nth_seq a n) + sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128))))"
    by (rule sint_seq_add_eq) (use aP mb Bhi in linarith)+
  have i1: "(0::nat) < 1" "(1::nat) < 256" by simp_all
  have bc: "sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128)))) mod 8380417
          = (uint_seq (nth_seq zetabrv 1) * sint_seq (nth_seq a (n + 128))) mod 8380417"
    using butterfly_cong[OF i1(1) i1(2) ok] by simp
  have lhs: "sf (nttLevel 0 a) n mod 8380417
           = (sint_seq (nth_seq a n)
              + sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a (n + 128))))) mod 8380417"
    using True mlevel0_coeff[OF n] noov by (simp add: sf_def)
  also have "\<dots> = (sint_seq (nth_seq a n)
                  + uint_seq (nth_seq zetabrv 1) * sint_seq (nth_seq a (n + 128))) mod 8380417"
    by (rule mod_add_cong[OF refl bc])
  finally have L: "sf (nttLevel 0 a) n mod 8380417 = (sf a n + zt 1 * sf a (n + 128)) mod 8380417"
    by (simp add: sf_def zt_def)
  have e2: "n mod 256 = n" using n by simp
  have e3: "n div 256 = 0" using n by simp
  have R: "bflyLayer 128 0 (sf a) n mod 8380417 = (sf a n + zt 1 * sf a (n + 128)) mod 8380417"
    using True e2 e3 by (simp add: bflyLayer_def mod_add_right_eq)
  show ?thesis using L R by simp
next
  case False
  hence ge: "128 \<le> n" by simp
  have nm: "n - 128 < 256" using n by simp
  have aP: "- B \<le> sint_seq (nth_seq a (n - 128))" "sint_seq (nth_seq a (n - 128)) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have aR: "- B \<le> sint_seq (nth_seq a n)" "sint_seq (nth_seq a n) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have zQ: "- 4194304 \<le> sint_seq (nth_seq zetas 1)" "sint_seq (nth_seq zetas 1) \<le> 4194304"
    using Assay_Equivalence.zeta_bound by auto
  have ok: "mont_input_ok (sint_seq (nth_seq zetas 1) * sint_seq (nth_seq a n))"
    by (rule mont_input_ok_of_bounds[OF zQ(1) zQ(2) aR(1) aR(2) Bhi])
  have mb: "- 8380417 < sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n)))"
           "sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n))) < 8380417"
    using mont_butterfly_bound[OF ok] by simp_all
  have noov: "sint_seq (nth_seq a (n - 128) - montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n)))
            = sint_seq (nth_seq a (n - 128)) - sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n)))"
    by (rule sint_seq_sub_eq) (use aP mb Bhi in linarith)+
  have i1: "(0::nat) < 1" "(1::nat) < 256" by simp_all
  have bc: "sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n))) mod 8380417
          = (uint_seq (nth_seq zetabrv 1) * sint_seq (nth_seq a n)) mod 8380417"
    using butterfly_cong[OF i1(1) i1(2) ok] by simp
  have lhs: "sf (nttLevel 0 a) n mod 8380417
           = (sf a (n - 128)
              - sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n)))) mod 8380417"
    using False mlevel0_coeff[OF n] noov by (simp add: sf_def)
  have key: "(sf a (n - 128) - sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n)))) mod 8380417
           = (sf a (n - 128) - zt 1 * sf a n) mod 8380417"
  proof -
    have "(sf a (n - 128) - sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n)))) mod 8380417
        = (sf a (n - 128) - sint_seq (montgomery_reduce (sext64 (nth_seq zetas 1) * sext64 (nth_seq a n))) mod 8380417) mod 8380417"
      by (simp add: mod_diff_right_eq)
    also have "\<dots> = (sf a (n - 128) - (uint_seq (nth_seq zetabrv 1) * sint_seq (nth_seq a n)) mod 8380417) mod 8380417"
      using bc by simp
    also have "\<dots> = (sf a (n - 128) - zt 1 * sf a n) mod 8380417"
      by (simp add: sf_def zt_def mod_diff_right_eq)
    finally show ?thesis .
  qed
  have e2: "n mod 256 = n" using n by simp
  have e3: "n div 256 = 0" using n by simp
  have R: "bflyLayer 128 0 (sf a) n mod 8380417 = (sf a (n - 128) + 8380417 - zt 1 * sf a n) mod 8380417"
    using False e2 e3 by (simp add: bflyLayer_def mod_diff_right_eq)
  have rearr: "sf a (n - 128) + 8380417 - zt 1 * sf a n
             = sf a (n - 128) - zt 1 * sf a n + 8380417" by simp
  have R2: "(sf a (n - 128) + 8380417 - zt 1 * sf a n) mod 8380417
          = (sf a (n - 128) - zt 1 * sf a n) mod 8380417"
    unfolding rearr by (rule mod_add_self2)
  have "sf (nttLevel 0 a) n mod 8380417 = (sf a (n - 128) - zt 1 * sf a n) mod 8380417"
    using lhs key by simp
  also have "\<dots> = (sf a (n - 128) + 8380417 - zt 1 * sf a n) mod 8380417"
    using R2 by simp
  also have "\<dots> = bflyLayer 128 0 (sf a) n mod 8380417"
    using R by simp
  finally show ?thesis .
qed

end

end
