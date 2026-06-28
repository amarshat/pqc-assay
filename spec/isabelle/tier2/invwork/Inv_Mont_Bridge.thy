(* Tier-2 inverse model bridge (fork 1, piece 4, sub-step 2).

   Goal: connect the SAW-checked montgomery inverse NTT model
   (Assay.MLDSA_NTT.invntt, the function SAW proves the PQClean C invntt_tomont
   equal to under -fwrapv) to the Tier-2 normal-domain inverse nttInvAllRef, mod q,
   plus the final invf = mont^2/256 scale that folds in the 256^-1 normalization.

   This is the Gentleman-Sande mirror of the forward Mont_Bridge: where the forward
   relates the montgomery `ntt` to `nttFwdAllRef`, the inverse relates the montgomery
   `invntt` to `nttInvAllRef`. It reuses the forward foundation directly
   (butterfly_cong / mont_mod_q / zeta_rel / sint_sext64_mult / sint_seq_sub_eq).

   This file lives in the thin child session Tier2_InvWork (on the forward Tier2
   heap) so the inverse work iterates without reproving the forward chain.

   STATUS: foundation bricks proven (this commit). The 8 GS layer unfolds, the
   per-layer congruences, the range preservation, and the compose into the
   invntt_bridge theorem are the remaining work. *)
theory Inv_Mont_Bridge
  imports "Tier2.Mont_Bridge"
begin

section \<open>Inverse-specific foundation\<close>

text \<open>The Gentleman-Sande high leg multiplies by the NEGATED twiddle
  \<open>zeta = -zetas[i]\<close> (the C walks the table in reverse and negates: the running
  counter does \<open>zeta = -zetas[--k]\<close>). Two new bricks beyond the forward foundation:
  (1) the int32 negation of a small word is exact on the sint view, and (2) the
  butterfly congruence carries the sign through. The final-scale congruence for
  \<open>invf\<close> is the forward montgomery congruence with the constant in place of a
  twiddle (no table lookup, so no \<open>zeta_rel\<close>).\<close>

text \<open>\<open>sint\<close> of the int32 zero word.\<close>
lemma sint_seq_zero: "sint_seq (0 :: (32, bool) seq) = 0"
  by (simp add: probe_sint_seq word_seq_convs seq_to_word)

text \<open>Negation of a word strictly inside int32 range is exact on the signed view
  (it cannot hit the asymmetric \<open>-2^31\<close> endpoint). Used for \<open>-zetas[i]\<close>, which is
  bounded by \<open>2^22\<close>.\<close>
lemma sint_seq_uminus_small:
  fixes z :: "(32, bool) seq"
  assumes lo: "- 2147483648 < sint_seq z" and hi: "sint_seq z < 2147483648"
  shows "sint_seq (- z) = - sint_seq z"
proof -
  have "(- z :: (32, bool) seq) = 0 - z" by simp
  hence "sint_seq (- z) = sint_seq (0 - z)" by simp
  also have "\<dots> = sint_seq (0 :: (32, bool) seq) - sint_seq z"
    by (rule sint_seq_sub_eq) (use lo hi sint_seq_zero in linarith)+
  also have "\<dots> = - sint_seq z" by (simp add: sint_seq_zero)
  finally show ?thesis .
qed

text \<open>Cancel the montgomery factor \<open>2^32\<close> (coprime to the prime \<open>q\<close>) from a mod-q
  equation. Proven over abstract integers, where both products are sign- and sum-free,
  so \<open>cong_mult_lcancel\<close> matches cleanly; applied later by resolution so the canonical
  \<open>- (c * x)\<close> form of a negated argument at the call site does not block the match.\<close>
lemma mont32_cancel:
  fixes x y :: int
  assumes "(4294967296 * x) mod 8380417 = (4294967296 * y) mod 8380417"
  shows "x mod 8380417 = y mod 8380417"
proof -
  have cop: "coprime (4294967296::int) 8380417"
  proof -
    have "gcd (4294967296::int) 8380417 = 1" by eval
    thus ?thesis by (simp add: coprime_iff_gcd_eq_1)
  qed
  from assms have "[4294967296 * x = 4294967296 * y] (mod 8380417)" by (simp add: cong_def)
  hence "[x = y] (mod 8380417)" using cop by (simp add: cong_mult_lcancel)
  thus ?thesis by (simp add: cong_def)
qed

text \<open>The inverse (Gentleman-Sande) per-butterfly congruence: the montgomery term
  computed with the negated twiddle \<open>-zetas[i]\<close> applied to a difference \<open>d\<close> is
  congruent mod q to the normal-domain product \<open>(-zetabrv[i]) \<cdot> d\<close>. Mirrors
  \<open>butterfly_cong\<close> (combine \<open>mont_mod_q\<close> with \<open>zeta_rel\<close>, cancel the montgomery factor
  \<open>2^32\<close>), tracking the sign through the negated twiddle.\<close>
lemma inv_butterfly_cong:
  fixes d :: "(32, bool) seq"
  assumes i0: "0 < i" and i: "i < 256"
      and ok: "mont_input_ok (- sint_seq (nth_seq zetas i) * sint_seq d)"
  shows "sint_seq (montgomery_reduce (sext64 (- nth_seq zetas i) * sext64 d)) mod 8380417
       = (- uint_seq (nth_seq zetabrv i) * sint_seq d) mod 8380417"
proof -
  define z  where "z  = nth_seq zetas i"
  define zb where "zb = uint_seq (nth_seq zetabrv i)"
  define sd where "sd = sint_seq d"
  define mr where "mr = sint_seq (montgomery_reduce (sext64 (- z) * sext64 d))"
  \<comment> \<open>goal: \<open>mr mod 8380417 = (- zb * sd) mod 8380417\<close>\<close>
  have zlo: "- 2147483648 < sint_seq z" and zhi: "sint_seq z < 2147483648"
    using zeta_bound[of i] by (simp_all add: z_def)
  have nz: "sint_seq (- z) = - sint_seq z"
    by (rule sint_seq_uminus_small[OF zlo zhi])
  have val: "sint_seq (sext64 (- z) * sext64 d) = - sint_seq z * sd"
    by (simp add: sint_sext64_mult nz sd_def)
  have ok2: "mont_input_ok (sint_seq (sext64 (- z) * sext64 d))"
    unfolding val using ok by (simp add: z_def sd_def)
  have b: "(4294967296 * mr) mod 8380417 = (- sint_seq z * sd) mod 8380417"
    using mont_mod_q[OF ok2] by (simp add: mr_def val)
  have zr: "sint_seq z mod 8380417 = (4294967296 * zb) mod 8380417"
    using zeta_rel[OF i0 i] by (simp add: z_def zb_def)
  have e: "(- sint_seq z * sd) mod 8380417 = (4294967296 * (- zb * sd)) mod 8380417"
  proof -
    have zr_c: "[sint_seq z = 4294967296 * zb] (mod 8380417)" using zr by (simp add: cong_def)
    have "[(- sd) * sint_seq z = (- sd) * (4294967296 * zb)] (mod 8380417)"
      by (rule cong_mult[OF cong_refl zr_c])
    hence "[- sint_seq z * sd = 4294967296 * (- zb * sd)] (mod 8380417)"
      by (simp add: algebra_simps)
    thus ?thesis by (simp add: cong_def)
  qed
  \<comment> \<open>cancel the montgomery factor \<open>2^32\<close> via the abstract helper (applied by resolution,
     so the negative right-hand side is fine: no \<open>simp\<close> runs at this call site).\<close>
  have comb: "(4294967296 * mr) mod 8380417 = (4294967296 * (- (zb * sd))) mod 8380417"
    using b e by simp
  have "mr mod 8380417 = (- (zb * sd)) mod 8380417"
    by (rule mont32_cancel[OF comb])
  thus "mr mod 8380417 = (- uint_seq (nth_seq zetabrv i) * sint_seq d) mod 8380417"
    by (simp add: zb_def sd_def)
qed

text \<open>The final-scale congruence: the montgomery factor times the scaled output is
  congruent to \<open>invf \<cdot> b\<close> mod q. This is the first conjunct of
  \<open>is_montgomery_reduction\<close> for the constant multiplier \<open>invf = 41978 = mont^2/256\<close>;
  combined with the per-layer bridge it yields the \<open>2^{-32}\<cdot>invf = mont/256\<close>
  normal-domain scaling of the inverse transform.\<close>
lemma invf_scale_cong:
  fixes b :: "(32, bool) seq"
  assumes ok: "mont_input_ok (sint_seq invf * sint_seq b)"
  shows "(4294967296 * sint_seq (montgomery_reduce (sext64 invf * sext64 b))) mod 8380417
       = (sint_seq invf * sint_seq b) mod 8380417"
proof -
  have ok2: "mont_input_ok (sint_seq (sext64 invf * sext64 b))"
    using ok by (simp add: sint_sext64_mult)
  show ?thesis
    using mont_mod_q[OF ok2] by (simp add: sint_sext64_mult)
qed

section \<open>Gentleman-Sande layer unfolds\<close>

text \<open>Per-position unfold of the montgomery inverse layers, mirroring Mont_Bridge's
  \<open>mlevel\<close> unfolds. The cryptol-notation context is needed for the \<open>[256][32]\<close> types;
  coercion is disabled so the nat/int index arithmetic goes through \<open>linarith\<close>. Inverse
  butterfly: low leg \<open>a[m] + a[m+len]\<close> (plain int32 add, no reduce), high leg
  \<open>montgomery_reduce(zeta * (a[m-len] - a[m]))\<close>, \<open>zeta = -zetas[(256>>ell)-1-(m div twolen)]\<close>.
  Level \<open>ell\<close> has \<open>len = 2^ell\<close> (the reverse of the forward layer order).\<close>

context includes cryptol_syntax begin

declare [[coercion_enabled = false]]

text \<open>Level 0 (\<open>len = 1\<close>, \<open>twolen = 2\<close>, \<open>kbase = 256\<close>): even positions are low legs.\<close>
lemma invlevel0_lo:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)" and ev: "n mod 2 = 0"
  shows "nth_seq (invnttLevel 0 a) n = nth_seq a n + nth_seq a (n + 1)"
proof -
  have n256: "n < 256" using n by simp
  have e1: "n mod 65536 = n" using n by simp
  have e2: "Suc n mod 65536 = Suc n" using n by simp
  have sh: "unat ((1::16 word) << 1) = 2" "((1::16 word) << 1) = 2"
           "unat ((1::16 word) << 0) = 1" "((1::16 word) << 0) = 1"
           "((0x100::16 word) >> 0) = 0x100" by eval+
  have wm: "(word_of_nat n :: 16 word) mod 2 = 0"
  proof -
    have "unat ((word_of_nat n :: 16 word) mod 2) = 0" using ev e1 by (simp add: unat_mod unat_of_nat)
    thus ?thesis by (simp add: unat_eq_zero)
  qed
  show ?thesis
    using n ev
    apply (simp add: invnttLevel_def fromTo_def Let_def n256)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 ev sh wm)
    done
qed

text \<open>Odd positions are high legs: \<open>montgomery_reduce(-zetas[255 - n div 2] * (a[n-1] - a[n]))\<close>.\<close>
lemma invlevel0_hi:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)" and oddn: "n mod 2 = 1"
  shows "nth_seq (invnttLevel 0 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (255 - n div 2)) * sext64 (nth_seq a (n - 1) - nth_seq a n))"
proof -
  have n256: "n < 256" using n by simp
  have e1: "n mod 65536 = n" using n by simp
  have nge1: "1 \<le> n" using oddn by (cases "n = 0") auto
  have ndv: "n div 2 < 128" using n by linarith
  have sh: "unat ((1::16 word) << 1) = 2" "((1::16 word) << 1) = 2"
           "unat ((1::16 word) << 0) = 1" "((1::16 word) << 0) = 1"
           "((0x100::16 word) >> 0) = 0x100" by eval+
  have wm: "(word_of_nat n :: 16 word) mod 2 = 1"
  proof -
    have "unat ((word_of_nat n :: 16 word) mod 2) = 1" using oddn e1 by (simp add: unat_mod unat_of_nat)
    thus ?thesis by (metis unat_1 word_unat.Rep_inject)
  qed
  have es: "unat (word_of_nat n - (1::16 word)) = n - 1"
    using nge1 by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 2 :: 16 word) \<le> 0xFF"
    using ndv by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0xFF::16 word) - word_of_nat n div 2) = 255 - n div 2"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  show ?thesis
    using n oddn
    apply (simp add: invnttLevel_def fromTo_def Let_def n256)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 oddn sh wm es ez)
    done
qed

lemma invlevel0_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 0 a) n
       = (if n mod 2 = 0
          then nth_seq a n + nth_seq a (n + 1)
          else montgomery_reduce (sext64 (- nth_seq zetas (255 - n div 2)) * sext64 (nth_seq a (n - 1) - nth_seq a n)))"
proof (cases "n mod 2 = 0")
  case True thus ?thesis using invlevel0_lo[OF n True] by simp
next
  case False hence "n mod 2 = 1" by simp
  thus ?thesis using invlevel0_hi[OF n] by simp
qed

text \<open>Level 1 (\<open>len = 2\<close>, \<open>twolen = 4\<close>, \<open>kbase = 128\<close>), twiddle \<open>-zetas[127 - n div 4]\<close>.\<close>
lemma invlevel1_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 4 < 2" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 1 a) n = nth_seq a n + nth_seq a (n + 2)"
proof -
  have dec: "4 * (n div 4) + n mod 4 = n" by simp
  have ndlt: "n div 4 < 64" using n by linarith
  have np: "n + 2 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n by simp
  have e2: "Suc (Suc n) mod 65536 = Suc (Suc n)" using np by simp
  have sh: "unat ((1::16 word) << 1) = 2" "((1::16 word) << 1) = 2"
           "unat ((2::16 word) << 1) = 4" "((2::16 word) << 1) = 4"
           "unat ((0x100::16 word) >> 1) = 128" "((0x100::16 word) >> 1) = 0x80" by eval+
  show ?thesis
    using hlo n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma invlevel1_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 4 < 2" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 1 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (127 - n div 4)) * sext64 (nth_seq a (n - 2) - nth_seq a n))"
proof -
  have nge: "2 \<le> n" using hhi by (cases "n < 2") auto
  have e1: "n mod 65536 = n" using n by simp
  have ndlt: "n div 4 < 64" using n by linarith
  have es: "unat (word_of_nat n - (2::16 word)) = n - 2"
    using nge by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 4 :: 16 word) \<le> 0x7F"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0x7F::16 word) - word_of_nat n div 4) = 127 - n div 4"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  have sh: "unat ((1::16 word) << 1) = 2" "((1::16 word) << 1) = 2"
           "unat ((2::16 word) << 1) = 4" "((2::16 word) << 1) = 4"
           "unat ((0x100::16 word) >> 1) = 128" "((0x100::16 word) >> 1) = 0x80" by eval+
  show ?thesis
    using hhi n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt es ez sh)
    done
qed

lemma invlevel1_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 1 a) n
       = (if n mod 4 < 2
          then nth_seq a n + nth_seq a (n + 2)
          else montgomery_reduce (sext64 (- nth_seq zetas (127 - n div 4)) * sext64 (nth_seq a (n - 2) - nth_seq a n)))"
  using invlevel1_lo[OF _ n] invlevel1_hi[OF _ n] by simp

text \<open>Level 2 (\<open>len = 4\<close>, \<open>twolen = 8\<close>, \<open>kbase = 64\<close>), twiddle \<open>-zetas[63 - n div 8]\<close>.\<close>
lemma invlevel2_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 8 < 4" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 2 a) n = nth_seq a n + nth_seq a (n + 4)"
proof -
  have dec: "8 * (n div 8) + n mod 8 = n" by simp
  have ndlt: "n div 8 < 32" using n by linarith
  have np: "n + 4 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n by simp
  have e2: "(n + 4) mod 65536 = n + 4" using np by simp
  have sh: "unat ((1::16 word) << 2) = 4" "((1::16 word) << 2) = 4"
           "unat ((4::16 word) << 1) = 8" "((4::16 word) << 1) = 8"
           "unat ((0x100::16 word) >> 2) = 64" "((0x100::16 word) >> 2) = 0x40" by eval+
  show ?thesis
    using hlo n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma invlevel2_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 8 < 4" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 2 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (63 - n div 8)) * sext64 (nth_seq a (n - 4) - nth_seq a n))"
proof -
  have nge: "4 \<le> n" using hhi by (cases "n < 4") auto
  have e1: "n mod 65536 = n" using n by simp
  have ndlt: "n div 8 < 32" using n by linarith
  have es: "unat (word_of_nat n - (4::16 word)) = n - 4"
    using nge by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 8 :: 16 word) \<le> 0x3F"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0x3F::16 word) - word_of_nat n div 8) = 63 - n div 8"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  have sh: "unat ((1::16 word) << 2) = 4" "((1::16 word) << 2) = 4"
           "unat ((4::16 word) << 1) = 8" "((4::16 word) << 1) = 8"
           "unat ((0x100::16 word) >> 2) = 64" "((0x100::16 word) >> 2) = 0x40" by eval+
  show ?thesis
    using hhi n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt es ez sh)
    done
qed

lemma invlevel2_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 2 a) n
       = (if n mod 8 < 4
          then nth_seq a n + nth_seq a (n + 4)
          else montgomery_reduce (sext64 (- nth_seq zetas (63 - n div 8)) * sext64 (nth_seq a (n - 4) - nth_seq a n)))"
  using invlevel2_lo[OF _ n] invlevel2_hi[OF _ n] by simp

text \<open>Level 3 (\<open>len = 8\<close>, \<open>twolen = 16\<close>, \<open>kbase = 32\<close>), twiddle \<open>-zetas[31 - n div 16]\<close>.\<close>
lemma invlevel3_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 16 < 8" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 3 a) n = nth_seq a n + nth_seq a (n + 8)"
proof -
  have dec: "16 * (n div 16) + n mod 16 = n" by simp
  have ndlt: "n div 16 < 16" using n by linarith
  have np: "n + 8 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n by simp
  have e2: "(n + 8) mod 65536 = n + 8" using np by simp
  have sh: "unat ((1::16 word) << 3) = 8" "((1::16 word) << 3) = 8"
           "unat ((8::16 word) << 1) = 16" "((8::16 word) << 1) = 16"
           "unat ((0x100::16 word) >> 3) = 32" "((0x100::16 word) >> 3) = 0x20" by eval+
  show ?thesis
    using hlo n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma invlevel3_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 16 < 8" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 3 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (31 - n div 16)) * sext64 (nth_seq a (n - 8) - nth_seq a n))"
proof -
  have nge: "8 \<le> n" using hhi by (cases "n < 8") auto
  have e1: "n mod 65536 = n" using n by simp
  have ndlt: "n div 16 < 16" using n by linarith
  have es: "unat (word_of_nat n - (8::16 word)) = n - 8"
    using nge by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 16 :: 16 word) \<le> 0x1F"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0x1F::16 word) - word_of_nat n div 16) = 31 - n div 16"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  have sh: "unat ((1::16 word) << 3) = 8" "((1::16 word) << 3) = 8"
           "unat ((8::16 word) << 1) = 16" "((8::16 word) << 1) = 16"
           "unat ((0x100::16 word) >> 3) = 32" "((0x100::16 word) >> 3) = 0x20" by eval+
  show ?thesis
    using hhi n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt es ez sh)
    done
qed

lemma invlevel3_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 3 a) n
       = (if n mod 16 < 8
          then nth_seq a n + nth_seq a (n + 8)
          else montgomery_reduce (sext64 (- nth_seq zetas (31 - n div 16)) * sext64 (nth_seq a (n - 8) - nth_seq a n)))"
  using invlevel3_lo[OF _ n] invlevel3_hi[OF _ n] by simp

text \<open>Level 4 (\<open>len = 16\<close>, \<open>twolen = 32\<close>, \<open>kbase = 16\<close>), twiddle \<open>-zetas[15 - n div 32]\<close>.\<close>
lemma invlevel4_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 32 < 16" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 4 a) n = nth_seq a n + nth_seq a (n + 16)"
proof -
  have dec: "32 * (n div 32) + n mod 32 = n" by simp
  have ndlt: "n div 32 < 8" using n by linarith
  have np: "n + 16 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n by simp
  have e2: "(n + 16) mod 65536 = n + 16" using np by simp
  have sh: "unat ((1::16 word) << 4) = 16" "((1::16 word) << 4) = 16"
           "unat ((16::16 word) << 1) = 32" "((16::16 word) << 1) = 32"
           "unat ((0x100::16 word) >> 4) = 16" "((0x100::16 word) >> 4) = 0x10" by eval+
  show ?thesis
    using hlo n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma invlevel4_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 32 < 16" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 4 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (15 - n div 32)) * sext64 (nth_seq a (n - 16) - nth_seq a n))"
proof -
  have nge: "16 \<le> n" using hhi by (cases "n < 16") auto
  have e1: "n mod 65536 = n" using n by simp
  have ndlt: "n div 32 < 8" using n by linarith
  have es: "unat (word_of_nat n - (16::16 word)) = n - 16"
    using nge by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 32 :: 16 word) \<le> 0xF"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0xF::16 word) - word_of_nat n div 32) = 15 - n div 32"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  have sh: "unat ((1::16 word) << 4) = 16" "((1::16 word) << 4) = 16"
           "unat ((16::16 word) << 1) = 32" "((16::16 word) << 1) = 32"
           "unat ((0x100::16 word) >> 4) = 16" "((0x100::16 word) >> 4) = 0x10" by eval+
  show ?thesis
    using hhi n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt es ez sh)
    done
qed

lemma invlevel4_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 4 a) n
       = (if n mod 32 < 16
          then nth_seq a n + nth_seq a (n + 16)
          else montgomery_reduce (sext64 (- nth_seq zetas (15 - n div 32)) * sext64 (nth_seq a (n - 16) - nth_seq a n)))"
  using invlevel4_lo[OF _ n] invlevel4_hi[OF _ n] by simp

text \<open>Level 5 (\<open>len = 32\<close>, \<open>twolen = 64\<close>, \<open>kbase = 8\<close>), twiddle \<open>-zetas[7 - n div 64]\<close>.\<close>
lemma invlevel5_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 64 < 32" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 5 a) n = nth_seq a n + nth_seq a (n + 32)"
proof -
  have dec: "64 * (n div 64) + n mod 64 = n" by simp
  have ndlt: "n div 64 < 4" using n by linarith
  have np: "n + 32 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n by simp
  have e2: "(n + 32) mod 65536 = n + 32" using np by simp
  have sh: "unat ((1::16 word) << 5) = 32" "((1::16 word) << 5) = 32"
           "unat ((32::16 word) << 1) = 64" "((32::16 word) << 1) = 64"
           "unat ((0x100::16 word) >> 5) = 8" "((0x100::16 word) >> 5) = 0x8" by eval+
  show ?thesis
    using hlo n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma invlevel5_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 64 < 32" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 5 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (7 - n div 64)) * sext64 (nth_seq a (n - 32) - nth_seq a n))"
proof -
  have nge: "32 \<le> n" using hhi by (cases "n < 32") auto
  have e1: "n mod 65536 = n" using n by simp
  have ndlt: "n div 64 < 4" using n by linarith
  have es: "unat (word_of_nat n - (32::16 word)) = n - 32"
    using nge by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 64 :: 16 word) \<le> 0x7"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0x7::16 word) - word_of_nat n div 64) = 7 - n div 64"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  have sh: "unat ((1::16 word) << 5) = 32" "((1::16 word) << 5) = 32"
           "unat ((32::16 word) << 1) = 64" "((32::16 word) << 1) = 64"
           "unat ((0x100::16 word) >> 5) = 8" "((0x100::16 word) >> 5) = 0x8" by eval+
  show ?thesis
    using hhi n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt es ez sh)
    done
qed

lemma invlevel5_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 5 a) n
       = (if n mod 64 < 32
          then nth_seq a n + nth_seq a (n + 32)
          else montgomery_reduce (sext64 (- nth_seq zetas (7 - n div 64)) * sext64 (nth_seq a (n - 32) - nth_seq a n)))"
  using invlevel5_lo[OF _ n] invlevel5_hi[OF _ n] by simp

text \<open>Level 6 (\<open>len = 64\<close>, \<open>twolen = 128\<close>, \<open>kbase = 4\<close>), twiddle \<open>-zetas[3 - n div 128]\<close>.\<close>
lemma invlevel6_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 128 < 64" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 6 a) n = nth_seq a n + nth_seq a (n + 64)"
proof -
  have dec: "128 * (n div 128) + n mod 128 = n" by simp
  have ndlt: "n div 128 < 2" using n by linarith
  have np: "n + 64 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n by simp
  have e2: "(n + 64) mod 65536 = n + 64" using np by simp
  have sh: "unat ((1::16 word) << 6) = 64" "((1::16 word) << 6) = 64"
           "unat ((64::16 word) << 1) = 128" "((64::16 word) << 1) = 128"
           "unat ((0x100::16 word) >> 6) = 4" "((0x100::16 word) >> 6) = 0x4" by eval+
  show ?thesis
    using hlo n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma invlevel6_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 128 < 64" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 6 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (3 - n div 128)) * sext64 (nth_seq a (n - 64) - nth_seq a n))"
proof -
  have nge: "64 \<le> n" using hhi by (cases "n < 64") auto
  have e1: "n mod 65536 = n" using n by simp
  have ndlt: "n div 128 < 2" using n by linarith
  have es: "unat (word_of_nat n - (64::16 word)) = n - 64"
    using nge by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 128 :: 16 word) \<le> 0x3"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0x3::16 word) - word_of_nat n div 128) = 3 - n div 128"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  have sh: "unat ((1::16 word) << 6) = 64" "((1::16 word) << 6) = 64"
           "unat ((64::16 word) << 1) = 128" "((64::16 word) << 1) = 128"
           "unat ((0x100::16 word) >> 6) = 4" "((0x100::16 word) >> 6) = 0x4" by eval+
  show ?thesis
    using hhi n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt es ez sh)
    done
qed

lemma invlevel6_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 6 a) n
       = (if n mod 128 < 64
          then nth_seq a n + nth_seq a (n + 64)
          else montgomery_reduce (sext64 (- nth_seq zetas (3 - n div 128)) * sext64 (nth_seq a (n - 64) - nth_seq a n)))"
  using invlevel6_lo[OF _ n] invlevel6_hi[OF _ n] by simp

text \<open>Level 7 (\<open>len = 128\<close>, \<open>twolen = 256\<close>, \<open>kbase = 2\<close>), twiddle constant \<open>-zetas[1]\<close>.\<close>
lemma invlevel7_lo:
  fixes a :: "[256][32]"
  assumes hlo: "n mod 256 < 128" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 7 a) n = nth_seq a n + nth_seq a (n + 128)"
proof -
  have dec: "256 * (n div 256) + n mod 256 = n" by simp
  have ndlt: "n div 256 < 1" using n by linarith
  have np: "n + 128 < 256" using dec hlo ndlt by linarith
  have e1: "n mod 65536 = n" using n by simp
  have e2: "(n + 128) mod 65536 = n + 128" using np by simp
  have sh: "unat ((1::16 word) << 7) = 128" "((1::16 word) << 7) = 128"
           "unat ((128::16 word) << 1) = 256" "((128::16 word) << 1) = 256"
           "unat ((0x100::16 word) >> 7) = 2" "((0x100::16 word) >> 7) = 0x2" by eval+
  show ?thesis
    using hlo n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt sh)
    done
qed

lemma invlevel7_hi:
  fixes a :: "[256][32]"
  assumes hhi: "\<not> n mod 256 < 128" and n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 7 a) n
       = montgomery_reduce (sext64 (- nth_seq zetas (1 - n div 256)) * sext64 (nth_seq a (n - 128) - nth_seq a n))"
proof -
  have nge: "128 \<le> n" using hhi by (cases "n < 128") auto
  have e1: "n mod 65536 = n" using n by simp
  have ndlt: "n div 256 < 1" using n by linarith
  have nd0: "n div 256 = 0" using n by simp
  have es: "unat (word_of_nat n - (128::16 word)) = n - 128"
    using nge by (simp add: unat_sub word_le_nat_alt unat_of_nat e1)
  have zle: "(word_of_nat n div 256 :: 16 word) \<le> 0x1"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat e1)
  have ez: "unat ((0x1::16 word) - word_of_nat n div 256) = 1 - n div 256"
    using zle by (simp add: unat_sub unat_div unat_of_nat e1)
  have sh: "unat ((1::16 word) << 7) = 128" "((1::16 word) << 7) = 128"
           "unat ((128::16 word) << 1) = 256" "((128::16 word) << 1) = 256"
           "unat ((0x100::16 word) >> 7) = 2" "((0x100::16 word) >> 7) = 0x2" by eval+
  show ?thesis
    using hhi n
    apply (simp add: invnttLevel_def fromTo_def Let_def n)
    apply (simp add: cryptol_prim_defs word_seq_convs
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     unat_of_nat unat_word_ariths sh)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt nd0 es ez sh)
    done
qed

lemma invlevel7_coeff:
  fixes a :: "[256][32]"
  assumes n: "n < (256::nat)"
  shows "nth_seq (invnttLevel 7 a) n
       = (if n mod 256 < 128
          then nth_seq a n + nth_seq a (n + 128)
          else montgomery_reduce (sext64 (- nth_seq zetas (1 - n div 256)) * sext64 (nth_seq a (n - 128) - nth_seq a n)))"
  using invlevel7_lo[OF _ n] invlevel7_hi[OF _ n] by simp

end

section \<open>The abstract Gentleman-Sande layer\<close>

text \<open>The inverse analog of CT_Routing's \<open>bflyLayer\<close>: one abstract Gentleman-Sande
  layer on an int-coefficient function, the common shape both the montgomery model
  and the normal-domain model reduce to mod q. Stride \<open>L\<close>, twiddle base \<open>ZB\<close> (= the
  level's \<open>kbase - 1\<close>). Lower leg is the unreduced sum \<open>g n + g(n+L)\<close>; upper leg is
  the negated-twiddle product on the difference, matching the C's Gentleman-Sande
  butterfly. Pure nat/int (coercion off, as in CT_Routing).\<close>

declare [[coercion_enabled = false]]

definition gsLayer :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
  "gsLayer L ZB g = (\<lambda>n.
     if n mod (2*L) < L
     then (g n + g (n + L)) mod 8380417
     else (zt (ZB - n div (2*L)) * (g n - g (n - L))) mod 8380417)"

lemma gsLayer_lt: "gsLayer L ZB g n < 8380417"
  by (simp add: gsLayer_def)

lemma gsLayer_ge: "0 \<le> gsLayer L ZB g n"
  by (simp add: gsLayer_def)

text \<open>The abstract Gentleman-Sande layer respects pointwise mod-q congruence of its
  coefficient function (analog of \<open>bflyLayer_cong_g\<close>); the engine of the per-layer
  composition.\<close>
lemma gsLayer_cong_g:
  fixes g g' :: "nat \<Rightarrow> int"
  assumes cg: "\<And>m. g m mod 8380417 = g' m mod 8380417"
  shows "gsLayer L ZB g n mod 8380417 = gsLayer L ZB g' n mod 8380417"
proof -
  have lo: "(g n + g (n + L)) mod 8380417 = (g' n + g' (n + L)) mod 8380417"
    by (rule mod_add_cong[OF cg cg])
  have hi: "(zt i * (g n - g (n - L))) mod 8380417
          = (zt i * (g' n - g' (n - L))) mod 8380417" for i
  proof -
    have d: "(g n - g (n - L)) mod 8380417 = (g' n - g' (n - L)) mod 8380417"
      by (rule mod_diff_cong[OF cg cg])
    show ?thesis by (rule mod_mult_cong[OF refl d])
  qed
  show ?thesis
  proof (cases "n mod (2*L) < L")
    case True thus ?thesis unfolding gsLayer_def using lo by simp
  next
    case False thus ?thesis unfolding gsLayer_def using hi by simp
  qed
qed

section \<open>Per-layer montgomery congruences\<close>

text \<open>A looser-cap variant of \<open>mont_input_ok_of_bounds\<close>. The forward version caps the
  coefficient magnitude at \<open>2139103230\<close> (it only ever sees \<open>coeff +/- mont(...)\<close>, bounded
  by \<open>B + Q\<close>). The Gentleman-Sande high leg instead feeds the montgomery reduce a
  *difference* of two coefficients, magnitude up to \<open>2B\<close>; for the loosest per-layer bound
  \<open>B \<le> 2^30 - 1\<close> that is \<open>2B \<le> 2^31 - 1\<close>, just over the forward cap. The precondition
  \<open>|zeta * x| < 2^31 * q\<close> still holds with wide margin: \<open>2^22 * (2^31 - 1) < 2^31 * q\<close>.\<close>
lemma mont_input_ok_of_bounds':
  fixes z x :: int
  assumes zlo: "- 4194304 \<le> z" and zhi: "z \<le> 4194304"
      and xlo: "- C \<le> x" and xhi: "x \<le> C" and Chi: "C \<le> 2147483647"
  shows "mont_input_ok (z * x)"
proof -
  have az: "\<bar>z\<bar> \<le> 4194304" using zlo zhi by (simp add: abs_le_iff)
  have ax: "\<bar>x\<bar> \<le> C" using xlo xhi by (simp add: abs_le_iff)
  have "\<bar>z * x\<bar> \<le> 4194304 * C" unfolding abs_mult using az ax by (intro mult_mono) auto
  also have "\<dots> \<le> 4194304 * 2147483647" using Chi by simp
  finally have "\<bar>z * x\<bar> \<le> 9007199250546688" by simp
  thus ?thesis unfolding mont_input_ok_def MLDSA_NTT_Spec.q_def by (simp add: abs_le_iff)
qed

context includes cryptol_syntax begin

text \<open>The generic per-position Gentleman-Sande congruence: given a layer output \<open>b\<close> whose
  position \<open>n\<close> unfolds to the inverse butterfly (low = unreduced add \<open>a[n]+a[n+L]\<close>, high =
  \<open>montgomery_reduce(-zetas[ZB - n div 2L] * (a[n-L]-a[n]))\<close>), the signed view of \<open>b\<close> at
  \<open>n\<close> is congruent mod q to one abstract \<open>gsLayer L ZB\<close> on the montgomery sint-view of \<open>a\<close>.
  The coefficient hypothesis is exactly \<open>invlevelN_coeff\<close>; the two index side-conditions
  (\<open>0 < ZB - n div 2L\<close>, \<open>ZB - n div 2L < 256\<close>) are discharged per level by \<open>linarith\<close>.
  Input bound \<open>B \<le> 2^30 - 1\<close> so both legs avoid int32 overflow (the sum/difference of two
  \<open>B\<close>-bounded coefficients stays in \<open>(-2^31, 2^31)\<close>). The inverse mirror of
  \<open>Mont_Bridge.mbfly0..7\<close>, generalized over the layer so it is proved once.\<close>
lemma gs_congruence:
  fixes a b :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
      and Lpos: "0 < L"
      and coeff: "nth_seq b n =
            (if n mod (2 * L) < L
             then nth_seq a n + nth_seq a (n + L)
             else montgomery_reduce (sext64 (- nth_seq zetas (ZB - n div (2 * L)))
                                     * sext64 (nth_seq a (n - L) - nth_seq a n)))"
      and idxpos: "0 < ZB - n div (2 * L)"
      and idxlt: "ZB - n div (2 * L) < 256"
  shows "sf b n mod 8380417 = gsLayer L ZB (sf a) n mod 8380417"
proof (cases "n mod (2 * L) < L")
  case True
  \<comment> \<open>low leg: an unreduced int32 add of two bounded coefficients\<close>
  have aP: "- B \<le> sint_seq (nth_seq a n)" "sint_seq (nth_seq a n) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have aQ: "- B \<le> sint_seq (nth_seq a (n + L))" "sint_seq (nth_seq a (n + L)) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have noov: "sint_seq (nth_seq a n + nth_seq a (n + L))
            = sint_seq (nth_seq a n) + sint_seq (nth_seq a (n + L))"
    by (rule sint_seq_add_eq) (use aP aQ Bhi in linarith)+
  have L: "sf b n mod 8380417 = (sf a n + sf a (n + L)) mod 8380417"
    using coeff True noov by (simp add: sf_def)
  have R: "gsLayer L ZB (sf a) n mod 8380417 = (sf a n + sf a (n + L)) mod 8380417"
    using True by (simp add: gsLayer_def)
  show ?thesis using L R by simp
next
  case False
  \<comment> \<open>high leg: a montgomery reduce of the negated twiddle on the int32 difference\<close>
  have aP: "- B \<le> sint_seq (nth_seq a (n - L))" "sint_seq (nth_seq a (n - L)) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have aR: "- B \<le> sint_seq (nth_seq a n)" "sint_seq (nth_seq a n) \<le> B"
    using B unfolding ntt_bounded_def by auto
  have dsub: "sint_seq (nth_seq a (n - L) - nth_seq a n)
            = sint_seq (nth_seq a (n - L)) - sint_seq (nth_seq a n)"
    by (rule sint_seq_sub_eq) (use aP aR Bhi in linarith)+
  have dlo: "- (2 * B) \<le> sint_seq (nth_seq a (n - L) - nth_seq a n)"
    using dsub aP aR by linarith
  have dhi: "sint_seq (nth_seq a (n - L) - nth_seq a n) \<le> 2 * B"
    using dsub aP aR by linarith
  have zQn: "- 4194304 \<le> - sint_seq (nth_seq zetas (ZB - n div (2 * L)))"
            "- sint_seq (nth_seq zetas (ZB - n div (2 * L))) \<le> 4194304"
    using Assay_Equivalence.zeta_bound[of "ZB - n div (2 * L)"] by auto
  have B2: "2 * B \<le> 2147483647" using Bhi by linarith
  have ok: "mont_input_ok (- sint_seq (nth_seq zetas (ZB - n div (2 * L)))
                           * sint_seq (nth_seq a (n - L) - nth_seq a n))"
  proof -
    have "mont_input_ok ((- sint_seq (nth_seq zetas (ZB - n div (2 * L))))
                         * sint_seq (nth_seq a (n - L) - nth_seq a n))"
      by (rule mont_input_ok_of_bounds'[OF zQn(1) zQn(2) dlo dhi B2])
    thus ?thesis by simp
  qed
  have bc: "sint_seq (montgomery_reduce (sext64 (- nth_seq zetas (ZB - n div (2 * L)))
                                         * sext64 (nth_seq a (n - L) - nth_seq a n))) mod 8380417
          = (- uint_seq (nth_seq zetabrv (ZB - n div (2 * L)))
             * sint_seq (nth_seq a (n - L) - nth_seq a n)) mod 8380417"
    using inv_butterfly_cong[OF idxpos idxlt ok] .
  have lhs: "sf b n mod 8380417
           = (- uint_seq (nth_seq zetabrv (ZB - n div (2 * L)))
              * sint_seq (nth_seq a (n - L) - nth_seq a n)) mod 8380417"
    using coeff False bc by (simp add: sf_def)
  have rhsalg: "(- uint_seq (nth_seq zetabrv (ZB - n div (2 * L)))
                 * sint_seq (nth_seq a (n - L) - nth_seq a n)) mod 8380417
              = (zt (ZB - n div (2 * L)) * (sf a n - sf a (n - L))) mod 8380417"
  proof -
    have "(- uint_seq (nth_seq zetabrv (ZB - n div (2 * L)))
           * sint_seq (nth_seq a (n - L) - nth_seq a n))
        = - uint_seq (nth_seq zetabrv (ZB - n div (2 * L)))
          * (sint_seq (nth_seq a (n - L)) - sint_seq (nth_seq a n))"
      by (simp only: dsub)
    also have "\<dots> = zt (ZB - n div (2 * L)) * (sf a n - sf a (n - L))"
      by (simp add: zt_def sf_def algebra_simps)
    finally show ?thesis by simp
  qed
  have R: "gsLayer L ZB (sf a) n mod 8380417
         = (zt (ZB - n div (2 * L)) * (sf a n - sf a (n - L))) mod 8380417"
    using False by (simp add: gsLayer_def)
  show ?thesis using lhs rhsalg R by simp
qed

text \<open>The eight per-layer instances. Each feeds \<open>gs_congruence\<close> the matching
  \<open>invlevelN_coeff\<close> unfold and the two index facts (\<open>linarith\<close> from \<open>n < 256\<close>). The
  abstract layer is \<open>gsLayer (2^ell) (2^(8-ell) - 1)\<close>: stride \<open>len = 2^ell\<close>, twiddle base
  \<open>ZB = kbase - 1\<close>. Level 0 needs the \<open>n mod 2 < 1 \<longleftrightarrow> n mod 2 = 0\<close> bridge.\<close>

lemma mbfly_inv0:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 0 a) n mod 8380417 = gsLayer 1 255 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel0_coeff[OF n] n in \<open>simp_all add: linorder_not_less\<close>)

lemma mbfly_inv1:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 1 a) n mod 8380417 = gsLayer 2 127 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel1_coeff[OF n] n in simp_all)

lemma mbfly_inv2:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 2 a) n mod 8380417 = gsLayer 4 63 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel2_coeff[OF n] n in simp_all)

lemma mbfly_inv3:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 3 a) n mod 8380417 = gsLayer 8 31 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel3_coeff[OF n] n in simp_all)

lemma mbfly_inv4:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 4 a) n mod 8380417 = gsLayer 16 15 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel4_coeff[OF n] n in simp_all)

lemma mbfly_inv5:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 5 a) n mod 8380417 = gsLayer 32 7 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel5_coeff[OF n] n in simp_all)

lemma mbfly_inv6:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 6 a) n mod 8380417 = gsLayer 64 3 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel6_coeff[OF n] n in simp_all)

lemma mbfly_inv7:
  fixes a :: "[256][32]"
  assumes B: "ntt_bounded B a" and Bhi: "B \<le> 1073741823" and n: "n < 256"
  shows "sf (invnttLevel 7 a) n mod 8380417 = gsLayer 128 1 (sf a) n mod 8380417"
  by (rule gs_congruence[OF B Bhi n])
     (use invlevel7_coeff[OF n] n in simp_all)

end

section \<open>Normal-side inverse layer unfolds\<close>

text \<open>The Gentleman-Sande mirror of Bridge_Word's forward layer unfolds, but for
  the normal-domain inverse layer @{const nttLayerInv}. The inverse butterfly differs: the
  low leg is a plain modular add @{text "(w[p] + w[p+len]) mod q"} (no twiddle), the high leg
  is @{text "(z * tHi) mod q"} with @{text "z = (q - zetabrv[idx]) mod q"} (the negated
  twiddle) and @{text "tHi = (w[p-len] + q - w[p]) mod q"}. The @{text "blk >= iter"} branch
  never fires: @{text "blk = p div 2len"} maxes at @{text "iter - 1"}. These produce the cf
  word-exact form; the bridge to @{const gsLayer} (mod q) is a separate step.

  Three int no-overflow facts feed the word reductions (companions to Bridge_Word's
  @{text add_mod_aux} / @{text mul_mod_aux} / @{text sub_mod_aux}): the negated twiddle
  @{text "(q - z) mod q"}, the high-leg difference @{text "(a + q - b) mod q"} kept inside a
  later multiply (so no @{text "take_bit 32"} truncation yet), and the product-then-truncate.\<close>

lemma negz_mod_aux:
  fixes A :: int
  assumes "0 \<le> A" "A < 8380417"
  shows "(8380417 - A) mod 18446744073709551616 mod 8380417 = (8380417 - A) mod 8380417"
proof -
  have "0 \<le> 8380417 - A \<and> 8380417 - A < 18446744073709551616" using assms by simp
  thus ?thesis by (simp add: mod_pos_pos_trivial)
qed

lemma subnd_mod_aux:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "((A + 8380417) mod 18446744073709551616 - B) mod 18446744073709551616 mod 8380417
       = (A + 8380417 - B) mod 8380417"
proof -
  have h1: "(A + 8380417) mod 18446744073709551616 = A + 8380417"
    using assms by (simp add: mod_pos_pos_trivial)
  have h2: "(A + 8380417 - B) mod 18446744073709551616 = A + 8380417 - B"
    using assms by (simp add: mod_pos_pos_trivial)
  show ?thesis using h1 h2 by simp
qed

lemma muld_mod_aux:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "take_bit 32 (A * B mod 18446744073709551616 mod 8380417) = (A * B) mod 8380417"
proof -
  have nd: "A * B mod 18446744073709551616 mod 8380417 = (A * B) mod 8380417"
    using mul_mod_aux[OF assms] .
  have lt: "(A * B) mod 8380417 < 2 ^ 32" using pos_mod_bound[of 8380417 "A * B"] by simp
  have ge: "0 \<le> (A * B) mod 8380417" by simp
  show ?thesis using nd lt ge by (simp add: take_bit_int_eq_self)
qed

context includes cryptol_translation_syntax begin

text \<open>Level 7 (\<open>len=128, iter=1, m0=2\<close>): the inverse mirror of forward \<open>layer1\<close>. \<open>blk = n div 256 = 0\<close>,
  \<open>off = n\<close>, twiddle index \<open>(m0-1) - blk = 1\<close> (the constant \<open>zetabrv[1]\<close>).\<close>
lemma invlayer7_lo:
  fixes w :: "[256][32]"
  assumes n: "n < (128::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 128 1 2 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 128))) mod 8380417"
proof -
  have n256: "n < 256" using n by simp
  have np: "n + 128 < 256" using n by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417"
    using bw[OF n256] by (simp add: uint_seq_conv)
  have bn128: "uint (seq_to_word (nth_seq w (n + 128))) < 8380417"
    using bw[OF np] by (simp add: uint_seq_conv)
  have e1: "n mod 18446744073709551616 = n" using n by simp
  have e2: "n mod 256 = n" using n by simp
  have e3: "n div 256 = 0" using n by simp
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using n
    apply (simp add: nttLayerInv_def fromTo_def Let_def n256)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n256 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 e3)
    apply (simp add: tb bn bn128 uq add_mod_aux3)
    done
qed

lemma invlayer7_hi:
  fixes w :: "[256][32]"
  assumes n: "128 \<le> n" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 128 1 2 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv 1)) mod 8380417
          * ((uint_seq (nth_seq w (n - 128)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
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
  have wd: "(word_of_nat n div 0x100 :: 64 word) = 0"
  proof -
    have "unat (word_of_nat n div 0x100 :: 64 word) = 0"
      using n2 by (simp add: unat_div unat_of_nat)
    thus ?thesis by (simp add: unat_eq_zero)
  qed
  have ez: "unat ((1::64 word) - word_of_nat n div 0x100) = 1"
    using wd by simp
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof -
    have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self)
  qed
  show ?thesis
    using n n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 e3 es wd ez)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer7_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 128 1 2 w) n)
       = (if n mod 256 < 128
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 128))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv 1)) mod 8380417
                * ((uint_seq (nth_seq w (n - 128)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
proof -
  have e2: "n mod 256 = n" using n by simp
  show ?thesis
  proof (cases "n < 128")
    case True thus ?thesis using invlayer7_lo[OF True bw] e2 by simp
  next
    case False hence ge: "128 \<le> n" by simp
    thus ?thesis using invlayer7_hi[OF ge n bw] False e2 by simp
  qed
qed

text \<open>Level 6 (\<open>len=64, iter=2, m0=4\<close>): variable twiddle index \<open>3 - n div 128\<close>. Template
  for the variable-index levels (the inverse mirror of forward \<open>layer2..7\<close>).\<close>
lemma invlayer6_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 128 < 64" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 64 2 4 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 64))) mod 8380417"
proof -
  have np: "n + 64 < 256" using hlo n2 by presburger
  have ndlt: "n div 128 < 2" using n2 by linarith
  have ndle: "\<not> 2 \<le> n div 128" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 64) mod 18446744073709551616 = n + 64" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bn64: "uint (seq_to_word (nth_seq w (n + 64))) < 8380417" using bw[OF np] by (simp add: uint_seq_conv)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt ndle)
    apply (simp add: tb bn bn64 uq add_mod_aux3)
    done
qed

lemma invlayer6_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 128 < 64" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 64 2 4 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv (3 - n div 128))) mod 8380417
          * ((uint_seq (nth_seq w (n - 64)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
proof -
  have nge: "64 \<le> n" using hhi by (cases "n < 64") auto
  have nm: "n - 64 < 256" using n2 by simp
  have ndlt: "n div 128 < 2" using n2 by linarith
  have ndle: "\<not> 2 \<le> n div 128" using n2 by linarith
  have nd: "3 - n div 128 < 256" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 64))) < 8380417" using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (3 - n div 128))) < 8380417"
    using Bridge_Word.zeta_bound[of "3 - n div 128"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x40::64 word)) = n - 64"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have zle: "(word_of_nat n div 0x80 :: 64 word) \<le> 3"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat)
  have ez: "unat ((3::64 word) - word_of_nat n div 0x80) = 3 - n div 128"
    using zle e1 by (simp add: unat_sub unat_div unat_of_nat)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt ndle es zle ez)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer6_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 64 2 4 w) n)
       = (if n mod 128 < 64
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 64))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv (3 - n div 128))) mod 8380417
                * ((uint_seq (nth_seq w (n - 64)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
  using invlayer6_lo[OF _ n bw] invlayer6_hi[OF _ n bw] by simp

text \<open>Level 0 (\<open>len=1, iter=128, m0=256\<close>): low predicate \<open>n mod 2 < 1\<close> (even positions),
  variable twiddle index \<open>255 - n div 2\<close>. The inverse mirror of forward \<open>layer8\<close>.\<close>
lemma invlayer0_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 2 < 1" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 1 128 256 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 1))) mod 8380417"
proof -
  have np: "Suc n < 256" using hlo n2 by presburger
  have ev: "n mod 2 = 0" using hlo by simp
  have ndlt: "n div 2 < 128" using n2 by linarith
  have ndle: "\<not> 128 \<le> n div 2" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "Suc n mod 18446744073709551616 = Suc n" using np by simp
  have wm: "(word_of_nat n :: 64 word) mod 2 = 0"
  proof -
    have "unat ((word_of_nat n :: 64 word) mod 2) = 0" using ev n2 by (simp add: unat_mod unat_of_nat)
    thus ?thesis by (simp add: unat_eq_zero)
  qed
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bn1: "uint (seq_to_word (nth_seq w (Suc n))) < 8380417" using bw[OF np] by (simp add: uint_seq_conv)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 ev ndlt ndle wm)
    apply (simp add: tb bn bn1 uq add_mod_aux3)
    done
qed

lemma invlayer0_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 2 < 1" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 1 128 256 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv (255 - n div 2))) mod 8380417
          * ((uint_seq (nth_seq w (n - 1)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
proof -
  have nge: "1 \<le> n" using hhi by (cases "n < 1") auto
  have od: "n mod 2 = 1" using hhi by presburger
  have nm: "n - Suc 0 < 256" using n2 by simp
  have ndlt: "n div 2 < 128" using n2 by linarith
  have ndle: "\<not> 128 \<le> n div 2" using n2 by linarith
  have nd: "255 - n div 2 < 256" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have wm: "(word_of_nat n :: 64 word) mod 2 = 1"
  proof -
    have "unat ((word_of_nat n :: 64 word) mod 2) = 1" using od n2 by (simp add: unat_mod unat_of_nat)
    thus ?thesis by (metis unat_1 word_unat.Rep_inject)
  qed
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - Suc 0))) < 8380417" using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (255 - n div 2))) < 8380417"
    using Bridge_Word.zeta_bound[of "255 - n div 2"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x1::64 word)) = n - 1"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have zle: "(word_of_nat n div 0x2 :: 64 word) \<le> 255"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat)
  have ez: "unat ((255::64 word) - word_of_nat n div 0x2) = 255 - n div 2"
    using zle e1 by (simp add: unat_sub unat_div unat_of_nat)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi od ndlt ndle es zle ez wm)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer0_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 1 128 256 w) n)
       = (if n mod 2 < 1
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 1))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv (255 - n div 2))) mod 8380417
                * ((uint_seq (nth_seq w (n - 1)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
  using invlayer0_lo[OF _ n bw] invlayer0_hi[OF _ n bw] by simp

text \<open>Levels 1..5: same shape as level 6 (variable twiddle index, mod-predicate), constants
  per @{const invParamsRef}: level \<open>ell\<close> is \<open>nttLayerInv (2^ell) (2^(7-ell)) (2^(8-ell))\<close>,
  twiddle index \<open>(2^(8-ell) - 1) - n div 2^(ell+1)\<close>.\<close>

lemma invlayer1_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 4 < 2" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 2 64 128 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 2))) mod 8380417"
proof -
  have np: "n + 2 < 256" using hlo n2 by presburger
  have ndlt: "n div 4 < 64" using n2 by linarith
  have ndle: "\<not> 64 \<le> n div 4" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "Suc (Suc n) mod 18446744073709551616 = Suc (Suc n)" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bn2: "uint (seq_to_word (nth_seq w (Suc (Suc n)))) < 8380417" using bw[OF np] by (simp add: uint_seq_conv)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt ndle)
    apply (simp add: tb bn bn2 uq add_mod_aux3)
    done
qed

lemma invlayer1_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 4 < 2" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 2 64 128 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv (127 - n div 4))) mod 8380417
          * ((uint_seq (nth_seq w (n - 2)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
proof -
  have nge: "2 \<le> n" using hhi by (cases "n < 2") auto
  have nm: "n - 2 < 256" using n2 by simp
  have ndlt: "n div 4 < 64" using n2 by linarith
  have ndle: "\<not> 64 \<le> n div 4" using n2 by linarith
  have nd: "127 - n div 4 < 256" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 2))) < 8380417" using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (127 - n div 4))) < 8380417"
    using Bridge_Word.zeta_bound[of "127 - n div 4"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x2::64 word)) = n - 2"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have zle: "(word_of_nat n div 0x4 :: 64 word) \<le> 127"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat)
  have ez: "unat ((127::64 word) - word_of_nat n div 0x4) = 127 - n div 4"
    using zle e1 by (simp add: unat_sub unat_div unat_of_nat)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt ndle es zle ez)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer1_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 2 64 128 w) n)
       = (if n mod 4 < 2
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 2))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv (127 - n div 4))) mod 8380417
                * ((uint_seq (nth_seq w (n - 2)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
  using invlayer1_lo[OF _ n bw] invlayer1_hi[OF _ n bw] by simp

lemma invlayer2_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 8 < 4" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 4 32 64 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 4))) mod 8380417"
proof -
  have np: "n + 4 < 256" using hlo n2 by presburger
  have ndlt: "n div 8 < 32" using n2 by linarith
  have ndle: "\<not> 32 \<le> n div 8" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 4) mod 18446744073709551616 = n + 4" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bn4: "uint (seq_to_word (nth_seq w (n + 4))) < 8380417" using bw[OF np] by (simp add: uint_seq_conv)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt ndle)
    apply (simp add: tb bn bn4 uq add_mod_aux3)
    done
qed

lemma invlayer2_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 8 < 4" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 4 32 64 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv (63 - n div 8))) mod 8380417
          * ((uint_seq (nth_seq w (n - 4)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
proof -
  have nge: "4 \<le> n" using hhi by (cases "n < 4") auto
  have nm: "n - 4 < 256" using n2 by simp
  have ndlt: "n div 8 < 32" using n2 by linarith
  have ndle: "\<not> 32 \<le> n div 8" using n2 by linarith
  have nd: "63 - n div 8 < 256" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 4))) < 8380417" using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (63 - n div 8))) < 8380417"
    using Bridge_Word.zeta_bound[of "63 - n div 8"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x4::64 word)) = n - 4"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have zle: "(word_of_nat n div 0x8 :: 64 word) \<le> 63"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat)
  have ez: "unat ((63::64 word) - word_of_nat n div 0x8) = 63 - n div 8"
    using zle e1 by (simp add: unat_sub unat_div unat_of_nat)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt ndle es zle ez)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer2_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 4 32 64 w) n)
       = (if n mod 8 < 4
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 4))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv (63 - n div 8))) mod 8380417
                * ((uint_seq (nth_seq w (n - 4)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
  using invlayer2_lo[OF _ n bw] invlayer2_hi[OF _ n bw] by simp

lemma invlayer3_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 16 < 8" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 8 16 32 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 8))) mod 8380417"
proof -
  have np: "n + 8 < 256" using hlo n2 by presburger
  have ndlt: "n div 16 < 16" using n2 by linarith
  have ndle: "\<not> 16 \<le> n div 16" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 8) mod 18446744073709551616 = n + 8" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bn8: "uint (seq_to_word (nth_seq w (n + 8))) < 8380417" using bw[OF np] by (simp add: uint_seq_conv)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt ndle)
    apply (simp add: tb bn bn8 uq add_mod_aux3)
    done
qed

lemma invlayer3_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 16 < 8" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 8 16 32 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv (31 - n div 16))) mod 8380417
          * ((uint_seq (nth_seq w (n - 8)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
proof -
  have nge: "8 \<le> n" using hhi by (cases "n < 8") auto
  have nm: "n - 8 < 256" using n2 by simp
  have ndlt: "n div 16 < 16" using n2 by linarith
  have ndle: "\<not> 16 \<le> n div 16" using n2 by linarith
  have nd: "31 - n div 16 < 256" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 8))) < 8380417" using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (31 - n div 16))) < 8380417"
    using Bridge_Word.zeta_bound[of "31 - n div 16"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x8::64 word)) = n - 8"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have zle: "(word_of_nat n div 0x10 :: 64 word) \<le> 31"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat)
  have ez: "unat ((31::64 word) - word_of_nat n div 0x10) = 31 - n div 16"
    using zle e1 by (simp add: unat_sub unat_div unat_of_nat)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt ndle es zle ez)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer3_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 8 16 32 w) n)
       = (if n mod 16 < 8
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 8))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv (31 - n div 16))) mod 8380417
                * ((uint_seq (nth_seq w (n - 8)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
  using invlayer3_lo[OF _ n bw] invlayer3_hi[OF _ n bw] by simp

lemma invlayer4_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 32 < 16" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 16 8 16 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 16))) mod 8380417"
proof -
  have np: "n + 16 < 256" using hlo n2 by presburger
  have ndlt: "n div 32 < 8" using n2 by linarith
  have ndle: "\<not> 8 \<le> n div 32" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 16) mod 18446744073709551616 = n + 16" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bn16: "uint (seq_to_word (nth_seq w (n + 16))) < 8380417" using bw[OF np] by (simp add: uint_seq_conv)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt ndle)
    apply (simp add: tb bn bn16 uq add_mod_aux3)
    done
qed

lemma invlayer4_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 32 < 16" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 16 8 16 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv (15 - n div 32))) mod 8380417
          * ((uint_seq (nth_seq w (n - 16)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
proof -
  have nge: "16 \<le> n" using hhi by (cases "n < 16") auto
  have nm: "n - 16 < 256" using n2 by simp
  have ndlt: "n div 32 < 8" using n2 by linarith
  have ndle: "\<not> 8 \<le> n div 32" using n2 by linarith
  have nd: "15 - n div 32 < 256" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 16))) < 8380417" using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (15 - n div 32))) < 8380417"
    using Bridge_Word.zeta_bound[of "15 - n div 32"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x10::64 word)) = n - 16"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have zle: "(word_of_nat n div 0x20 :: 64 word) \<le> 15"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat)
  have ez: "unat ((15::64 word) - word_of_nat n div 0x20) = 15 - n div 32"
    using zle e1 by (simp add: unat_sub unat_div unat_of_nat)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt ndle es zle ez)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer4_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 16 8 16 w) n)
       = (if n mod 32 < 16
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 16))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv (15 - n div 32))) mod 8380417
                * ((uint_seq (nth_seq w (n - 16)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
  using invlayer4_lo[OF _ n bw] invlayer4_hi[OF _ n bw] by simp

lemma invlayer5_lo:
  fixes w :: "[256][32]"
  assumes hlo: "n mod 64 < 32" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 32 4 8 w) n)
       = (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 32))) mod 8380417"
proof -
  have np: "n + 32 < 256" using hlo n2 by presburger
  have ndlt: "n div 64 < 4" using n2 by linarith
  have ndle: "\<not> 4 \<le> n div 64" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have e2: "(n + 32) mod 18446744073709551616 = n + 32" using np by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bn32: "uint (seq_to_word (nth_seq w (n + 32))) < 8380417" using bw[OF np] by (simp add: uint_seq_conv)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hlo n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 e2 hlo ndlt ndle)
    apply (simp add: tb bn bn32 uq add_mod_aux3)
    done
qed

lemma invlayer5_hi:
  fixes w :: "[256][32]"
  assumes hhi: "\<not> n mod 64 < 32" and n2: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 32 4 8 w) n)
       = ((8380417 - uint_seq (nth_seq zetabrv (7 - n div 64))) mod 8380417
          * ((uint_seq (nth_seq w (n - 32)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
         mod 8380417"
proof -
  have nge: "32 \<le> n" using hhi by (cases "n < 32") auto
  have nm: "n - 32 < 256" using n2 by simp
  have ndlt: "n div 64 < 4" using n2 by linarith
  have ndle: "\<not> 4 \<le> n div 64" using n2 by linarith
  have nd: "7 - n div 64 < 256" using n2 by linarith
  have e1: "n mod 18446744073709551616 = n" using n2 by simp
  have bn: "uint (seq_to_word (nth_seq w n)) < 8380417" using bw[OF n2] by (simp add: uint_seq_conv)
  have bnm: "uint (seq_to_word (nth_seq w (n - 32))) < 8380417" using bw[OF nm] by (simp add: uint_seq_conv)
  have bz: "uint (seq_to_word (nth_seq zetabrv (7 - n div 64))) < 8380417"
    using Bridge_Word.zeta_bound[of "7 - n div 64"] nd by (simp add: uint_seq_conv)
  have es: "unat (word_of_nat n - (0x20::64 word)) = n - 32"
    using nge n2 by (simp add: unat_sub word_le_nat_alt unat_of_nat)
  have zle: "(word_of_nat n div 0x40 :: 64 word) \<le> 7"
    using ndlt by (simp add: word_le_nat_alt unat_div unat_of_nat)
  have ez: "unat ((7::64 word) - word_of_nat n div 0x40) = 7 - n div 64"
    using zle e1 by (simp add: unat_sub unat_div unat_of_nat)
  have uq: "uint (seq_to_word fips204_ntt_lift.q) = 8380417" by eval
  have tb: "take_bit 64 (uint x) = uint x" for x :: "32 word"
  proof - have "uint x < 18446744073709551616" using uint_lt2p[of x] by simp
    thus ?thesis by (simp add: take_bit_int_eq_self) qed
  show ?thesis
    using hhi n2
    apply (simp add: nttLayerInv_def fromTo_def Let_def n2)
    apply (simp add: cryptol_prim_defs word_seq_convs q_def
                     from_nat_def from_int_word_def of_int_of_nat_eq ucast_of_nat_small
                     unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                     uint_mod_distrib uint_word_ariths unat_of_nat unat_word_ariths
                     n2 uint_seq_conv)
    apply (simp add: word_less_nat_alt word_le_nat_alt unat_div unat_mod unat_of_nat
                     e1 hhi ndlt ndle es zle ez)
    apply (simp add: tb bn bnm bz uq negz_mod_aux subnd_mod_aux muld_mod_aux)
    done
qed

lemma invlayer5_coeff:
  fixes w :: "[256][32]"
  assumes n: "n < (256::nat)"
  assumes bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  shows "uint_seq (nth_seq (nttLayerInv 32 4 8 w) n)
       = (if n mod 64 < 32
          then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + 32))) mod 8380417
          else ((8380417 - uint_seq (nth_seq zetabrv (7 - n div 64))) mod 8380417
                * ((uint_seq (nth_seq w (n - 32)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
               mod 8380417)"
  using invlayer5_lo[OF _ n bw] invlayer5_hi[OF _ n bw] by simp

section \<open>Normal-side cf == gsLayer bridge\<close>

text \<open>The inverse analog of CT_Routing's @{text abs_N}: each normal-domain inverse layer,
  viewed on the cf coefficient function, is congruent mod q to the abstract @{const gsLayer}.
  The low leg is a literal match; the high leg is a mod-q congruence, since the normal model
  computes the negated twiddle and the high difference reduced (@{text "(q - z) mod q"},
  @{text "(a + q - c) mod q"}) where @{const gsLayer} keeps @{text "z * (c - a)"} minus-free:
  @{text "(q - z)(a + q - c) = z(c - a) + q*(...)"}, an integer identity, so equal mod q.\<close>
lemma abs_inv_cong:
  fixes w b :: "[256][32]"
  assumes n: "n < 256" and Lpos: "0 < L"
      and coeff: "uint_seq (nth_seq b n) =
            (if n mod (2 * L) < L
             then (uint_seq (nth_seq w n) + uint_seq (nth_seq w (n + L))) mod 8380417
             else ((8380417 - uint_seq (nth_seq zetabrv (ZB - n div (2 * L)))) mod 8380417
                   * ((uint_seq (nth_seq w (n - L)) + 8380417 - uint_seq (nth_seq w n)) mod 8380417))
                  mod 8380417)"
  shows "cf b n mod 8380417 = gsLayer L ZB (cf w) n mod 8380417"
proof (cases "n mod (2 * L) < L")
  case True
  have l: "cf b n mod 8380417 = (cf w n + cf w (n + L)) mod 8380417"
    using coeff True by (simp add: cf_def)
  have r: "gsLayer L ZB (cf w) n mod 8380417 = (cf w n + cf w (n + L)) mod 8380417"
    using True by (simp add: gsLayer_def)
  show ?thesis using l r by simp
next
  case False
  define zb where "zb = uint_seq (nth_seq zetabrv (ZB - n div (2 * L)))"
  define av where "av = cf w (n - L)"
  define cv where "cv = cf w n"
  have eq: "(8380417 - zb) * (av + 8380417 - cv)
          = zb * (cv - av) + 8380417 * (av + 8380417 - cv - zb)"
    by (simp add: algebra_simps)
  have key: "cf b n mod 8380417 = (zb * (cv - av)) mod 8380417"
  proof -
    have "cf b n = ((8380417 - zb) mod 8380417 * ((av + 8380417 - cv) mod 8380417)) mod 8380417"
      using coeff False by (simp add: cf_def zb_def av_def cv_def)
    hence "cf b n mod 8380417
         = ((8380417 - zb) mod 8380417 * ((av + 8380417 - cv) mod 8380417)) mod 8380417" by simp
    also have "\<dots> = ((8380417 - zb) * (av + 8380417 - cv)) mod 8380417"
      by (metis mod_mult_eq)
    also have "\<dots> = (zb * (cv - av)) mod 8380417"
      by (subst eq) (rule mod_mult_self2)
    finally show ?thesis .
  qed
  have r: "gsLayer L ZB (cf w) n mod 8380417 = (zb * (cv - av)) mod 8380417"
    using False by (simp add: gsLayer_def zt_def zb_def cv_def av_def)
  show ?thesis using key r by simp
qed

text \<open>The eight instances. Each feeds @{text abs_inv_cong} the matching @{text invlayerN_coeff}
  unfold (@{text simp_all} bridges \<open>2*L\<close> to the concrete \<open>2len\<close>); level 7's constant index
  needs \<open>n div 256 = 0\<close>.\<close>
lemma abs_inv0:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 1 128 256 w) n mod 8380417 = gsLayer 1 255 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer0_coeff[OF n bw])
qed

lemma abs_inv1:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 2 64 128 w) n mod 8380417 = gsLayer 2 127 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer1_coeff[OF n bw])
qed

lemma abs_inv2:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 4 32 64 w) n mod 8380417 = gsLayer 4 63 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer2_coeff[OF n bw])
qed

lemma abs_inv3:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 8 16 32 w) n mod 8380417 = gsLayer 8 31 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer3_coeff[OF n bw])
qed

lemma abs_inv4:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 16 8 16 w) n mod 8380417 = gsLayer 16 15 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer4_coeff[OF n bw])
qed

lemma abs_inv5:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 32 4 8 w) n mod 8380417 = gsLayer 32 7 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer5_coeff[OF n bw])
qed

lemma abs_inv6:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 64 2 4 w) n mod 8380417 = gsLayer 64 3 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer6_coeff[OF n bw])
qed

lemma abs_inv7:
  fixes w :: "[256][32]"
  assumes bnd: "bounded w" and n: "n < 256"
  shows "cf (nttLayerInv 128 1 2 w) n mod 8380417 = gsLayer 128 1 (cf w) n mod 8380417"
proof -
  have bw: "\<And>i. i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417" using boundedD[OF bnd] by blast
  have nd: "n div 256 = 0" using n by simp
  show ?thesis by (rule abs_inv_cong[OF n]) (simp_all add: invlayer7_coeff[OF n bw] nd)
qed

end

section \<open>Per-layer R-preservation (the inverse pres chain)\<close>

text \<open>The inverse analog of Mont_Bridge's pres0..7: one Gentleman-Sande layer preserves
  the congruence relation @{const Rcong} between the montgomery model and the normal model.
  Generic over the layer: given the montgomery layer @{text mb} (== @{const gsLayer} on the sf
  view, from @{text mbfly_invN}) and the normal layer @{text ab} (== @{const gsLayer} on the cf
  view, from @{text abs_invN}), @{const gsLayer} respecting pointwise mod-q congruence
  (@{thm gsLayer_cong_g}) bridges the two. OOB indices (>= 256) fall to position 255 on both
  sides (@{thm oob255}).\<close>

context includes cryptol_syntax begin

lemma pres_inv_gen:
  fixes a w bb cc :: "[256][32]"
  assumes mb: "\<And>k. k < 256 \<Longrightarrow> sf bb k mod 8380417 = gsLayer L ZB (sf a) k mod 8380417"
      and ab: "\<And>k. k < 256 \<Longrightarrow> cf cc k mod 8380417 = gsLayer L ZB (cf w) k mod 8380417"
      and R: "Rcong a w"
  shows "Rcong bb cc"
proof -
  have Rg: "sf a m mod 8380417 = cf w m mod 8380417" for m using R by (simp add: Rcong_def)
  have main: "sf bb k mod 8380417 = cf cc k mod 8380417" if k: "k < 256" for k
  proof -
    have "sf bb k mod 8380417 = gsLayer L ZB (sf a) k mod 8380417" using mb[OF k] .
    also have "\<dots> = gsLayer L ZB (cf w) k mod 8380417" by (rule gsLayer_cong_g[OF Rg])
    also have "\<dots> = cf cc k mod 8380417" using ab[OF k] by simp
    finally show ?thesis .
  qed
  show ?thesis unfolding Rcong_def
  proof (intro allI)
    fix m show "sf bb m mod 8380417 = cf cc m mod 8380417"
    proof (cases "m < 256")
      case True thus ?thesis using main by simp
    next
      case False hence ge: "256 \<le> m" by simp
      show ?thesis using main[of 255] oob255[OF ge, of bb] oob255[OF ge, of cc]
        by (simp add: sf_def cf_def)
    qed
  qed
qed

lemma pres_inv0:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 0 a) (nttLayerInv 1 128 256 w)"
  by (rule pres_inv_gen[OF mbfly_inv0[OF B Bhi] abs_inv0[OF bw] R])

lemma pres_inv1:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 1 a) (nttLayerInv 2 64 128 w)"
  by (rule pres_inv_gen[OF mbfly_inv1[OF B Bhi] abs_inv1[OF bw] R])

lemma pres_inv2:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 2 a) (nttLayerInv 4 32 64 w)"
  by (rule pres_inv_gen[OF mbfly_inv2[OF B Bhi] abs_inv2[OF bw] R])

lemma pres_inv3:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 3 a) (nttLayerInv 8 16 32 w)"
  by (rule pres_inv_gen[OF mbfly_inv3[OF B Bhi] abs_inv3[OF bw] R])

lemma pres_inv4:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 4 a) (nttLayerInv 16 8 16 w)"
  by (rule pres_inv_gen[OF mbfly_inv4[OF B Bhi] abs_inv4[OF bw] R])

lemma pres_inv5:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 5 a) (nttLayerInv 32 4 8 w)"
  by (rule pres_inv_gen[OF mbfly_inv5[OF B Bhi] abs_inv5[OF bw] R])

lemma pres_inv6:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 6 a) (nttLayerInv 64 2 4 w)"
  by (rule pres_inv_gen[OF mbfly_inv6[OF B Bhi] abs_inv6[OF bw] R])

lemma pres_inv7:
  fixes a w :: "[256][32]"
  assumes B: "ntt_bounded BB a" and Bhi: "BB \<le> 1073741823" and bw: "bounded w" and R: "Rcong a w"
  shows "Rcong (invnttLevel 7 a) (nttLayerInv 128 1 2 w)"
  by (rule pres_inv_gen[OF mbfly_inv7[OF B Bhi] abs_inv7[OF bw] R])

end

text \<open>REMAINING (sub-step 2 tail + sub-step 3): the doubling bound-growth chain (an
  invnttLevel_bounded growth lemma: input ntt_bounded B, Q <= B ==> output ntt_bounded (2*B);
  thread B_ell = 2^ell * B_0, B_0 = 8380416 so 2^7 * B_0 = 1072693248 <= mbfly cap 1073741823);
  the bounded chain on the normal side (nttLayerInv preserves bounded); compose pres_inv0..7
  into Rcong (invntt-prefix) (nttInvAllRef), then the invf final scale (invf_scale_cong) and
  sub-step 1 + forward ntt_bridge into theorem invntt_bridge. Plus an inverse Negacyclic_Bridge
  (nttInvAllRef == FIPS inverse), inverse of fwd_ntt_correct.\<close>

end
