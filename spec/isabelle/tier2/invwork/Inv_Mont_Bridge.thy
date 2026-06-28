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

end

text \<open>REMAINING (sub-step 2 bulk + sub-step 3): invlevel0_hi/coeff, the 7 further levels,
  the per-layer congruences (mirror mbfly0..7 via inv_butterfly_cong + the no-overflow
  add/sub lifts), range preservation (mirror pres0..7), the invf final scale, then compose
  with sub-step 1 and the forward ntt_bridge into theorem invntt_bridge.\<close>

end
