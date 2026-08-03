theory Inv_Signed_Bridge
  imports "Tier2_InvWork.Inv_Mont_Bridge"
begin

text \<open>Inverse mirror of \<open>Signed_Bridge.ntt_signed_correct\<close>: lifts the FUNCTIONAL inverse
  transform theorem from the non-negative \<open>[0,Q)\<close> window (\<open>invntt_bridge\<close>, \<open>bounded w\<close>) to the
  signed centered window \<open>|coeff| < Q\<close> (\<open>ntt_bounded 8380416 w\<close>), the inputs the deployed
  \<open>invntt_tomont\<close> call site actually receives.

  The inverse has the same shape as the forward plus a final montgomery scale by \<open>invf\<close>.
  \<open>invntt_scale_bridge\<close> splits into (i) a SIGN-AGNOSTIC scale part
  (\<open>invntt_scale_coeff\<close> + \<open>invf_scale_cong\<close>: \<open>2^32 * sf(invntt w) \<equiv> invf * sf(invnttCore w)\<close>) and
  (ii) one \<open>[0,Q)\<close>-locked step (\<open>Rcong_invcore\<close>: \<open>sf(invnttCore w) \<equiv> cf(nttInvAllRef w) mod q\<close>).
  We keep (i) verbatim and replace (ii) with the abstract route: the closed form \<open>applyG_inv\<close>
  holds for ANY integer coefficient function, and \<open>mbfly_inv0..7\<close> already land on the signed view
  \<open>sf\<close>, so propagating \<open>sf(invnttCore w) \<equiv> invBfly(sf w) (mod q)\<close> with a REFLEXIVE base
  dissolves the non-negativity.\<close>

subsection \<open>A mod-q congruence for one abstract Gentleman-Sande layer\<close>

lemma gsLayer_cong_modq:
  fixes A B :: "nat \<Rightarrow> int"
  assumes part: "\<And>m. m < 256 \<Longrightarrow> m mod (2*L) < L \<Longrightarrow> m + L < 256"
    and ag: "\<forall>m. m < 256 \<longrightarrow> A m mod 8380417 = B m mod 8380417"
  shows "\<forall>n. n < 256 \<longrightarrow> gsLayer L ZB A n mod 8380417 = gsLayer L ZB B n mod 8380417"
proof (intro allI impI)
  fix n :: nat assume n: "n < 256"
  show "gsLayer L ZB A n mod 8380417 = gsLayer L ZB B n mod 8380417"
  proof (cases "n mod (2*L) < L")
    case True
    have pl: "n + L < 256" using part[OF n True] .
    have c0: "[A n = B n] (mod 8380417)" using ag n by (simp add: cong_def)
    have c1: "[A (n + L) = B (n + L)] (mod 8380417)" using ag pl by (simp add: cong_def)
    have "[A n + A (n + L) = B n + B (n + L)] (mod 8380417)" by (intro cong_add c0 c1)
    hence "(A n + A (n + L)) mod 8380417 = (B n + B (n + L)) mod 8380417" by (simp add: cong_def)
    thus ?thesis using True by (simp add: gsLayer_def)
  next
    case False
    have nl: "n - L < 256" using n less_imp_diff_less by blast
    have c0: "[A n = B n] (mod 8380417)" using ag n by (simp add: cong_def)
    have c1: "[A (n - L) = B (n - L)] (mod 8380417)" using ag nl by (simp add: cong_def)
    have "[zt (ZB - n div (2*L)) * (A n - A (n - L))
         = zt (ZB - n div (2*L)) * (B n - B (n - L))] (mod 8380417)"
      by (intro cong_mult cong_refl cong_diff c0 c1)
    hence "(zt (ZB - n div (2*L)) * (A n - A (n - L))) mod 8380417
         = (zt (ZB - n div (2*L)) * (B n - B (n - L))) mod 8380417" by (simp add: cong_def)
    thus ?thesis using False by (simp add: gsLayer_def)
  qed
qed

text \<open>Partner-in-range facts for the strides used in the inverse congruence steps
  (\<open>L = 2..128\<close>; the level-0 step \<open>L = 1\<close> is direct \<open>mbfly_inv0\<close>, no congruence). Same block
  decomposition as the forward \<open>part_*\<close> facts (presburger is pathologically slow here).\<close>
lemma part_2: "m < 256 \<Longrightarrow> m mod (2*2) < 2 \<Longrightarrow> m + 2 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*2) < 2"
  have d: "m div 4 < 64" using a less_mult_imp_div_less[of m 64 4] by simp
  have e: "m div 4 * 4 + m mod 4 = m" by (rule div_mult_mod_eq)
  have f: "m mod 4 < 2" using b by simp
  from d e f show "m + 2 < 256" by linarith
qed
lemma part_4: "m < 256 \<Longrightarrow> m mod (2*4) < 4 \<Longrightarrow> m + 4 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*4) < 4"
  have d: "m div 8 < 32" using a less_mult_imp_div_less[of m 32 8] by simp
  have e: "m div 8 * 8 + m mod 8 = m" by (rule div_mult_mod_eq)
  have f: "m mod 8 < 4" using b by simp
  from d e f show "m + 4 < 256" by linarith
qed
lemma part_8: "m < 256 \<Longrightarrow> m mod (2*8) < 8 \<Longrightarrow> m + 8 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*8) < 8"
  have d: "m div 16 < 16" using a less_mult_imp_div_less[of m 16 16] by simp
  have e: "m div 16 * 16 + m mod 16 = m" by (rule div_mult_mod_eq)
  have f: "m mod 16 < 8" using b by simp
  from d e f show "m + 8 < 256" by linarith
qed
lemma part_16: "m < 256 \<Longrightarrow> m mod (2*16) < 16 \<Longrightarrow> m + 16 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*16) < 16"
  have d: "m div 32 < 8" using a less_mult_imp_div_less[of m 8 32] by simp
  have e: "m div 32 * 32 + m mod 32 = m" by (rule div_mult_mod_eq)
  have f: "m mod 32 < 16" using b by simp
  from d e f show "m + 16 < 256" by linarith
qed
lemma part_32: "m < 256 \<Longrightarrow> m mod (2*32) < 32 \<Longrightarrow> m + 32 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*32) < 32"
  have d: "m div 64 < 4" using a less_mult_imp_div_less[of m 4 64] by simp
  have e: "m div 64 * 64 + m mod 64 = m" by (rule div_mult_mod_eq)
  have f: "m mod 64 < 32" using b by simp
  from d e f show "m + 32 < 256" by linarith
qed
lemma part_64: "m < 256 \<Longrightarrow> m mod (2*64) < 64 \<Longrightarrow> m + 64 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*64) < 64"
  have d: "m div 128 < 2" using a less_mult_imp_div_less[of m 2 128] by simp
  have e: "m div 128 * 128 + m mod 128 = m" by (rule div_mult_mod_eq)
  have f: "m mod 128 < 64" using b by simp
  from d e f show "m + 64 < 256" by linarith
qed
lemma part_128: "m < 256 \<Longrightarrow> m mod (2*128) < 128 \<Longrightarrow> m + 128 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*128) < 128"
  have d: "m div 256 < 1" using a less_mult_imp_div_less[of m 1 256] by simp
  have e: "m div 256 * 256 + m mod 256 = m" by (rule div_mult_mod_eq)
  have f: "m mod 256 < 128" using b by simp
  from d e f show "m + 128 < 256" by linarith
qed

subsection \<open>The montgomery inverse core on the signed view equals the abstract GS transform\<close>

context includes cryptol_syntax begin

declare [[coercion_enabled = false]]

text \<open>Mirror of \<open>Signed_Bridge.sf_ntt_eq_fwdbfly\<close> for the inverse core (the eight GS layers
  before the \<open>invf\<close> scale). Bound chain is the doubling one (\<open>invcore_bounded_nb\<close>), each step is
  \<open>mbfly_inv_i\<close> composed with \<open>gsLayer_cong_modq\<close>, base is reflexive.\<close>
lemma sf_invcore_eq_invbfly:
  assumes bnd: "ntt_bounded 8380416 w"
  shows "\<forall>n. n < 256 \<longrightarrow> sf (invnttCore w) n mod 8380417 = invBfly (sf w) n mod 8380417"
proof -
  \<comment> \<open>bound chain: the inverse doubles the magnitude bound per layer\<close>
  have nb0: "ntt_bounded 8380416 w" by (rule bnd)
  have nb1: "ntt_bounded 16760832 (invnttLevel 0 w)" using invlevel0_bounded[OF nb0] by simp
  have nb2: "ntt_bounded 33521664 (invnttLevel 1 (invnttLevel 0 w))" using invlevel1_bounded[OF nb1] by simp
  have nb3: "ntt_bounded 67043328 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))" using invlevel2_bounded[OF nb2] by simp
  have nb4: "ntt_bounded 134086656 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))" using invlevel3_bounded[OF nb3] by simp
  have nb5: "ntt_bounded 268173312 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))" using invlevel4_bounded[OF nb4] by simp
  have nb6: "ntt_bounded 536346624 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))))" using invlevel5_bounded[OF nb5] by simp
  have nb7: "ntt_bounded 1072693248 (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))))" using invlevel6_bounded[OF nb6] by simp
  \<comment> \<open>congruence chain: sf(i-fold invnttLevel) == i-fold gsLayer on sf w, mod q\<close>
  have S1: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 0 w) n mod 8380417 = gsLayer 1 255 (sf w) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    show "sf (invnttLevel 0 w) n mod 8380417 = gsLayer 1 255 (sf w) n mod 8380417"
      by (rule mbfly_inv0[OF nb0 _ n]) simp
  qed
  have S2: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 1 (invnttLevel 0 w)) n mod 8380417
                          = gsLayer 2 127 (gsLayer 1 255 (sf w)) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttLevel 1 (invnttLevel 0 w)) n mod 8380417 = gsLayer 2 127 (sf (invnttLevel 0 w)) n mod 8380417"
      by (rule mbfly_inv1[OF nb1 _ n]) simp
    also have "\<dots> = gsLayer 2 127 (gsLayer 1 255 (sf w)) n mod 8380417"
      using gsLayer_cong_modq[OF part_2 S1] n by blast
    finally show "sf (invnttLevel 1 (invnttLevel 0 w)) n mod 8380417
                = gsLayer 2 127 (gsLayer 1 255 (sf w)) n mod 8380417" .
  qed
  have S3: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))) n mod 8380417
                          = gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))) n mod 8380417 = gsLayer 4 63 (sf (invnttLevel 1 (invnttLevel 0 w))) n mod 8380417"
      by (rule mbfly_inv2[OF nb2 _ n]) simp
    also have "\<dots> = gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))) n mod 8380417"
      using gsLayer_cong_modq[OF part_4 S2] n by blast
    finally show "sf (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))) n mod 8380417
                = gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))) n mod 8380417" .
  qed
  have S4: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))) n mod 8380417
                          = gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))) n mod 8380417 = gsLayer 8 31 (sf (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))) n mod 8380417"
      by (rule mbfly_inv3[OF nb3 _ n]) simp
    also have "\<dots> = gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))) n mod 8380417"
      using gsLayer_cong_modq[OF part_8 S3] n by blast
    finally show "sf (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))) n mod 8380417
                = gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))) n mod 8380417" .
  qed
  have S5: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))) n mod 8380417
                          = gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))) n mod 8380417 = gsLayer 16 15 (sf (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))) n mod 8380417"
      by (rule mbfly_inv4[OF nb4 _ n]) simp
    also have "\<dots> = gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))))) n mod 8380417"
      using gsLayer_cong_modq[OF part_16 S4] n by blast
    finally show "sf (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))) n mod 8380417
                = gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))))) n mod 8380417" .
  qed
  have S6: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))) n mod 8380417
                          = gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))) n mod 8380417 = gsLayer 32 7 (sf (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))) n mod 8380417"
      by (rule mbfly_inv5[OF nb5 _ n]) simp
    also have "\<dots> = gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))))) n mod 8380417"
      using gsLayer_cong_modq[OF part_32 S5] n by blast
    finally show "sf (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))) n mod 8380417
                = gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))))) n mod 8380417" .
  qed
  have S7: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))))) n mod 8380417
                          = gsLayer 64 3 (gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))))) n mod 8380417 = gsLayer 64 3 (sf (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))))) n mod 8380417"
      by (rule mbfly_inv6[OF nb6 _ n]) simp
    also have "\<dots> = gsLayer 64 3 (gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))))))) n mod 8380417"
      using gsLayer_cong_modq[OF part_64 S6] n by blast
    finally show "sf (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w))))))) n mod 8380417
                = gsLayer 64 3 (gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w))))))) n mod 8380417" .
  qed
  have S8: "\<forall>n. n < 256 \<longrightarrow> sf (invnttLevel 7 (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))))) n mod 8380417
                          = gsLayer 128 1 (gsLayer 64 3 (gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttLevel 7 (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))))) n mod 8380417 = gsLayer 128 1 (sf (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))))) n mod 8380417"
      by (rule mbfly_inv7[OF nb7 _ n]) simp
    also have "\<dots> = gsLayer 128 1 (gsLayer 64 3 (gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))))))) n mod 8380417"
      using gsLayer_cong_modq[OF part_128 S7] n by blast
    finally show "sf (invnttLevel 7 (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))))) n mod 8380417
                = gsLayer 128 1 (gsLayer 64 3 (gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))))))) n mod 8380417" .
  qed
  show ?thesis
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (invnttCore w) n mod 8380417
        = sf (invnttLevel 7 (invnttLevel 6 (invnttLevel 5 (invnttLevel 4 (invnttLevel 3 (invnttLevel 2 (invnttLevel 1 (invnttLevel 0 w)))))))) n mod 8380417"
      by (simp add: invnttCore_def)
    also have "\<dots> = gsLayer 128 1 (gsLayer 64 3 (gsLayer 32 7 (gsLayer 16 15 (gsLayer 8 31 (gsLayer 4 63 (gsLayer 2 127 (gsLayer 1 255 (sf w)))))))) n mod 8380417"
      using S8 n by blast
    also have "\<dots> = invBfly (sf w) n mod 8380417"
      by (simp add: invBfly_def)
    finally show "sf (invnttCore w) n mod 8380417 = invBfly (sf w) n mod 8380417" .
  qed
qed

subsection \<open>Signed-window inverse NTT correctness\<close>

text \<open>The inverse transform theorem on the signed centered window \<open>|coeff| < Q\<close>: the montgomery
  model \<open>invntt\<close> (the model SAW checks the C \<open>invntt_tomont\<close> against), montgomery-scaled by
  \<open>invf = mont^2/256\<close>, computes the FIPS-204 inverse negacyclic DFT of the SIGNED coefficient values
  \<open>sf w\<close>. Same statement as \<open>invntt_bridge\<close> but with \<open>cf w m\<close> replaced by the signed \<open>sf w m\<close>,
  under \<open>ntt_bounded 8380416 w\<close> instead of \<open>bounded w\<close>.\<close>
theorem invntt_signed_correct:
  assumes bnd: "ntt_bounded 8380416 w" and k: "k < 256"
  shows "(4294967296 * sint_seq (nth_seq (invntt w) k)) mod 8380417
       = (sint_seq invf * (\<Sum>m<256. sf w m * zpw (- (2 * int (brv 8 m) + 1) * int k))) mod 8380417"
proof -
  have cb: "- 2145386496 \<le> sint_seq (nth_seq (invnttCore w) k)"
           "sint_seq (nth_seq (invnttCore w) k) \<le> 2145386496"
    using invcore_bounded_nb[OF bnd] unfolding ntt_bounded_def by auto
  have ivb: "- 4194304 \<le> sint_seq invf" "sint_seq invf \<le> 4194304" using invf_sint_bound by auto
  have ok: "mont_input_ok (sint_seq invf * sint_seq (nth_seq (invnttCore w) k))"
    by (rule mont_input_ok_of_bounds'[OF ivb(1) ivb(2) cb(1) cb(2)]) simp
  have sc: "(4294967296 * sint_seq (montgomery_reduce (sext64 invf
              * sext64 (nth_seq (invnttCore w) k)))) mod 8380417
          = (sint_seq invf * sint_seq (nth_seq (invnttCore w) k)) mod 8380417"
    by (rule invf_scale_cong[OF ok])
  have corek: "sf (invnttCore w) k mod 8380417 = invBfly (sf w) k mod 8380417"
    using sf_invcore_eq_invbfly[OF bnd] k by blast
  have ag: "invBfly (sf w) k mod 8380417 = ginv_form 8 (sf w) k mod 8380417"
  proof -
    have "[applyG 8 (sf w) k = ginv_form 8 (sf w) k] (mod 8380417)"
      using applyG_inv[of 8 "sf w"] k by simp
    thus ?thesis by (simp add: applyG_8_eq_invBfly cong_def)
  qed
  have gf: "ginv_form 8 (sf w) k = (\<Sum>m<256. sf w m * zpw (- (2 * int (brv 8 m) + 1) * int k))"
    by (rule ginv_form_8[OF k])
  have "(4294967296 * sint_seq (nth_seq (invntt w) k)) mod 8380417
      = (4294967296 * sint_seq (montgomery_reduce (sext64 invf
           * sext64 (nth_seq (invnttCore w) k)))) mod 8380417"
    by (simp add: invntt_scale_coeff[OF k])
  also have "\<dots> = (sint_seq invf * sint_seq (nth_seq (invnttCore w) k)) mod 8380417" by (rule sc)
  also have "\<dots> = (sint_seq invf * sf (invnttCore w) k) mod 8380417" by (simp add: sf_def)
  also have "\<dots> = (sint_seq invf * invBfly (sf w) k) mod 8380417"
    by (rule mod_mult_cong[OF refl corek])
  also have "\<dots> = (sint_seq invf * ginv_form 8 (sf w) k) mod 8380417"
    by (rule mod_mult_cong[OF refl ag])
  also have "\<dots> = (sint_seq invf * (\<Sum>m<256. sf w m * zpw (- (2 * int (brv 8 m) + 1) * int k))) mod 8380417"
    by (simp add: gf)
  finally show ?thesis .
qed

end

end
