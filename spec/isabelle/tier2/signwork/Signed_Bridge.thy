theory Signed_Bridge
  imports "Tier2.Mont_Bridge"
begin

text \<open>Extends the forward transform theorem \<open>ntt_bridge\<close> from the non-negative \<open>[0,Q)\<close>
  window to the signed centered window \<open>|coeff| < Q\<close>, the inputs the reference forward NTT
  actually receives (keygen/sign feed centered \<open>s1\<close>, \<open>s2\<close> coefficients that can be negative).

  Route: the montgomery model \<open>ntt\<close> read on the SIGNED view \<open>sf\<close> equals the abstract \<open>fwdBfly\<close>
  transform of \<open>sf w\<close> mod q for any in-range input, then reuse the ABSTRACT closed form
  \<open>applyN_inv\<close> (which holds for any integer coefficient function, no non-negativity). The
  non-negativity in \<open>ntt_bridge\<close> entered only through \<open>Rcong_base\<close> (\<open>sf w = cf w\<close> needs
  \<open>sint = uint\<close>); here the base relation is \<open>sf w \<equiv> sf w\<close>, reflexive, so the restriction
  dissolves.\<close>

subsection \<open>A mod-q congruence for one abstract butterfly layer\<close>

text \<open>If two integer coefficient functions agree mod q on \<open>[0,256)\<close>, one \<open>bflyLayer\<close> maps them
  to functions that still agree mod q on \<open>[0,256)\<close>. \<open>part\<close> keeps the lower-leg partner
  \<open>n+L\<close> in range (needed since \<open>ag\<close> is stated only below 256); it holds for every stride
  \<open>L\<close> that divides 128 (all eight NTT layers).\<close>
lemma bflyLayer_cong_modq:
  fixes A B :: "nat \<Rightarrow> int"
  assumes part: "\<And>m. m < 256 \<Longrightarrow> m mod (2*L) < L \<Longrightarrow> m + L < 256"
    and ag: "\<forall>m. m < 256 \<longrightarrow> A m mod 8380417 = B m mod 8380417"
  shows "\<forall>n. n < 256 \<longrightarrow> bflyLayer L M0 A n mod 8380417 = bflyLayer L M0 B n mod 8380417"
proof (intro allI impI)
  fix n :: nat assume n: "n < 256"
  show "bflyLayer L M0 A n mod 8380417 = bflyLayer L M0 B n mod 8380417"
  proof (cases "n mod (2*L) < L")
    case True
    have pl: "n + L < 256" using part[OF n True] .
    have c0: "[A n = B n] (mod 8380417)" using ag n by (simp add: cong_def)
    have c1: "[A (n + L) = B (n + L)] (mod 8380417)" using ag pl by (simp add: cong_def)
    have "[A n + zt (n div (2*L) + M0 + 1) * A (n + L)
         = B n + zt (n div (2*L) + M0 + 1) * B (n + L)] (mod 8380417)"
      by (intro cong_add cong_mult cong_refl c0 c1)
    hence "(A n + zt (n div (2*L) + M0 + 1) * A (n + L)) mod 8380417
         = (B n + zt (n div (2*L) + M0 + 1) * B (n + L)) mod 8380417"
      by (simp add: cong_def)
    thus ?thesis using True by (simp add: bflyLayer_def mod_add_right_eq)
  next
    case False
    have nl: "n - L < 256" using n less_imp_diff_less by blast
    have c0: "[A n = B n] (mod 8380417)" using ag n by (simp add: cong_def)
    have c1: "[A (n - L) = B (n - L)] (mod 8380417)" using ag nl by (simp add: cong_def)
    have "[A (n - L) + 8380417 - zt (n div (2*L) + M0 + 1) * A n
         = B (n - L) + 8380417 - zt (n div (2*L) + M0 + 1) * B n] (mod 8380417)"
      by (intro cong_diff cong_add cong_mult cong_refl c0 c1)
    hence "(A (n - L) + 8380417 - zt (n div (2*L) + M0 + 1) * A n) mod 8380417
         = (B (n - L) + 8380417 - zt (n div (2*L) + M0 + 1) * B n) mod 8380417"
      by (simp add: cong_def)
    thus ?thesis using False by (simp add: bflyLayer_def mod_diff_right_eq)
  qed
qed

text \<open>Partner-in-range facts, one per stride used in a congruence step (\<open>L = 64..1\<close>).
  Proven by the block decomposition (\<open>presburger\<close> is pathologically slow on these): a
  position in the lower half of its \<open>2L\<close>-block plus \<open>L\<close> stays below 256 because
  \<open>2L\<close> divides 256. Each: \<open>m div (2L) < 256 div (2L)\<close> and \<open>m = (2L)(m div 2L) + m mod (2L)\<close>
  with \<open>m mod (2L) < L\<close>, closed by \<open>linarith\<close>.\<close>
lemma part_64: "m < 256 \<Longrightarrow> m mod (2*64) < 64 \<Longrightarrow> m + 64 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*64) < 64"
  have d: "m div 128 < 2" using a less_mult_imp_div_less[of m 2 128] by simp
  have e: "m div 128 * 128 + m mod 128 = m" by (rule div_mult_mod_eq)
  have f: "m mod 128 < 64" using b by simp
  from d e f show "m + 64 < 256" by linarith
qed
lemma part_32: "m < 256 \<Longrightarrow> m mod (2*32) < 32 \<Longrightarrow> m + 32 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*32) < 32"
  have d: "m div 64 < 4" using a less_mult_imp_div_less[of m 4 64] by simp
  have e: "m div 64 * 64 + m mod 64 = m" by (rule div_mult_mod_eq)
  have f: "m mod 64 < 32" using b by simp
  from d e f show "m + 32 < 256" by linarith
qed
lemma part_16: "m < 256 \<Longrightarrow> m mod (2*16) < 16 \<Longrightarrow> m + 16 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*16) < 16"
  have d: "m div 32 < 8" using a less_mult_imp_div_less[of m 8 32] by simp
  have e: "m div 32 * 32 + m mod 32 = m" by (rule div_mult_mod_eq)
  have f: "m mod 32 < 16" using b by simp
  from d e f show "m + 16 < 256" by linarith
qed
lemma part_8: "m < 256 \<Longrightarrow> m mod (2*8) < 8 \<Longrightarrow> m + 8 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*8) < 8"
  have d: "m div 16 < 16" using a less_mult_imp_div_less[of m 16 16] by simp
  have e: "m div 16 * 16 + m mod 16 = m" by (rule div_mult_mod_eq)
  have f: "m mod 16 < 8" using b by simp
  from d e f show "m + 8 < 256" by linarith
qed
lemma part_4: "m < 256 \<Longrightarrow> m mod (2*4) < 4 \<Longrightarrow> m + 4 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*4) < 4"
  have d: "m div 8 < 32" using a less_mult_imp_div_less[of m 32 8] by simp
  have e: "m div 8 * 8 + m mod 8 = m" by (rule div_mult_mod_eq)
  have f: "m mod 8 < 4" using b by simp
  from d e f show "m + 4 < 256" by linarith
qed
lemma part_2: "m < 256 \<Longrightarrow> m mod (2*2) < 2 \<Longrightarrow> m + 2 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*2) < 2"
  have d: "m div 4 < 64" using a less_mult_imp_div_less[of m 64 4] by simp
  have e: "m div 4 * 4 + m mod 4 = m" by (rule div_mult_mod_eq)
  have f: "m mod 4 < 2" using b by simp
  from d e f show "m + 2 < 256" by linarith
qed
lemma part_1: "m < 256 \<Longrightarrow> m mod (2*1) < 1 \<Longrightarrow> m + 1 < (256::nat)"
proof -
  assume a: "m < 256" and b: "m mod (2*1) < 1"
  have d: "m div 2 < 128" using a less_mult_imp_div_less[of m 128 2] by simp
  have e: "m div 2 * 2 + m mod 2 = m" by (rule div_mult_mod_eq)
  have f: "m mod 2 < 1" using b by simp
  from d e f show "m + 1 < 256" by linarith
qed

subsection \<open>The montgomery NTT on the signed view equals the abstract transform\<close>

context includes cryptol_syntax begin

declare [[coercion_enabled = false]]

text \<open>The signed-view analogue of \<open>ntt_bridge\<close>'s \<open>Rcong\<close> chain, but propagating
  \<open>sf(montgomery layer) \<equiv> bflyLayer(sf w) (mod q)\<close> instead of the montgomery-vs-normal-model
  relation. The base is reflexive, so no non-negativity is used; each step is \<open>mbfly_i\<close>
  (already stated on \<open>sf\<close>) composed with \<open>bflyLayer_cong_modq\<close>, and the bound chain
  \<open>nb0..nb7\<close> is identical to \<open>ntt_bridge\<close>'s.\<close>
lemma sf_ntt_eq_fwdbfly:
  assumes bnd: "ntt_bounded 8380416 w"
  shows "\<forall>n. n < 256 \<longrightarrow> sf (ntt w) n mod 8380417 = fwdBfly (sf w) n mod 8380417"
proof -
  \<comment> \<open>bound chain: ntt_bounded grows by q each layer (as in ntt_bridge)\<close>
  have nb0: "ntt_bounded 8380416 w" by (rule bnd)
  have nb1: "ntt_bounded 16760833 (nttLevel 0 w)" using nttLevel_bounded[OF nb0] by simp
  have nb2: "ntt_bounded 25141250 (nttLevel 1 (nttLevel 0 w))" using nttLevel_bounded[OF nb1] by simp
  have nb3: "ntt_bounded 33521667 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))" using nttLevel_bounded[OF nb2] by simp
  have nb4: "ntt_bounded 41902084 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))" using nttLevel_bounded[OF nb3] by simp
  have nb5: "ntt_bounded 50282501 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))" using nttLevel_bounded[OF nb4] by simp
  have nb6: "ntt_bounded 58662918 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))))" using nttLevel_bounded[OF nb5] by simp
  have nb7: "ntt_bounded 67043335 (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))))" using nttLevel_bounded[OF nb6] by simp
  \<comment> \<open>congruence chain: sf(i-fold nttLevel) == i-fold bflyLayer on sf w, mod q\<close>
  have S1: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 0 w) n mod 8380417 = bflyLayer 128 0 (sf w) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    show "sf (nttLevel 0 w) n mod 8380417 = bflyLayer 128 0 (sf w) n mod 8380417"
      by (rule mbfly0[OF nb0 _ n]) simp
  qed
  have S2: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 1 (nttLevel 0 w)) n mod 8380417
                          = bflyLayer 64 1 (bflyLayer 128 0 (sf w)) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (nttLevel 1 (nttLevel 0 w)) n mod 8380417 = bflyLayer 64 1 (sf (nttLevel 0 w)) n mod 8380417"
      by (rule mbfly1[OF nb1 _ n]) simp
    also have "\<dots> = bflyLayer 64 1 (bflyLayer 128 0 (sf w)) n mod 8380417"
      using bflyLayer_cong_modq[OF part_64 S1] n by blast
    finally show "sf (nttLevel 1 (nttLevel 0 w)) n mod 8380417
                = bflyLayer 64 1 (bflyLayer 128 0 (sf w)) n mod 8380417" .
  qed
  have S3: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 2 (nttLevel 1 (nttLevel 0 w))) n mod 8380417
                          = bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (nttLevel 2 (nttLevel 1 (nttLevel 0 w))) n mod 8380417 = bflyLayer 32 3 (sf (nttLevel 1 (nttLevel 0 w))) n mod 8380417"
      by (rule mbfly2[OF nb2 _ n]) simp
    also have "\<dots> = bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))) n mod 8380417"
      using bflyLayer_cong_modq[OF part_32 S2] n by blast
    finally show "sf (nttLevel 2 (nttLevel 1 (nttLevel 0 w))) n mod 8380417
                = bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))) n mod 8380417" .
  qed
  have S4: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))) n mod 8380417
                          = bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))) n mod 8380417 = bflyLayer 16 7 (sf (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))) n mod 8380417"
      by (rule mbfly3[OF nb3 _ n]) simp
    also have "\<dots> = bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))) n mod 8380417"
      using bflyLayer_cong_modq[OF part_16 S3] n by blast
    finally show "sf (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))) n mod 8380417
                = bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))) n mod 8380417" .
  qed
  have S5: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))) n mod 8380417
                          = bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))) n mod 8380417 = bflyLayer 8 15 (sf (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))) n mod 8380417"
      by (rule mbfly4[OF nb4 _ n]) simp
    also have "\<dots> = bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))))) n mod 8380417"
      using bflyLayer_cong_modq[OF part_8 S4] n by blast
    finally show "sf (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))) n mod 8380417
                = bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))))) n mod 8380417" .
  qed
  have S6: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))) n mod 8380417
                          = bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))) n mod 8380417 = bflyLayer 4 31 (sf (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))) n mod 8380417"
      by (rule mbfly5[OF nb5 _ n]) simp
    also have "\<dots> = bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))))) n mod 8380417"
      using bflyLayer_cong_modq[OF part_4 S5] n by blast
    finally show "sf (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))) n mod 8380417
                = bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))))) n mod 8380417" .
  qed
  have S7: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))))) n mod 8380417
                          = bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))))) n mod 8380417 = bflyLayer 2 63 (sf (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))))) n mod 8380417"
      by (rule mbfly6[OF nb6 _ n]) simp
    also have "\<dots> = bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))))))) n mod 8380417"
      using bflyLayer_cong_modq[OF part_2 S6] n by blast
    finally show "sf (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w))))))) n mod 8380417
                = bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w))))))) n mod 8380417" .
  qed
  have S8: "\<forall>n. n < 256 \<longrightarrow> sf (nttLevel 7 (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))))) n mod 8380417
                          = bflyLayer 1 127 (bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))))))) n mod 8380417"
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (nttLevel 7 (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))))) n mod 8380417 = bflyLayer 1 127 (sf (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))))) n mod 8380417"
      by (rule mbfly7[OF nb7 _ n]) simp
    also have "\<dots> = bflyLayer 1 127 (bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))))))) n mod 8380417"
      using bflyLayer_cong_modq[OF part_1 S7] n by blast
    finally show "sf (nttLevel 7 (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))))) n mod 8380417
                = bflyLayer 1 127 (bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))))))) n mod 8380417" .
  qed
  show ?thesis
  proof (intro allI impI)
    fix n :: nat assume n: "n < 256"
    have "sf (ntt w) n mod 8380417
        = sf (nttLevel 7 (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 w)))))))) n mod 8380417"
      by (simp add: ntt_unfold)
    also have "\<dots> = bflyLayer 1 127 (bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (sf w)))))))) n mod 8380417"
      using S8 n by blast
    also have "\<dots> = fwdBfly (sf w) n mod 8380417"
      by (simp add: fwdBfly_def)
    finally show "sf (ntt w) n mod 8380417 = fwdBfly (sf w) n mod 8380417" .
  qed
qed

subsection \<open>Signed-window forward NTT correctness\<close>

text \<open>The forward transform theorem on the signed centered window \<open>|coeff| < Q\<close>
  (\<open>ntt_bounded 8380416 w\<close>): the montgomery model \<open>ntt\<close> (the same model SAW checks the C
  against) computes, at output position \<open>k\<close>, the FIPS-204 negacyclic DFT of the SIGNED
  coefficient values \<open>sf w\<close> at the bit-reversed index \<open>brv 8 k\<close>. Unlike \<open>ntt_bridge\<close>, no
  non-negativity is required; the input reading is the signed one throughout.\<close>
theorem ntt_signed_correct:
  assumes bnd: "ntt_bounded 8380416 w" and k: "k < 256"
  shows "sint_seq (nth_seq (ntt w) k) mod 8380417
       = (\<Sum>j<256. sf w j * 1753 ^ ((2 * brv 8 k + 1) * j)) mod 8380417"
proof -
  have step: "sf (ntt w) k mod 8380417 = fwdBfly (sf w) k mod 8380417"
    using sf_ntt_eq_fwdbfly[OF bnd] k by blast
  have ai: "[applyN 8 (sf w) k = inv_form 8 (sf w) k] (mod qq)"
    using applyN_inv[of 8 "sf w"] k by simp
  have fb: "fwdBfly (sf w) k mod 8380417 = inv_form 8 (sf w) k mod 8380417"
    using ai by (simp add: applyN_8_eq_fwdBfly cong_def)
  have "sint_seq (nth_seq (ntt w) k) mod 8380417 = fwdBfly (sf w) k mod 8380417"
    using step by (simp add: sf_def)
  also have "\<dots> = inv_form 8 (sf w) k mod 8380417" by (rule fb)
  also have "\<dots> = (\<Sum>j<256. sf w j * 1753 ^ ((2 * brv 8 k + 1) * j)) mod 8380417"
    by (simp add: inv_form_8)
  finally show ?thesis .
qed

end

end
