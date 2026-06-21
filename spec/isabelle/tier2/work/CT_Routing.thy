(* Tier-2 CT routing (WIP): lift the 8 proven per-layer butterfly laws
   (Bridge_Word.layer*_coeff) to an int-coefficient view, then compose them via
   fwd_unfold into a single 8-fold abstract-butterfly transform. This decouples
   the word-level seam (done) from the combinatorial bit-reversal / NNTT argument
   (next), which can then run purely on the abstract `bflyLayer`. *)
theory CT_Routing
  imports "Tier2_Base.Bridge_Word"
begin

context includes cryptol_translation_syntax begin

text \<open>Int-coefficient view of a lifted 256-vector, and the twiddle table as an
  int function. Coefficients live in [0,q).\<close>
definition cf :: "[256][32] \<Rightarrow> nat \<Rightarrow> int" where
  "cf w n = uint_seq (nth_seq w n)"

definition zt :: "nat \<Rightarrow> int" where
  "zt j = uint_seq (nth_seq zetabrv j)"

definition bounded :: "[256][32] \<Rightarrow> bool" where
  "bounded w \<longleftrightarrow> (\<forall>i<256. uint_seq (nth_seq w i) < 8380417)"

text \<open>One abstract Cooley-Tukey layer on an int-coefficient function. Params:
  stride \<open>L\<close> and twiddle base \<open>M0\<close> (the \<open>m0\<close> of the lifted layer). Lower half is
  the additive leg, upper half the subtractive leg; twiddle index \<open>n div (2L) + M0+1\<close>.\<close>
definition bflyLayer :: "nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
  "bflyLayer L M0 g = (\<lambda>n.
     if n mod (2*L) < L
     then (g n + zt (n div (2*L) + M0 + 1) * g (n + L) mod 8380417) mod 8380417
     else (g (n - L) + 8380417
           - zt (n div (2*L) + M0 + 1) * g n mod 8380417) mod 8380417)"

text \<open>Every abstract-layer output is a valid coefficient: both legs end in \<open>mod q\<close>.\<close>
lemma bflyLayer_lt: "bflyLayer L M0 g n < 8380417"
  by (simp add: bflyLayer_def)

lemma bflyLayer_ge: "0 \<le> bflyLayer L M0 g n"
  by (simp add: bflyLayer_def)

text \<open>Drawing the per-index coefficient bound out of \<open>bounded\<close>.\<close>
lemma boundedD: "bounded w \<Longrightarrow> i < 256 \<Longrightarrow> uint_seq (nth_seq w i) < 8380417"
  by (simp add: bounded_def)

subsection \<open>Per-layer abstraction: each lifted layer = one abstract butterfly\<close>

text \<open>Layer with stride 128 (m0=0): \<open>n div 256 = 0\<close> so the twiddle index is 1 and
  the half-test \<open>n mod 256 < 128\<close> is just \<open>n < 128\<close>.\<close>
lemma abs_128:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 128 1 0 w) n = bflyLayer 128 0 (cf w) n"
  using layer1_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute)

lemma abs_64:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 64 2 1 w) n = bflyLayer 64 1 (cf w) n"
  using layer2_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute)

lemma abs_32:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 32 4 3 w) n = bflyLayer 32 3 (cf w) n"
  using layer3_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute)

lemma abs_16:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 16 8 7 w) n = bflyLayer 16 7 (cf w) n"
  using layer_16_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute)

lemma abs_8:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 8 16 15 w) n = bflyLayer 8 15 (cf w) n"
  using layer_8_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute)

lemma abs_4:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 4 32 31 w) n = bflyLayer 4 31 (cf w) n"
  using layer_4_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute)

lemma abs_2:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 2 64 63 w) n = bflyLayer 2 63 (cf w) n"
  using layer_2_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute)

lemma abs_1:
  assumes "bounded w" and "n < 256"
  shows "cf (nttLayerFwd 1 128 127 w) n = bflyLayer 1 127 (cf w) n"
  using layer_1_coeff[OF assms(2) boundedD[OF assms(1)]] assms(2)
  by (simp add: cf_def zt_def bflyLayer_def add.commute numeral_2_eq_2)

subsection \<open>Bound preservation: a lifted layer keeps coefficients in [0,q)\<close>

lemma bounded_128: "bounded w \<Longrightarrow> bounded (nttLayerFwd 128 1 0 w)"
  by (simp add: bounded_def) (metis abs_128 bflyLayer_lt cf_def bounded_def)

lemma bounded_64: "bounded w \<Longrightarrow> bounded (nttLayerFwd 64 2 1 w)"
  by (simp add: bounded_def) (metis abs_64 bflyLayer_lt cf_def bounded_def)

lemma bounded_32: "bounded w \<Longrightarrow> bounded (nttLayerFwd 32 4 3 w)"
  by (simp add: bounded_def) (metis abs_32 bflyLayer_lt cf_def bounded_def)

lemma bounded_16: "bounded w \<Longrightarrow> bounded (nttLayerFwd 16 8 7 w)"
  by (simp add: bounded_def) (metis abs_16 bflyLayer_lt cf_def bounded_def)

lemma bounded_8: "bounded w \<Longrightarrow> bounded (nttLayerFwd 8 16 15 w)"
  by (simp add: bounded_def) (metis abs_8 bflyLayer_lt cf_def bounded_def)

lemma bounded_4: "bounded w \<Longrightarrow> bounded (nttLayerFwd 4 32 31 w)"
  by (simp add: bounded_def) (metis abs_4 bflyLayer_lt cf_def bounded_def)

lemma bounded_2: "bounded w \<Longrightarrow> bounded (nttLayerFwd 2 64 63 w)"
  by (simp add: bounded_def) (metis abs_2 bflyLayer_lt cf_def bounded_def)

subsection \<open>Composition target (NEXT): the full lifted forward NTT as one
  8-fold abstract-butterfly transform.\<close>

definition fwdBfly :: "(nat \<Rightarrow> int) \<Rightarrow> (nat \<Rightarrow> int)" where
  "fwdBfly = bflyLayer 1 127 \<circ> bflyLayer 2 63 \<circ> bflyLayer 4 31 \<circ> bflyLayer 8 15
           \<circ> bflyLayer 16 7 \<circ> bflyLayer 32 3 \<circ> bflyLayer 64 1 \<circ> bflyLayer 128 0"

end \<comment> \<open>close cryptol_translation_syntax: the routing lemmas below are pure
  nat/int reasoning.\<close>

text \<open>The Cryptol setup leaves automatic coercion insertion globally enabled,
  which makes \<open>f m\<close> accept a coercible \<open>m\<close> and so defeats the \<open>nat\<close> typing of the
  bounded quantifiers below (\<open>\<forall>m<256\<close>). Disable it: these lemmas are pure nat/int.\<close>
declare [[coercion_enabled = false]]

text \<open>Transitivity of agreement on positions below 256.\<close>
lemma agree_trans:
  fixes f g h :: "nat \<Rightarrow> int"
  assumes "\<forall>m. (m::nat) < 256 \<longrightarrow> f m = g m" and "\<forall>m. (m::nat) < 256 \<longrightarrow> g m = h m"
  shows "\<forall>m. (m::nat) < 256 \<longrightarrow> f m = h m"
proof (intro allI impI)
  fix m :: nat assume m: "m < 256"
  from assms(1) m have "f m = g m" by blast
  moreover from assms(2) m have "g m = h m" by blast
  ultimately show "f m = h m" by simp
qed

text \<open>Agree-below-256 congruence for one abstract layer. A layer reads its input
  only at \<open>n\<close>, \<open>n+L\<close> (lower leg) and \<open>n-L\<close> (upper leg). \<open>n-L \<le> n < 256\<close> is free;
  the lower-leg partner bound \<open>n+L < 256\<close> is the only side condition, discharged
  per concrete stride by \<open>presburger\<close>.\<close>
lemma bflyLayer_cong:
  fixes A B :: "nat \<Rightarrow> int" and L M0 :: nat
  assumes part: "\<And>m::nat. m < 256 \<Longrightarrow> m mod (2*L) < L \<Longrightarrow> m + L < 256"
    and ag: "\<forall>m. (m::nat) < 256 \<longrightarrow> A m = B m"
  shows "\<forall>n. (n::nat) < 256 \<longrightarrow> bflyLayer L M0 A n = bflyLayer L M0 B n"
proof (intro allI impI)
  fix n :: nat assume n: "n < 256"
  show "bflyLayer L M0 A n = bflyLayer L M0 B n"
  proof (cases "n mod (2*L) < L")
    case True
    have pl: "n + L < 256" using part[OF n True] .
    have "A n = B n" using ag n by blast
    moreover have "A (n + L) = B (n + L)" using ag pl by blast
    ultimately show ?thesis using True by (simp add: bflyLayer_def)
  next
    case False
    have ml: "n - L < 256" using n by simp
    have "A n = B n" using ag n by blast
    moreover have "A (n - L) = B (n - L)" using ag ml by blast
    ultimately show ?thesis using False by (simp add: bflyLayer_def)
  qed
qed

text \<open>The full lifted forward NTT, at every position, equals the 8-fold abstract
  Cooley-Tukey butterfly transform on the int-coefficient view. Chains the
  per-layer abstractions \<open>abs_*\<close> inside-out under bound preservation, using the
  agree-below-256 congruence at each composition step.\<close>
theorem fwd_as_bfly:
  assumes "bounded w" and "n < 256"
  shows "cf (nttFwdAllRef w) n = fwdBfly (cf w) n"
proof -
  define w1 where "w1 = nttLayerFwd 128 1 0 w"
  define w2 where "w2 = nttLayerFwd 64 2 1 w1"
  define w3 where "w3 = nttLayerFwd 32 4 3 w2"
  define w4 where "w4 = nttLayerFwd 16 8 7 w3"
  define w5 where "w5 = nttLayerFwd 8 16 15 w4"
  define w6 where "w6 = nttLayerFwd 4 32 31 w5"
  define w7 where "w7 = nttLayerFwd 2 64 63 w6"
  have b1: "bounded w1" unfolding w1_def using assms(1) by (rule bounded_128)
  have b2: "bounded w2" unfolding w2_def using b1 by (rule bounded_64)
  have b3: "bounded w3" unfolding w3_def using b2 by (rule bounded_32)
  have b4: "bounded w4" unfolding w4_def using b3 by (rule bounded_16)
  have b5: "bounded w5" unfolding w5_def using b4 by (rule bounded_8)
  have b6: "bounded w6" unfolding w6_def using b5 by (rule bounded_4)
  have b7: "bounded w7" unfolding w7_def using b6 by (rule bounded_2)
  \<comment> \<open>per-layer abstraction, all positions\<close>
  have a1: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w1 m = bflyLayer 128 0 (cf w) m"
    unfolding w1_def using abs_128[OF assms(1)] by blast
  have a2: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w2 m = bflyLayer 64 1 (cf w1) m"
    unfolding w2_def using abs_64[OF b1] by blast
  have a3: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w3 m = bflyLayer 32 3 (cf w2) m"
    unfolding w3_def using abs_32[OF b2] by blast
  have a4: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w4 m = bflyLayer 16 7 (cf w3) m"
    unfolding w4_def using abs_16[OF b3] by blast
  have a5: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w5 m = bflyLayer 8 15 (cf w4) m"
    unfolding w5_def using abs_8[OF b4] by blast
  have a6: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w6 m = bflyLayer 4 31 (cf w5) m"
    unfolding w6_def using abs_4[OF b5] by blast
  have a7: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w7 m = bflyLayer 2 63 (cf w6) m"
    unfolding w7_def using abs_2[OF b6] by blast
  \<comment> \<open>fold the abstractions into the nested composition, inside-out\<close>
  have P1: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w1 m = bflyLayer 128 0 (cf w) m" by (rule a1)
  have P2: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w2 m
      = bflyLayer 64 1 (bflyLayer 128 0 (cf w)) m"
  proof -
    have c: "\<forall>m. (m::nat) < 256 \<longrightarrow>bflyLayer 64 1 (cf w1) m
        = bflyLayer 64 1 (bflyLayer 128 0 (cf w)) m"
      by (rule bflyLayer_cong[OF _ P1]) presburger
    show ?thesis by (rule agree_trans[OF a2 c])
  qed
  have P3: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w3 m
      = bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w))) m"
  proof -
    have c: "\<forall>m. (m::nat) < 256 \<longrightarrow>bflyLayer 32 3 (cf w2) m
        = bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w))) m"
      by (rule bflyLayer_cong[OF _ P2]) presburger
    show ?thesis by (rule agree_trans[OF a3 c])
  qed
  have P4: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w4 m
      = bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w)))) m"
  proof -
    have c: "\<forall>m. (m::nat) < 256 \<longrightarrow>bflyLayer 16 7 (cf w3) m
        = bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w)))) m"
      by (rule bflyLayer_cong[OF _ P3]) presburger
    show ?thesis by (rule agree_trans[OF a4 c])
  qed
  have P5: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w5 m
      = bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w))))) m"
  proof -
    have c: "\<forall>m. (m::nat) < 256 \<longrightarrow>bflyLayer 8 15 (cf w4) m
        = bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w))))) m"
      by (rule bflyLayer_cong[OF _ P4]) presburger
    show ?thesis by (rule agree_trans[OF a5 c])
  qed
  have P6: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w6 m
      = bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w)))))) m"
  proof -
    have c: "\<forall>m. (m::nat) < 256 \<longrightarrow>bflyLayer 4 31 (cf w5) m
        = bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w)))))) m"
      by (rule bflyLayer_cong[OF _ P5]) presburger
    show ?thesis by (rule agree_trans[OF a6 c])
  qed
  have P7: "\<forall>m. (m::nat) < 256 \<longrightarrow>cf w7 m
      = bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w))))))) m"
  proof -
    have c: "\<forall>m. (m::nat) < 256 \<longrightarrow>bflyLayer 2 63 (cf w6) m
        = bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15 (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w))))))) m"
      by (rule bflyLayer_cong[OF _ P6]) presburger
    show ?thesis by (rule agree_trans[OF a7 c])
  qed
  \<comment> \<open>outermost layer at the single position n\<close>
  have unf: "nttFwdAllRef w = nttLayerFwd 1 128 127 w7"
    unfolding w7_def w6_def w5_def w4_def w3_def w2_def w1_def by (rule fwd_unfold)
  have congN: "\<forall>k. (k::nat) < 256 \<longrightarrow>bflyLayer 1 127 (cf w7) k
      = bflyLayer 1 127 (bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15
          (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w)))))))) k"
    by (rule bflyLayer_cong[OF _ P7]) presburger
  have "cf (nttFwdAllRef w) n = cf (nttLayerFwd 1 128 127 w7) n" using unf by simp
  also have "\<dots> = bflyLayer 1 127 (cf w7) n" using abs_1[OF b7 assms(2)] by simp
  also have "\<dots> = bflyLayer 1 127 (bflyLayer 2 63 (bflyLayer 4 31 (bflyLayer 8 15
          (bflyLayer 16 7 (bflyLayer 32 3 (bflyLayer 64 1 (bflyLayer 128 0 (cf w)))))))) n"
    using congN assms(2) by blast
  also have "\<dots> = fwdBfly (cf w) n" by (simp add: fwdBfly_def)
  finally show ?thesis .
qed

end
