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

text \<open>TODO (next increment): prove
  \<open>bounded w \<Longrightarrow> n < 256 \<Longrightarrow> cf (nttFwdAllRef w) n = fwdBfly (cf w) n\<close>
  by chaining abs_* outermost-in under bound preservation, using an
  \<open>agree-below-256\<close> congruence for \<open>bflyLayer\<close> (each layer reads only n, n\<plusminus>L,
  all < 256 for the well-formed strides). Then the remaining work is purely on
  \<open>fwdBfly\<close>: derive the bit-reversal permutation from the m0 schedule and chain
  onto Bridge-1 (NNTT_eq_FNTT_twist).\<close>

end
end
