theory GF64
  imports HQC.HQC_Poly HQC_FFT_Math.Cantor
begin

text \<open>GF(2^64) as the polynomials over GF(2) of degree below 64, with the product reduced modulo
  x^64 + x^4 + x^3 + x + 1 (the modulus of gf264.h). Only the commutative-ring structure is
  needed by the FFT theorems, so irreducibility is never used.\<close>

definition PG :: "gf2 poly" where
  "PG = monom 1 64 + monom 1 4 + monom 1 3 + monom 1 1 + 1"

lemma degree_PG: "degree PG = 64"
  unfolding PG_def by (simp add: degree_add_eq_left degree_monom_eq)

lemma PG_nz: "PG \<noteq> 0"
  using degree_PG by auto

lemma red_small: "degree p < 64 \<or> p = 0 \<Longrightarrow> p mod PG = p"
  using degree_PG by (auto intro: mod_poly_less)

lemma degree_mod_PG: "degree (p mod PG) < 64 \<or> p mod PG = 0"
  using degree_mod_less[of PG p] degree_PG PG_nz by auto

typedef gf64 = "{p :: gf2 poly. p mod PG = p}"
  by (rule exI[of _ 0]) simp

setup_lifting type_definition_gf64

lemma mod_PG_add: "(p + q) mod PG = p mod PG + q mod PG"
  using poly_mod_diff_left[of p "- q" PG] by simp

lemma pw_inj: "pw (x :: 'a :: len word) = pw y \<Longrightarrow> x = y"
proof (rule bit_eqI)
  fix n assume "pw x = pw y"
  then have "coeff (pw x) n = coeff (pw y) n" by simp
  then show "bit x n \<longleftrightarrow> bit y n" by (cases "bit x n"; cases "bit y n") (simp_all add: coeff_pw)
qed

instantiation gf64 :: comm_ring_1
begin
lift_definition zero_gf64 :: gf64 is 0 by simp
lift_definition one_gf64 :: gf64 is 1 by (rule red_small) simp
lift_definition plus_gf64 :: "gf64 \<Rightarrow> gf64 \<Rightarrow> gf64" is "\<lambda>p q. p + q" by (simp add: mod_PG_add)
lift_definition uminus_gf64 :: "gf64 \<Rightarrow> gf64" is "\<lambda>p. - p" by simp
lift_definition minus_gf64 :: "gf64 \<Rightarrow> gf64 \<Rightarrow> gf64" is "\<lambda>p q. p - q" by (simp add: poly_mod_diff_left)
lift_definition times_gf64 :: "gf64 \<Rightarrow> gf64 \<Rightarrow> gf64" is "\<lambda>p q. (p * q) mod PG" by simp
instance
proof
  fix a b c :: gf64
  show "a * b * c = a * (b * c)"
    by transfer (simp add: mod_mult_left_eq mod_mult_right_eq mult.assoc)
  show "a * b = b * a" by transfer (simp add: mult.commute)
  show "1 * a = a" by transfer simp
  show "(a + b) * c = a * c + b * c" by transfer (simp add: distrib_right mod_PG_add)
  show "a + b + c = a + (b + c)" by transfer (simp add: add.assoc)
  show "a + b = b + a" by transfer (simp add: add.commute)
  show "0 + a = a" by transfer simp
  show "- a + a = 0" by transfer simp
  show "a - b = a + - b" by transfer simp
  show "(0 :: gf64) \<noteq> 1" by transfer simp
qed
end

instance gf64 :: char2
proof
  show "1 + 1 = (0 :: gf64)" by transfer (simp add: gf2_poly_one_one)
qed

text \<open>A 64-bit word as a field element.\<close>

lift_definition gfw :: "64 word \<Rightarrow> gf64" is "\<lambda>w. pw w"
proof -
  fix w :: "64 word"
  have "degree (pw w) < 64 \<or> pw w = 0"
  proof (cases "pw w = 0")
    case False
    have "coeff (pw w) j = 0" if "j \<ge> 64" for j using that bit_imp_le_length[of w j] by (auto simp: coeff_pw)
    then have "degree (pw w) < 64"
      using False leading_coeff_0_iff[of "pw w"] by (metis not_less)
    then show ?thesis ..
  qed simp
  then show "pw w mod PG = pw w" by (rule red_small)
qed

lemma gfw_xor: "gfw (x XOR y) = gfw x + gfw y"
  by transfer (simp add: pw_xor)

lemma gfw_zero [simp]: "gfw 0 = 0"
  by transfer simp

lemma gfw_inj: "gfw x = gfw y \<Longrightarrow> x = y"
  by transfer (rule pw_inj)

end
