theory HQC_Poly
  imports "Cryptol.Cryptol" "HOL-Library.Z2"
begin

text \<open>Algebra for HQC's multiplication in GF(2)[x]: a word list read as a polynomial over GF(2),
  the Karatsuba identity on such lists, and the 64-bit shift-and-XOR loop as polynomial
  multiplication. Nothing here uses the lifted models; HQC_Seq connects them.\<close>

text \<open>Polynomials over GF(2), and the reading of a list of 64-bit words as one (word 0 least
  significant, bit j of a word the coefficient of x^j).\<close>

type_synonym gf2 = Z2.bit

lemma gf2_add_self[simp]: "(x :: gf2) + x = 0"
  by simp

lemma gf2_poly_one_one: "(1 :: gf2 poly) + 1 = 0"
  by (simp only: poly_eq_iff coeff_add) simp

lemma gf2_poly_two[simp]: "(2 :: gf2 poly) = 0"
  using gf2_poly_one_one by (simp add: one_add_one)

lemma gf2_poly_add_self[simp]: "(p :: gf2 poly) + p = 0"
  by (metis mult_2 gf2_poly_two mult_zero_left)

lemma gf2_poly_two_mult[simp]: "(p :: gf2 poly) * 2 = 0" "2 * (p :: gf2 poly) = 0"
  by simp_all

lemma gf2_poly_minus: "(p :: gf2 poly) - q = p + q"
proof -
  have "p - q + q = p" by simp
  then have "p - q + q + q = p + q" by simp
  then show ?thesis by (simp only: add.assoc gf2_poly_add_self add_0_right)
qed

definition pw :: "'a::len word \<Rightarrow> gf2 poly" where
  "pw w = (\<Sum>j<LENGTH('a). monom (of_bool (bit w j)) j)"

lemma coeff_pw: "coeff (pw (w :: 'a::len word)) j = of_bool (bit w j)"
  by (auto simp: pw_def coeff_sum coeff_monom sum.delta dest: bit_imp_le_length)

lemma pw_xor: "pw (x XOR y) = pw x + pw y"
  by (auto simp: poly_eq_iff coeff_pw bit_xor_iff)

lemma pw_zero[simp]: "pw (0 :: 'a::len word) = 0"
  by (simp add: poly_eq_iff coeff_pw)

primrec Pl :: "64 word list \<Rightarrow> gf2 poly" where
  "Pl [] = 0"
| "Pl (w # ws) = pw w + monom 1 64 * Pl ws"

lemma Pl_append: "Pl (xs @ ys) = Pl xs + monom 1 (64 * length xs) * Pl ys"
proof (induction xs)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  have "monom (1 :: gf2) 64 * monom 1 (64 * length xs) = monom 1 (64 * length (x # xs))"
    by (simp add: mult_monom)
  then show ?case using Cons by (simp add: algebra_simps flip: mult.assoc)
qed

lemma Pl_replicate0[simp]: "Pl (replicate k 0) = 0"
  by (induction k) simp_all

lemma Pl_xor: "length xs = length ys \<Longrightarrow> Pl (map2 (XOR) xs ys) = Pl xs + Pl ys"
proof (induction xs arbitrary: ys)
  case Nil then show ?case by simp
next
  case (Cons x xs)
  then obtain y ys' where "ys = y # ys'" by (cases ys) auto
  with Cons show ?case by (simp add: pw_xor algebra_simps)
qed

lemma Pl_take_drop: "Pl xs = Pl (take k xs) + monom 1 (64 * k) * Pl (drop k xs)" if "k \<le> length xs"
proof -
  have "Pl xs = Pl (take k xs @ drop k xs)" by simp
  also have "\<dots> = Pl (take k xs) + monom 1 (64 * k) * Pl (drop k xs)"
    using that by (simp only: Pl_append length_take min_absorb2)
  finally show ?thesis .
qed

text \<open>The same identity with the three products given as lists, the form the lifted \<open>kstep\<close>
  unfolds to.\<close>

lemma kara_alg:
  fixes z0 z2 zm :: "64 word list"
  assumes l: "length z0 = 2 * n0" "length z2 = 2 * n1" "length zm = 2 * n1" "n0 \<le> n1"
    and p: "Pl z0 = A0 * B0" "Pl z2 = A1 * B1" "Pl zm = (A0 + A1) * (B0 + B1)"
  shows "Pl (map2 (XOR) (z0 @ z2)
            (replicate n0 0 @ map2 (XOR) (map2 (XOR) zm (z0 @ replicate (2 * (n1 - n0)) 0)) z2
             @ replicate n0 0))
         = (A0 + monom 1 (64 * n0) * A1) * (B0 + monom 1 (64 * n0) * B1)"
proof -
  define X where "X = (monom 1 (64 * n0) :: gf2 poly)"
  have XX: "monom (1 :: gf2) (n0 * 128) = X * X"
    by (simp add: X_def mult_monom mult.commute)
  have Pmid: "Pl (map2 (XOR) (map2 (XOR) zm (z0 @ replicate (2 * (n1 - n0)) 0)) z2) = A0 * B1 + A1 * B0"
  proof -
    have "Pl (map2 (XOR) (map2 (XOR) zm (z0 @ replicate (2 * (n1 - n0)) 0)) z2)
          = (A0 + A1) * (B0 + B1) + A0 * B0 + A1 * B1"
      using l p by (simp add: Pl_xor Pl_append)
    also have "\<dots> = A0 * B1 + A1 * B0 + (A0 * B0 + A0 * B0) + (A1 * B1 + A1 * B1)"
      by (simp add: algebra_simps)
    finally show ?thesis by simp
  qed
  have lmid: "length (map2 (XOR) (map2 (XOR) zm (z0 @ replicate (2 * (n1 - n0)) 0)) z2) = 2 * n1"
    using l by simp
  show ?thesis
    using l p lmid by (simp add: Pl_xor Pl_append Pmid XX X_def algebra_simps)
qed


lemma pw_split128:
  "pw (R :: 128 word) = pw (ucast (take_bit 64 R) :: 64 word) + monom 1 64 * pw (ucast (drop_bit 64 R) :: 64 word)"
  by (auto simp: poly_eq_iff coeff_pw coeff_monom_mult bit_ucast_iff bit_take_bit_iff bit_drop_bit_eq
           not_le dest: bit_imp_le_length)

lemma pw_shift:
  assumes "i < 64"
  shows "pw ((ucast (B :: 64 word) :: 128 word) << i) = monom 1 i * pw B"
proof -
  have "bit ((ucast B :: 128 word) << i) j \<longleftrightarrow> i \<le> j \<and> bit B (j - i)" for j
    using assms by (auto simp: bit_shiftl_iff bit_ucast_iff dest: bit_imp_le_length)
  then show ?thesis
    by (auto simp: poly_eq_iff coeff_pw coeff_monom_mult not_le)
qed

definition clw_step :: "64 word \<Rightarrow> 64 word \<Rightarrow> 128 word \<Rightarrow> nat \<Rightarrow> 128 word" where
  "clw_step A B acc k = (if bit A k then acc XOR ((ucast B :: 128 word) << k) else acc)"

lemma clw_partial:
  "k \<le> 64 \<Longrightarrow> pw (foldl (clw_step A B) 0 [0..<k]) = (\<Sum>i<k. monom (of_bool (bit A i)) i) * pw B"
proof (induction k)
  case 0 then show ?case by simp
next
  case (Suc k)
  then show ?case
    by (cases "bit A k") (simp_all add: clw_step_def pw_xor pw_shift algebra_simps)
qed

lemma clw_correct: "pw (foldl (clw_step A B) 0 [0..<64]) = pw A * pw B"
  using clw_partial[of 64 A B] by (simp add: pw_def)

end
