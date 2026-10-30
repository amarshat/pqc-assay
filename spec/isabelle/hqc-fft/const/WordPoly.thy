theory WordPoly
  imports GF64
begin

text \<open>Polynomial images of the word operations the lifted models use: casts and shifts become
  truncation (\<open>poly_cutoff\<close>) and division by a power of x (\<open>poly_shift\<close>).\<close>

lemma pw_ucast: "pw (ucast (w :: 'a :: len word) :: 'b :: len word) = poly_cutoff LENGTH('b) (pw w)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_poly_cutoff bit_ucast_iff dest: bit_imp_le_length)

lemma pw_push_bit: "pw (push_bit k (w :: 'a :: len word)) = poly_cutoff LENGTH('a) (monom 1 k * pw w)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_poly_cutoff bit_push_bit_iff coeff_monom_mult)

lemma pw_drop_bit: "pw (drop_bit k (w :: 'a :: len word)) = poly_shift k (pw w)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_poly_shift bit_drop_bit_eq add.commute)

lemma pw_take_bit: "pw (take_bit k (w :: 'a :: len word)) = poly_cutoff k (pw w)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_poly_cutoff bit_take_bit_iff)

lemma pw_word_cat:
  "pw (word_cat (x :: 'a :: len word) (y :: 'b :: len word) :: 'c :: len word)
     = poly_cutoff LENGTH('c) (pw y + monom 1 LENGTH('b) * pw x)"
  by (rule poly_eqI)
     (auto simp: coeff_pw coeff_poly_cutoff bit_word_cat_iff coeff_monom_mult not_less
           dest: bit_imp_le_length)

lemma coeff_pw_ge: "j \<ge> LENGTH('a) \<Longrightarrow> coeff (pw (w :: 'a :: len word)) j = 0"
  using bit_imp_le_length[of w j] by (auto simp: coeff_pw)

lemma degree_pw: "degree (pw (w :: 'a :: len word)) < LENGTH('a) \<or> pw w = 0"
proof (cases "pw w = 0")
  case False
  then have "coeff (pw w) (degree (pw w)) \<noteq> 0" by simp
  then show ?thesis using coeff_pw_ge[of "degree (pw w)" w] by (metis not_less)
qed simp

lemma cutoff_id: "(\<And>j. j \<ge> n \<Longrightarrow> coeff p j = 0) \<Longrightarrow> poly_cutoff n p = p"
  by (rule poly_eqI) (auto simp: coeff_poly_cutoff)

lemma cutoff_shift: "(p :: 'a :: comm_ring_1 poly) = poly_cutoff n p + monom 1 n * poly_shift n p"
  by (rule poly_eqI) (auto simp: coeff_poly_cutoff coeff_poly_shift coeff_monom_mult)

text \<open>Rewrites that collapse chains of truncations and shifts.\<close>

lemma cutoff_cutoff [simp]: "poly_cutoff m (poly_cutoff n p) = poly_cutoff (min m n) p"
  by (rule poly_eqI) (simp add: coeff_poly_cutoff)

lemma cutoff_add [simp]: "poly_cutoff n (p + q) = poly_cutoff n p + poly_cutoff n q"
  by (rule poly_eqI) (simp add: coeff_poly_cutoff)

lemma shift_add [simp]: "poly_shift n (p + q) = poly_shift n p + poly_shift n q"
  by (rule poly_eqI) (simp add: coeff_poly_shift)

lemma cutoff_pw [simp]: "LENGTH('a) \<le> n \<Longrightarrow> poly_cutoff n (pw (w :: 'a :: len word)) = pw w"
  by (rule cutoff_id) (simp add: coeff_pw_ge)

lemma shift_pw [simp]: "LENGTH('a) \<le> n \<Longrightarrow> poly_shift n (pw (w :: 'a :: len word)) = 0"
  by (rule poly_eqI) (simp add: coeff_poly_shift coeff_pw_ge)

lemma cutoff_monom_mult [simp]:
  "k \<le> n \<Longrightarrow> poly_cutoff n (monom 1 k * (p :: 'a :: comm_ring_1 poly)) = monom 1 k * poly_cutoff (n - k) p"
  by (rule poly_eqI) (auto simp: coeff_poly_cutoff coeff_monom_mult)

lemma shift_monom_mult [simp]:
  "k \<le> n \<Longrightarrow> poly_shift n (monom 1 k * (p :: 'a :: comm_ring_1 poly)) = poly_shift (n - k) p"
  by (rule poly_eqI) (simp add: coeff_poly_shift coeff_monom_mult)

lemma shift_cutoff [simp]: "poly_shift k (poly_cutoff n p) = poly_cutoff (n - k) (poly_shift k p)"
  by (rule poly_eqI) (auto simp: coeff_poly_shift coeff_poly_cutoff less_diff_conv)

lemma cutoff_zero_len [simp]: "poly_cutoff 0 p = 0"
  by (rule poly_eqI) (simp add: coeff_poly_cutoff)

lemma pw_mult_pow2:
  "pw ((w :: 'a :: len word) * 2 ^ k) = poly_cutoff LENGTH('a) (monom 1 k * pw w)"
  using pw_push_bit[of k w] by (simp add: push_bit_eq_mult)

lemma pw_mult_num [simp]:
  "pw ((w :: 'a :: len word) * 2) = poly_cutoff LENGTH('a) (monom 1 1 * pw w)"
  "pw ((w :: 'a :: len word) * 8) = poly_cutoff LENGTH('a) (monom 1 3 * pw w)"
  "pw ((w :: 'a :: len word) * 16) = poly_cutoff LENGTH('a) (monom 1 4 * pw w)"
  using pw_mult_pow2[of w 1] pw_mult_pow2[of w 3] pw_mult_pow2[of w 4] by simp_all

lemma shift_shift [simp]: "poly_shift a (poly_shift b p) = poly_shift (a + b) p"
  by (rule poly_eqI) (simp add: coeff_poly_shift add.assoc)

lemma cutoff_shift_pw [simp]:
  "LENGTH('a) \<le> n + k \<Longrightarrow> poly_cutoff n (poly_shift k (pw (w :: 'a :: len word))) = poly_shift k (pw w)"
  by (rule cutoff_id) (simp add: coeff_poly_shift coeff_pw_ge)

end
