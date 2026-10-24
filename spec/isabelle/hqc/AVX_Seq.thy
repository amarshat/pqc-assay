theory AVX_Seq
  imports HQC_Seq AVXK
begin

text \<open>The two multi-way Karatsuba levels of the AVX2 gf2x.c are correct over correct products:
  \<open>k3step_correct\<close> (karat_mult3, three parts, six products) and \<open>k5step_correct\<close>
  (karat_mult_5, five parts, fifteen products).\<close>

lemma X_pow: "(monom 1 m :: gf2 poly) ^ k = monom 1 (m * k)"
  by (induction k) (simp_all add: mult_monom)

lemma monom_pow_t:
  "monom (1 :: gf2) (t * 128) = monom 1 (t * 64) ^ 2" "monom (1 :: gf2) (t * 192) = monom 1 (t * 64) ^ 3"
  "monom (1 :: gf2) (t * 256) = monom 1 (t * 64) ^ 4"
  by (simp_all add: X_pow mult.commute)

lemma monom_pow_t5:
  "monom (1 :: gf2) (t * 320) = monom 1 (t * 64) ^ 5" "monom (1 :: gf2) (t * 384) = monom 1 (t * 64) ^ 6"
  "monom (1 :: gf2) (t * 448) = monom 1 (t * 64) ^ 7" "monom (1 :: gf2) (t * 512) = monom 1 (t * 64) ^ 8"
  by (simp_all add: X_pow mult.commute)

lemma pow_expand:
  fixes x :: "gf2 poly"
  shows "x ^ 5 = x * x * x * x * x" "x ^ 6 = x * x * x * x * x * x"
        "x ^ 7 = x * x * x * x * x * x * x" "x ^ 8 = x * x * x * x * x * x * x * x"
  by (simp_all add: eval_nat_numeral algebra_simps)

text \<open>The 3-way recombination as a list identity: six products placed at block offsets 0..4.\<close>

lemma k3_sum:
  fixes d0 d1 d2 d3 d4 d5 :: "64 word list"
  assumes l: "length d0 = 2 * t" "length d1 = 2 * t" "length d2 = 2 * t"
             "length d3 = 2 * t" "length d4 = 2 * t" "length d5 = 2 * t"
    and n: "n1 = t" "n2 = 2 * t" "n3 = 3 * t" "n4 = 4 * t"
  shows "Pl (map2 (XOR) (map2 (XOR) (map2 (XOR) (map2 (XOR) (d0 @ replicate n4 0)
             (replicate n1 0 @ map2 (XOR) (map2 (XOR) d3 d0) d1 @ replicate n3 0))
             (replicate n2 0 @ map2 (XOR) (map2 (XOR) (map2 (XOR) d4 d0) d2) d1 @ replicate n2 0))
             (replicate n3 0 @ map2 (XOR) (map2 (XOR) d5 d1) d2 @ replicate n1 0))
             (replicate n4 0 @ d2))
         = Pl d0 + monom 1 (t * 64) * (Pl d3 + Pl d0 + Pl d1) + monom 1 (t * 64) ^ 2 * (Pl d4 + Pl d0 + Pl d2 + Pl d1)
           + monom 1 (t * 64) ^ 3 * (Pl d5 + Pl d1 + Pl d2) + monom 1 (t * 64) ^ 4 * Pl d2"
  using l unfolding n by (simp add: Pl_xor Pl_append monom_pow_t algebra_simps)

context includes cryptol_syntax begin

lemma Pl_L_split3:
  "Pl (L (a :: [3 * 't][64])) = Pl (take LEN('t) (L a)) + monom 1 (LEN('t) * 64) * Pl (take LEN('t) (drop LEN('t) (L a)))
     + monom 1 (LEN('t) * 64) ^ 2 * Pl (drop (2 * LEN('t)) (L a))"
proof -
  have "Pl (L a) = Pl (take LEN('t) (L a)) + monom 1 (64 * LEN('t)) * Pl (drop LEN('t) (L a))"
    by (rule Pl_take_drop) simp
  also have "Pl (drop LEN('t) (L a)) = Pl (take LEN('t) (drop LEN('t) (L a))) + monom 1 (64 * LEN('t)) * Pl (drop LEN('t) (drop LEN('t) (L a)))"
    by (rule Pl_take_drop) simp
  finally show ?thesis
    by (simp add: power2_eq_square mult_monom algebra_simps mult_2 mult_2_right mult.commute)
qed

lemma k3step_correct:
  assumes t: "1 \<le> LEN('t)"
    and m: "\<And>x y. Pl (L (m x y)) = Pl (L x) * Pl (L y)"
  shows "Pl (L (k3step`{'t} m a b)) = Pl (L a) * Pl (L b)"
  using t
  apply (simp only: k3step_def Let_def)
  apply (simp del: xor_logic_seq add: L_xor L_append L_zero L_coerce L_take L_drop)
  apply (rule trans[OF k3_sum])
            apply simp_all[10]
  apply (simp del: xor_logic_seq add: m L_xor Pl_xor L_coerce L_take L_drop Pl_L_split3
                   power2_eq_square power3_eq_cube power4_eq_xxxx mult_2_right algebra_simps)
  done

lemma Pl_L_split5:
  "Pl (L (a :: [5 * 't][64])) = Pl (take LEN('t) (L a))
     + monom 1 (LEN('t) * 64) * Pl (take LEN('t) (drop LEN('t) (L a)))
     + monom 1 (LEN('t) * 64) * monom 1 (LEN('t) * 64) * Pl (take LEN('t) (drop (LEN('t) + LEN('t)) (L a)))
     + monom 1 (LEN('t) * 64) * monom 1 (LEN('t) * 64) * monom 1 (LEN('t) * 64)
       * Pl (take LEN('t) (drop (LEN('t) + (LEN('t) + LEN('t))) (L a)))
     + monom 1 (LEN('t) * 64) * monom 1 (LEN('t) * 64) * monom 1 (LEN('t) * 64) * monom 1 (LEN('t) * 64)
       * Pl (drop (LEN('t) + (LEN('t) + (LEN('t) + LEN('t)))) (L a))"
proof -
  let ?T = "LEN('t)" and ?X = "monom 1 (64 * LEN('t)) :: gf2 poly"
  have d0: "Pl (L a) = Pl (take ?T (L a)) + ?X * Pl (drop ?T (L a))"
    by (rule Pl_take_drop) simp
  have d1: "Pl (drop ?T (L a)) = Pl (take ?T (drop ?T (L a))) + ?X * Pl (drop (?T + ?T) (L a))"
    by (subst Pl_take_drop[of ?T]) (simp_all add: drop_drop)
  have d2: "Pl (drop (?T + ?T) (L a)) = Pl (take ?T (drop (?T + ?T) (L a))) + ?X * Pl (drop (?T + (?T + ?T)) (L a))"
    by (subst Pl_take_drop[of ?T]) (simp_all add: drop_drop)
  have d3: "Pl (drop (?T + (?T + ?T)) (L a)) = Pl (take ?T (drop (?T + (?T + ?T)) (L a))) + ?X * Pl (drop (?T + (?T + (?T + ?T))) (L a))"
    by (subst Pl_take_drop[of ?T]) (simp_all add: drop_drop)
  show ?thesis
    unfolding d0 d1 d2 d3 by (simp add: algebra_simps mult.commute)
qed

lemma k5step_correct:
  assumes t: "1 \<le> LEN('t)"
    and m: "\<And>x y. Pl (L (m x y)) = Pl (L x) * Pl (L y)"
  shows "Pl (L (k5step`{'t} m a b)) = Pl (L a) * Pl (L b)"
  using t
  apply (simp only: k5step_def Let_def)
  apply (simp del: xor_logic_seq add: L_xor L_append L_zero L_coerce L_take L_drop)
  apply (simp del: xor_logic_seq add: m L_xor Pl_xor Pl_append L_coerce L_take L_drop Pl_L_split5
                   monom_pow_t monom_pow_t5 power2_eq_square power3_eq_cube power4_eq_xxxx pow_expand
                   mult_2_right algebra_simps)
  done

end

end
