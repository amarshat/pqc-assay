theory Barrett_Core
  imports Main
begin

text \<open>The Barrett integer identity (escape2_core analog), proved without smt: for
  0 <= X < 2^46, the impl's floor-quotient remainder with one conditional subtract
  equals X mod q. q = 8380417, M = floor(2^46/q) = 8396807, S = 2^46. Key numeric
  facts: M*q = S - 49145 (so M*q < S, and S - M*q < q), which bounds the Barrett
  approximation error to one q.\<close>

text \<open>Barrett approximation bounds (the intermediate facts inside \<open>barrett_core\<close>,
  exported for the word-level bridge): the floor-quotient \<open>Q\<close> under-approximates so
  \<open>Q*q \<le> X\<close> (subtraction never underflows) and the remainder \<open>X - Q*q < 8429562 < 2q\<close>
  (fits in 32 bits). Same derivation as \<open>barrett_core\<close>; M*q = S - 49145 caps the error.\<close>
lemma barrett_core_bounds:
  fixes X :: int
  assumes x0: "0 \<le> X" and xhi: "X < 70368744177664"
  shows "((X * 8396807) div 70368744177664) * 8380417 \<le> X
       \<and> X < ((X * 8396807) div 70368744177664) * 8380417 + 8429562"
proof -
  define Q where "Q = (X * 8396807) div 70368744177664"
  have dm: "Q * 70368744177664 + (X * 8396807) mod 70368744177664 = X * 8396807"
    unfolding Q_def by simp
  have mlo: "0 \<le> (X * 8396807) mod 70368744177664" using x0 by simp
  have mhi: "(X * 8396807) mod 70368744177664 < 70368744177664" by simp
  have QSle: "Q * 70368744177664 \<le> X * 8396807" using dm mlo by linarith
  have QSgt: "X * 8396807 < Q * 70368744177664 + 70368744177664" using dm mhi by linarith
  have MQ: "(8396807::int) * 8380417 = 70368744128519" by simp
  have l1: "Q * 70368744177664 * 8380417 \<le> X * 8396807 * 8380417"
    using mult_right_mono[OF QSle, of 8380417] by simp
  have l2: "X * 8396807 * 8380417 \<le> X * 70368744177664"
    using x0 by (simp add: mult.assoc MQ mult_left_mono)
  have l3: "(Q * 8380417) * 70368744177664 \<le> X * 70368744177664"
    using l1 l2 by (simp add: mult.assoc mult.left_commute mult.commute)
  have Rge: "Q * 8380417 \<le> X"
    using l3 mult_right_le_imp_le[of "Q * 8380417" 70368744177664 X] by simp
  have u1: "X * 8396807 * 8380417 < (Q * 70368744177664 + 70368744177664) * 8380417"
    using mult_strict_right_mono[OF QSgt, of 8380417] by simp
  have u2: "X * 70368744177664 - X * 49145 < (Q * 8380417) * 70368744177664 + 8380417 * 70368744177664"
    using u1 by (simp add: mult.assoc MQ algebra_simps)
  have u3: "X * 49145 < 70368744177664 * 49145"
    using xhi x0 by simp
  have u4: "X * 70368744177664 < (Q * 8380417 + 8429562) * 70368744177664"
    using u2 u3 by (simp add: algebra_simps)
  have Rlt: "X < Q * 8380417 + 8429562"
    using u4 mult_right_less_imp_less[of X 70368744177664 "Q * 8380417 + 8429562"] by simp
  from Rge Rlt show ?thesis unfolding Q_def by simp
qed

lemma barrett_core:
  fixes X :: int
  assumes x0: "0 \<le> X" and xhi: "X < 70368744177664"
  shows "(let r = X - ((X * 8396807) div 70368744177664) * 8380417
          in if r \<ge> 8380417 then r - 8380417 else r) = X mod 8380417"
proof -
  define Q where "Q = (X * 8396807) div 70368744177664"
  \<comment> \<open>division characterization of Q\<close>
  have dm: "Q * 70368744177664 + (X * 8396807) mod 70368744177664 = X * 8396807"
    unfolding Q_def by simp
  have mlo: "0 \<le> (X * 8396807) mod 70368744177664" using x0 by simp
  have mhi: "(X * 8396807) mod 70368744177664 < 70368744177664" by simp
  have QSle: "Q * 70368744177664 \<le> X * 8396807" using dm mlo by linarith
  have QSgt: "X * 8396807 < Q * 70368744177664 + 70368744177664" using dm mhi by linarith
  \<comment> \<open>numeric: M*q = S - 49145\<close>
  have MQ: "(8396807::int) * 8380417 = 70368744128519" by simp

  \<comment> \<open>lower bound: Q*q \<le> X\<close>
  have l1: "Q * 70368744177664 * 8380417 \<le> X * 8396807 * 8380417"
    using mult_right_mono[OF QSle, of 8380417] by simp
  have l2: "X * 8396807 * 8380417 \<le> X * 70368744177664"
    using x0 by (simp add: mult.assoc MQ mult_left_mono)
  have l3: "(Q * 8380417) * 70368744177664 \<le> X * 70368744177664"
    using l1 l2 by (simp add: mult.assoc mult.left_commute mult.commute)
  have Rge: "Q * 8380417 \<le> X"
    using l3 mult_right_le_imp_le[of "Q * 8380417" 70368744177664 X] by simp

  \<comment> \<open>upper bound: X < Q*q + 2q\<close>
  have u1: "X * 8396807 * 8380417 < (Q * 70368744177664 + 70368744177664) * 8380417"
    using mult_strict_right_mono[OF QSgt, of 8380417] by simp
  have u2: "X * 70368744177664 - X * 49145 < (Q * 8380417) * 70368744177664 + 8380417 * 70368744177664"
    using u1 by (simp add: mult.assoc MQ algebra_simps)
  have u3: "X * 49145 < 70368744177664 * 49145"
    using xhi x0 by simp
  have u4: "X * 70368744177664 < (Q * 8380417 + 8429562) * 70368744177664"
    using u2 u3 by (simp add: algebra_simps)
  have Rlt: "X < Q * 8380417 + 8429562"
    using u4 mult_right_less_imp_less[of X 70368744177664 "Q * 8380417 + 8429562"] by simp

  \<comment> \<open>finish: R = X - Q*q in [0, 2q), R \<equiv> X (mod q), pick branch\<close>
  have shift0: "(X - Q * 8380417) mod 8380417 = X mod 8380417"
  proof -
    have "(X - Q * 8380417) mod 8380417 = (X + (- Q) * 8380417) mod 8380417"
      by (simp add: algebra_simps)
    also have "\<dots> = X mod 8380417" by (rule mod_mult_self1)
    finally show ?thesis .
  qed
  have shift1: "(X - Q * 8380417 - 8380417) mod 8380417 = X mod 8380417"
  proof -
    have "(X - Q * 8380417 - 8380417) mod 8380417 = (X + (- Q - 1) * 8380417) mod 8380417"
      by (simp add: algebra_simps)
    also have "\<dots> = X mod 8380417" by (rule mod_mult_self1)
    finally show ?thesis .
  qed
  have "(let r = X - ((X * 8396807) div 70368744177664) * 8380417
         in if r \<ge> 8380417 then r - 8380417 else r)
        = (if 8380417 \<le> X - Q * 8380417 then X - Q * 8380417 - 8380417 else X - Q * 8380417)"
    by (simp add: Let_def Q_def)
  also have "\<dots> = X mod 8380417"
  proof (cases "8380417 \<le> X - Q * 8380417")
    case True
    have c1: "0 \<le> X - Q * 8380417 - 8380417" using True by simp
    have c2: "X - Q * 8380417 - 8380417 < 8380417" using Rlt by simp
    have "(if 8380417 \<le> X - Q * 8380417 then X - Q * 8380417 - 8380417 else X - Q * 8380417)
            = X - Q * 8380417 - 8380417" using True by simp
    also have "\<dots> = (X - Q * 8380417 - 8380417) mod 8380417"
      by (rule mod_pos_pos_trivial[OF c1 c2, symmetric])
    also have "\<dots> = X mod 8380417" by (rule shift1)
    finally show ?thesis .
  next
    case False
    have c1: "0 \<le> X - Q * 8380417" using Rge by simp
    have c2: "X - Q * 8380417 < 8380417" using False by simp
    have "(if 8380417 \<le> X - Q * 8380417 then X - Q * 8380417 - 8380417 else X - Q * 8380417)
            = X - Q * 8380417" using False by simp
    also have "\<dots> = (X - Q * 8380417) mod 8380417"
      by (rule mod_pos_pos_trivial[OF c1 c2, symmetric])
    also have "\<dots> = X mod 8380417" by (rule shift0)
    finally show ?thesis .
  qed
  finally show ?thesis .
qed

end
