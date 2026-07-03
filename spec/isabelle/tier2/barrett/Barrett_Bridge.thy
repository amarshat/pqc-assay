theory Barrett_Bridge
  imports Barrett_Lift Barrett_Core "Word_Lib.Word_Lemmas"
begin

text \<open>Route Y word-level bridge. Goal: barrettBV_bridge x, i.e.
  x < 2^46 \<longrightarrow> barrettBV x = drop`{96} ((zext x) mod q).

  Unfolding the lifted definitions and simplifying the Cryptol image ops
  (simp add: cryptol_prim_defs word_seq_convs) reduces the goal to a pure
  Isabelle-Word statement (smallReduce already case-split), over w = seq_to_word x:

    (q \<le> R \<longrightarrow> w < 1<<46 \<longrightarrow> R - q = ucast (take_bit 32 (ucast (ucast w mod q))))
  \<and> (\<not> q \<le> R \<longrightarrow> w < 1<<46 \<longrightarrow> R     = ucast (take_bit 32 (ucast (ucast w mod q))))
    where R = UCAST(128\<rightarrow>32) (take_bit 32
                (UCAST(64\<rightarrow>128) w - (UCAST(64\<rightarrow>128) w * 0x802007 >> 46) * 0x7FE001))
          q = 0x7FE001 = 8380417,  0x802007 = 8396807 = floor(2^46/q).

  The proof pushes unsigned interpretation (uint) through the word ops onto
  Barrett_Core (the integer identity, already proven), discharging the standard
  Word_Lib side conditions. This REPLACES the nine bvToInt homomorphisms admitted
  in the SAW spike (spike2_lift.saw) with proven Word_Lib lemmas (algebra +
  induction, no bit-blast, no smt):
    - UCAST(64\<rightarrow>128) w  :  uint_up_ucast / is_up      (zext, uint preserved)
    - _ * 0x802007      :  uint_word_ariths            (no overflow: n*M < 2^69)
    - _ >> 46           :  uint_shiftr_eq              (shiftr = div 2^46)
    - _ * 0x7FE001      :  uint_word_ariths            (no overflow, via bounds)
    - _ - _             :  uint_sub_lem                (no underflow: quot*q \<le> n)
    - take_bit 32 / ucast:  unsigned_take_bit_eq / unsigned_ucast_eq (rem < 2q < 2^32)
    - _ mod q           :  uint_mod_distrib            (urem)
    - q \<le> _, _ < _, ==   :  word_le_def, word_less_def, word_uint_eq_iff
  Barrett_Core (bounds + core identity) then closes the resulting integer statement.
  Companion escape2 note: paper/notes/escape2-lift-plan.md.\<close>

text \<open>uint of the 128-bit Barrett remainder: for x < 2^46 the quotient
  under-approximates (quot*q \<le> x, no underflow) and the products stay below 2^128
  (no overflow), so the whole thing equals the integer remainder x - quot*q.\<close>
lemma barrett_sub_uint:
  fixes w :: "64 word"
  assumes hw: "uint w < 70368744177664"
  shows "uint ((ucast w :: 128 word)
              - (((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001)
         = uint w - (uint w * 8396807 div 70368744177664) * 8380417"
proof -
  define X where "X = uint w"
  have x0: "0 \<le> X" unfolding X_def by simp
  have xhi: "X < 70368744177664" unfolding X_def using hw by simp
  define Q where "Q = X * 8396807 div 70368744177664"
  have uxll: "uint (ucast w :: 128 word) = X"
    unfolding X_def by (simp add: uint_up_ucast is_up)
  have p_lt: "X * 8396807 < 2 ^ 128"
  proof -
    have "X * 8396807 < 70368744177664 * 8396807"
      using xhi by (simp add: mult_strict_right_mono)
    thus ?thesis by simp
  qed
  have uprod: "uint ((ucast w :: 128 word) * 0x802007) = X * 8396807"
    using p_lt x0 uxll by (simp add: uint_word_ariths mod_pos_pos_trivial)
  have uquot: "uint (((ucast w :: 128 word) * 0x802007) >> 46) = Q"
    unfolding Q_def by (simp add: uint_shiftr_eq uprod)
  have bnds: "Q * 8380417 \<le> X \<and> X < Q * 8380417 + 8429562"
    using barrett_core_bounds[OF x0 xhi] unfolding Q_def by simp
  have Qq_le: "Q * 8380417 \<le> X" using bnds by simp
  have Q0: "0 \<le> Q" unfolding Q_def using x0 by simp
  have Qq_lt: "Q * 8380417 < 2 ^ 128" using Qq_le xhi by simp
  have uqq: "uint ((((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001) = Q * 8380417"
    using Qq_lt Q0 uquot by (simp add: uint_word_ariths mod_pos_pos_trivial)
  have ge: "uint ((((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001)
            \<le> uint (ucast w :: 128 word)"
    using uxll uqq Qq_le by simp
  have usub0: "uint ((ucast w :: 128 word)
                     - (((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001)
             = uint (ucast w :: 128 word)
               - uint ((((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001)"
    using ge by (simp add: uint_sub_lem)
  show ?thesis using usub0 uxll uqq unfolding X_def Q_def by simp
qed

lemma uint_1_shiftl_46: "uint (1 << 46 :: 64 word) = 70368744177664"
  by (simp add: shiftl_def)

text \<open>uint of the 32-bit truncation of the 128-bit Barrett remainder: since the
  remainder lies in [0, 2q) < 2^32, truncating to 32 bits is lossless.\<close>
lemma barrett_R32val:
  fixes w :: "64 word"
  assumes hw: "uint w < 70368744177664"
  shows "uint (ucast ((ucast w :: 128 word)
                     - (((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001) :: 32 word)
         = uint w - (uint w * 8396807 div 70368744177664) * 8380417"
proof -
  have x0: "0 \<le> uint w" by simp
  have bnds: "(uint w * 8396807 div 70368744177664) * 8380417 \<le> uint w
            \<and> uint w < (uint w * 8396807 div 70368744177664) * 8380417 + 8429562"
    using barrett_core_bounds[OF x0 hw] .
  have rlo: "0 \<le> uint w - (uint w * 8396807 div 70368744177664) * 8380417" using bnds by simp
  have rhi: "uint w - (uint w * 8396807 div 70368744177664) * 8380417 < 4294967296" using bnds by simp
  have "uint (ucast ((ucast w :: 128 word)
                    - (((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001) :: 32 word)
      = take_bit 32 (uint ((ucast w :: 128 word)
                    - (((ucast w :: 128 word) * 0x802007) >> 46) * 0x7FE001))"
    by (simp add: unsigned_ucast_eq)
  also have "\<dots> = take_bit 32 (uint w - (uint w * 8396807 div 70368744177664) * 8380417)"
    by (simp add: barrett_sub_uint[OF hw])
  also have "\<dots> = uint w - (uint w * 8396807 div 70368744177664) * 8380417"
    using rlo rhi by (simp add: take_bit_int_eq_self)
  finally show ?thesis .
qed

context includes cryptol_syntax begin

theorem barrettBV_bridge_holds: "barrettBV_bridge x"
  unfolding barrettBV_bridge_def barrettBV_def smallReduce_def q_def barrettMult_def Let_def
  apply (simp add: cryptol_prim_defs word_seq_convs right_shift_def left_shift_def)
  apply (simp add: word_le_def word_less_def word_uint_eq_iff
                   unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                   uint_shiftr_eq uint_mod_distrib)
  apply (intro conjI impI)
  subgoal premises p
  proof -
    have hw: "uint (seq_to_word x) < 70368744177664"
      using p(2) uint_1_shiftl_46 by linarith
    have x0: "0 \<le> uint (seq_to_word x)" by simp
    define R where "R = uint (seq_to_word x) - uint (seq_to_word x) * 8396807 div 70368744177664 * 8380417"
    have bnds: "uint (seq_to_word x) * 8396807 div 70368744177664 * 8380417 \<le> uint (seq_to_word x)
              \<and> uint (seq_to_word x) < uint (seq_to_word x) * 8396807 div 70368744177664 * 8380417 + 8429562"
      using barrett_core_bounds[OF x0 hw] by simp
    have rlo: "0 \<le> R" unfolding R_def using bnds by simp
    have rhi: "R < 4294967296" unfolding R_def using bnds by simp
    note bs = barrett_sub_uint[OF hw, folded R_def]
    note br = barrett_R32val[OF hw, folded R_def]
    have bc: "(if 8380417 \<le> R then R - 8380417 else R) = uint (seq_to_word x) mod 8380417"
      using barrett_core[OF x0 hw] unfolding R_def by (simp add: Let_def)
    have branch: "8380417 \<le> R" using p(1) bs rlo rhi by (simp add: take_bit_int_eq_self)
    have tb128: "take_bit 128 (uint (seq_to_word x)) = uint (seq_to_word x)"
      using uint_lt2p[of "seq_to_word x"] x0 by (simp add: take_bit_int_eq_self)
    have qmod: "take_bit 32 (uint (seq_to_word x) mod 8380417) = uint (seq_to_word x) mod 8380417"
      by (rule take_bit_int_eq_self; simp add: pos_mod_bound)
    have goalval: "R - 8380417 = uint (seq_to_word x) mod 8380417" using bc branch by simp
    show ?thesis using bs rlo branch rhi tb128 qmod goalval
      by (simp add: uint_word_ariths unsigned_take_bit_eq unsigned_ucast_eq
                    take_bit_int_eq_self mod_pos_pos_trivial)
  qed
  subgoal premises p
  proof -
    have hw: "uint (seq_to_word x) < 70368744177664"
      using p(2) uint_1_shiftl_46 by linarith
    have x0: "0 \<le> uint (seq_to_word x)" by simp
    define R where "R = uint (seq_to_word x) - uint (seq_to_word x) * 8396807 div 70368744177664 * 8380417"
    have bnds: "uint (seq_to_word x) * 8396807 div 70368744177664 * 8380417 \<le> uint (seq_to_word x)
              \<and> uint (seq_to_word x) < uint (seq_to_word x) * 8396807 div 70368744177664 * 8380417 + 8429562"
      using barrett_core_bounds[OF x0 hw] by simp
    have rlo: "0 \<le> R" unfolding R_def using bnds by simp
    have rhi: "R < 4294967296" unfolding R_def using bnds by simp
    note bs = barrett_sub_uint[OF hw, folded R_def]
    have bc: "(if 8380417 \<le> R then R - 8380417 else R) = uint (seq_to_word x) mod 8380417"
      using barrett_core[OF x0 hw] unfolding R_def by (simp add: Let_def)
    have branch: "\<not> 8380417 \<le> R" using p(1) bs rlo rhi by (simp add: take_bit_int_eq_self)
    have tb128: "take_bit 128 (uint (seq_to_word x)) = uint (seq_to_word x)"
      using uint_lt2p[of "seq_to_word x"] x0 by (simp add: take_bit_int_eq_self)
    have qmod: "take_bit 32 (uint (seq_to_word x) mod 8380417) = uint (seq_to_word x) mod 8380417"
      by (rule take_bit_int_eq_self; simp add: pos_mod_bound)
    have goalval: "R = uint (seq_to_word x) mod 8380417" using bc branch by simp
    show ?thesis using bs rlo rhi tb128 qmod goalval
      by (simp add: take_bit_int_eq_self)
  qed
  done

end
end
