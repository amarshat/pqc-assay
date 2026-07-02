theory Barrett_Bridge
  imports Barrett_Lift Barrett_Core "Word_Lib.Word_Lemmas"
begin

text \<open>Route Y word-level bridge (WIP). Goal: barrettBV_bridge x, i.e.
  x < 2^46 \<longrightarrow> barrettBV x = drop`{96} ((zext x) mod q).

  Unfolding the lifted definitions and simplifying the Cryptol image ops
  (simp add: cryptol_prim_defs word_seq_convs) reduces the goal to a pure
  Isabelle-Word statement (smallReduce already case-split), over w = seq_to_word x:

    (q \<le> R \<longrightarrow> w < 1<<46 \<longrightarrow> R - q = ucast (take_bit 32 (ucast (ucast w mod q))))
  \<and> (\<not> q \<le> R \<longrightarrow> w < 1<<46 \<longrightarrow> R     = ucast (take_bit 32 (ucast (ucast w mod q))))
    where R = UCAST(128\<rightarrow>32) (take_bit 32
                (UCAST(64\<rightarrow>128) w - (UCAST(64\<rightarrow>128) w * 0x802007 >> 46) * 0x7FE001))
          q = 0x7FE001 = 8380417,  0x802007 = 8396807 = floor(2^46/q).

  Remaining: push unat through the word ops onto Barrett_Core (the integer identity,
  already proven), discharging the standard Word_Lib side conditions. This REPLACES
  the nine bvToInt homomorphisms admitted in the SAW spike (spike2_lift.saw) with
  proven Word_Lib lemmas (algebra + induction, no bit-blast):
    - UCAST(64\<rightarrow>128) w  :  unat_ucast_up_simp        (zext, unat preserved)
    - _ * 0x802007      :  unat_mult_lem             (no overflow: n*M < 2^69 < 2^128)
    - _ >> 46           :  shiftr_div_2n_w           (shiftr = div 2^46)
    - _ * 0x7FE001      :  unat_mult_lem             (no overflow)
    - _ - _             :  unat_sub                  (no underflow: quotient*q \<le> n, Barrett)
    - take_bit 32 / ucast:  unat_ucast / take_bit    (remainder < 2q < 2^32, lossless)
    - _ mod q           :  unat_mod_distrib          (urem)
    - q \<le> _, _ < _      :  word_le_nat_alt, word_less_nat_alt (comparison reflections)
  then Barrett_Core closes the resulting nat/int identity. Companion escape2 note:
  paper/notes/escape2-lift-plan.md.\<close>

context includes cryptol_syntax begin

theorem barrettBV_bridge_holds: "barrettBV_bridge x"
  unfolding barrettBV_bridge_def barrettBV_def smallReduce_def q_def barrettMult_def Let_def
  apply (simp add: cryptol_prim_defs word_seq_convs)
  oops

end
end
