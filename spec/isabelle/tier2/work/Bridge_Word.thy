(* Tier-2 word-level bridge (WIP): reason on the SAW-anchored lifted transform
   nttFwdAllRef. First brick: the lifted foldl over the 8 (len,iter,m0) tuples
   unfolds to the explicit 8-layer composition. *)
theory Bridge_Word
  imports "Tier2_Base.fips204_ntt_lift" "Tier2_Base.Bitrev" "Tier2_Base.Negacyclic_NTT"
begin

context includes cryptol_syntax begin

lemma fwd_unfold:
  "nttFwdAllRef w =
     nttLayerFwd 1 128 127 (nttLayerFwd 2 64 63 (nttLayerFwd 4 32 31
     (nttLayerFwd 8 16 15 (nttLayerFwd 16 8 7 (nttLayerFwd 32 4 3
     (nttLayerFwd 64 2 1 (nttLayerFwd 128 1 0 w)))))))"
  unfolding nttFwdAllRef_def fwdParamsRef_def Let_def
  by (simp add: foldl_seq.rep_eq)

end

text \<open>Per-op seam: the lifted forward-butterfly add (\<open>w[j] = (w[j] + t) mod q\<close>,
  done in 64-bit then truncated to 32) computes integer addition mod q, for
  coefficients already in \<open>[0,q)\<close>. Word-level via the v1 \<open>word_seq_convs\<close> route.\<close>
text \<open>The no-overflow integer fact behind the 64-bit add-then-reduce.\<close>
lemma add_mod_aux:
  fixes A B :: int
  assumes "0 \<le> A" "A < 8380417" "0 \<le> B" "B < 8380417"
  shows "take_bit 32 ((take_bit 64 A + take_bit 64 B) mod 18446744073709551616 mod 8380417)
         = (A + B) mod 8380417"
proof -
  have tA: "take_bit 64 A = A" using assms by (simp add: take_bit_int_eq_self)
  have tB: "take_bit 64 B = B" using assms by (simp add: take_bit_int_eq_self)
  have s: "(A + B) mod 18446744073709551616 = A + B"
    using assms by (simp add: mod_pos_pos_trivial)
  have lt: "(A + B) mod 8380417 < 2 ^ 32"
    using pos_mod_bound[of 8380417 "A + B"] by simp
  have ge: "0 \<le> (A + B) mod 8380417" by simp
  show ?thesis using tA tB s lt ge by (simp add: take_bit_int_eq_self)
qed

context includes cryptol_translation_syntax begin

lemma op_add:
  fixes a b :: "[32]"
  assumes "uint_seq a < 8380417" and "uint_seq b < 8380417"
  shows "uint_seq (drop`{32,32,Bit}
            (((zext`{64,32} a) +`{[64]} (zext`{64,32} b)) %`{[64]} q))
         = (uint_seq a + uint_seq b) mod 8380417"
  using assms
  apply (simp add: cryptol_prim_defs word_seq_convs q_def)
  apply (simp add: unsigned_ucast_eq unsigned_take_bit_eq uint_up_ucast is_up
                   uint_mod_distrib uint_word_ariths)
  apply (rule add_mod_aux)
  apply simp_all
  done

end
end
