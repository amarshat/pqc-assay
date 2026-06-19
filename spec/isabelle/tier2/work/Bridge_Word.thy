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
end
