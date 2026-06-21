(* Tier-2 final bridge (WIP): the lifted forward NTT computes the FIPS-204
   negacyclic transform in bit-reversed output order.

   Target theorem (route A, self-contained closed form):
     cf (nttFwdAllRef w) k
       = (\<Sum>j<256. cf w j * 1753^((2*(brv 8 k)+1)*j)) mod 8380417   (k<256, bounded w)

   i.e. output position k holds the negacyclic DFT coefficient at index brv 8 k.
   This matches FIPS-204's bit-reversed forward-NTT convention (zeta = 1753, the
   primitive 512th root of unity mod q = 8380417).

   We build on `fwd_as_bfly` (CT_Routing): the lifted NTT already equals the
   8-fold abstract butterfly `fwdBfly` on the int-coefficient view, so the rest
   is a pure int-mod-q partial-sum invariant over the DIF butterfly layers.

   This file is WIP: it currently establishes the foundational facts only. The
   central invariant is NOT yet proven; nothing here is admitted with sorry. *)
theory Negacyclic_Bridge
  imports CT_Routing
begin

text \<open>The primitive root and modulus, as int.\<close>
abbreviation (input) qq :: int where "qq \<equiv> 8380417"
abbreviation (input) zr :: int where "zr \<equiv> 1753"

text \<open>Foundation: the lifted twiddle table holds real powers of the root in
  bit-reversed index order: \<open>zt j = zr ^ (brv 8 j) mod q\<close>. Proven by evaluation
  over the concrete 256-entry table (same device as \<open>zeta_bound\<close>).\<close>

lemma zt_eval_pow:
  "\<forall>i<256. uint_seq (nth_seq zetabrv i) = (zr ^ (brv 8 i)) mod qq"
  by eval

lemma zt_pow:
  assumes "j < 256"
  shows "zt j = (zr ^ (brv 8 j)) mod qq"
  using zt_eval_pow assms by (simp add: zt_def)

text \<open>Range of the twiddle power (re-derived from the closed form; matches the
  existing \<open>zeta_bound\<close>).\<close>
lemma zt_ge0: "j < 256 \<Longrightarrow> 0 \<le> zt j"
  by (simp add: zt_pow)

lemma zt_lt: "j < 256 \<Longrightarrow> zt j < qq"
  by (simp add: zt_pow)

end
