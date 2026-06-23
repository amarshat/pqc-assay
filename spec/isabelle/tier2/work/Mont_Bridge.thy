(* Tier-2 model bridge (WIP): connect the SAW-checked montgomery NTT model
   (Assay.MLDSA_NTT.ntt, the function SAW proves the PQClean C equal to under
   -fwrapv) to the Tier-2 normal-domain model nttFwdAllRef, mod q.

   Goal:  sint_seq (ntt w @ k) == cf (nttFwdAllRef w) k   (mod q)
   chained with fwd_ntt_correct gives the SAW-checked model == FIPS-204 forward
   transform (mod q), closing the last gap in the C -> FIPS chain.

   This file is currently an ARCHITECTURE SPIKE: it only checks that the Assay
   session (montgomery_reduce_correct) and the Tier-2 session (fwd_ntt_correct)
   can be imported together. *)
theory Mont_Bridge
  imports Negacyclic_Bridge "Assay.Assay_Equivalence"
begin

text \<open>Foundation: the montgomery-domain twiddle table (Assay model \<open>zetas\<close>, stored
  signed) and the normal-domain table (Tier-2 \<open>zetabrv\<close>) agree at every index up
  to the Montgomery factor: \<open>sint(zetas[k]) \<equiv> 2^32 \<cdot> zetabrv[k] (mod q)\<close>. Both are
  the same primitive root \<open>\<zeta>=1753\<close> at bit-reversed index \<open>k\<close>; the C table is the
  Montgomery form. Proven by evaluation over the two concrete 256-entry tables.\<close>
text \<open>Index 0 is never an actual twiddle (the NTT accesses \<open>zetas[2^i + blk]\<close>, always
  \<open>\<ge> 1\<close>): there the montgomery table holds the dummy \<open>0\<close> while the normal table holds
  \<open>1\<close>, so the relation is stated for \<open>0 < k\<close>. Evaluated over the two tables' tails.\<close>
lemma zeta_rel:
  assumes k0: "0 < k" and k: "k < 256"
  shows "sint_seq (nth_seq zetas k) mod 8380417
       = (4294967296 * uint_seq (nth_seq zetabrv k)) mod 8380417"
proof -
  have L: "list_all (\<lambda>p. sint_seq (fst p) mod 8380417
                        = (4294967296 * uint_seq (snd p)) mod 8380417)
              (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)))"
    unfolding zetas_def zetabrv_def by eval
  have lz: "length (seq_to_list zetas) = 256" unfolding zetas_def by eval
  have lb: "length (seq_to_list zetabrv) = 256" unfolding zetabrv_def by eval
  define j where "j = k - 1"
  have jlt: "j < 255" using k0 k j_def by simp
  have ldz: "length (drop 1 (seq_to_list zetas)) = 255" using lz by simp
  have ldb: "length (drop 1 (seq_to_list zetabrv)) = 255" using lb by simp
  have lzip: "length (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv))) = 255"
    using ldz ldb by simp
  have app: "sint_seq (fst (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j)) mod 8380417
           = (4294967296 * uint_seq (snd (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j))) mod 8380417"
    using L jlt lzip by (simp add: list_all_length)
  have zk: "zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j
          = (drop 1 (seq_to_list zetas) ! j, drop 1 (seq_to_list zetabrv) ! j)"
    using jlt ldz ldb by (simp add: nth_zip)
  have dz: "drop 1 (seq_to_list zetas) ! j = seq_to_list zetas ! k"
    using k0 j_def by (simp add: nth_drop)
  have db: "drop 1 (seq_to_list zetabrv) ! j = seq_to_list zetabrv ! k"
    using k0 j_def by (simp add: nth_drop)
  have fz: "fst (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j)
          = seq_to_list zetas ! k"
    by (simp del: One_nat_def add: zk dz)
  have sz: "snd (zip (drop 1 (seq_to_list zetas)) (drop 1 (seq_to_list zetabrv)) ! j)
          = seq_to_list zetabrv ! k"
    by (simp del: One_nat_def add: zk db)
  have core: "sint_seq (seq_to_list zetas ! k) mod 8380417
            = (4294967296 * uint_seq (seq_to_list zetabrv ! k)) mod 8380417"
    using app by (simp del: One_nat_def add: fz sz)
  have nz: "nth_seq zetas k = seq_to_list zetas ! k" using k lz by (simp add: seq_to_list)
  have nb: "nth_seq zetabrv k = seq_to_list zetabrv ! k" using k lb by (simp add: seq_to_list)
  show ?thesis using core nz nb by simp
qed

end
