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

text \<open>Brick (b): the montgomery_reduce mod-q property, as a congruence usable by the
  bridge. This is the first conjunct of \<open>is_montgomery_reduction\<close> (proven in the Assay
  session as \<open>montgomery_reduce_correct\<close>): the reduced value scaled by the Montgomery
  factor \<open>2^32\<close> is congruent to the input modulo \<open>q\<close>.\<close>
lemma mont_mod_q:
  fixes a :: "(64, bool) seq"
  assumes "mont_input_ok (sint_seq a)"
  shows "(4294967296 * sint_seq (montgomery_reduce a)) mod 8380417 = sint_seq a mod 8380417"
proof -
  have "is_montgomery_reduction (sint_seq a) (sint_seq (montgomery_reduce a))"
    using assms by (rule montgomery_reduce_correct)
  thus ?thesis
    unfolding is_montgomery_reduction_def MLDSA_NTT_Spec.q_def by simp
qed

text \<open>Brick (c): the per-butterfly congruence. The montgomery butterfly term computed
  by the C model with the Montgomery twiddle \<open>zetas[i]\<close> is congruent, modulo \<open>q\<close>, to the
  normal-domain product \<open>zetabrv[i] \<cdot> x\<close> used by the Tier-2 model. Combines (a) \<open>zeta_rel\<close>
  with (b) \<open>mont_mod_q\<close> and cancels the Montgomery factor \<open>2^32\<close> (coprime to the prime
  \<open>q\<close>). The bound hypothesis \<open>mont_input_ok\<close> is discharged per-layer in brick (d) from a
  coefficient-size invariant.\<close>
lemma butterfly_cong:
  fixes x :: "(32, bool) seq"
  assumes i0: "0 < i" and i: "i < 256"
      and ok: "mont_input_ok (sint_seq (nth_seq zetas i) * sint_seq x)"
  shows "sint_seq (montgomery_reduce (sext64 (nth_seq zetas i) * sext64 x)) mod 8380417
       = (uint_seq (nth_seq zetabrv i) * sint_seq x) mod 8380417"
proof -
  define z  where "z  = nth_seq zetas i"
  define zb where "zb = uint_seq (nth_seq zetabrv i)"
  define sx where "sx = sint_seq x"
  define mr where "mr = sint_seq (montgomery_reduce (sext64 z * sext64 x))"
  \<comment> \<open>goal is now: \<open>mr mod 8380417 = (zb * sx) mod 8380417\<close>\<close>
  have ok2: "mont_input_ok (sint_seq (sext64 z * sext64 x))"
    using ok by (simp add: z_def sx_def sint_sext64_mult)
  have b: "(4294967296 * mr) mod 8380417 = (sint_seq z * sx) mod 8380417"
    using mont_mod_q[OF ok2] by (simp add: mr_def sx_def sint_sext64_mult)
  have zr: "sint_seq z mod 8380417 = (4294967296 * zb) mod 8380417"
    using zeta_rel[OF i0 i] by (simp add: z_def zb_def)
  have e: "(sint_seq z * sx) mod 8380417 = (4294967296 * (zb * sx)) mod 8380417"
  proof -
    have "(sint_seq z * sx) mod 8380417 = ((sint_seq z mod 8380417) * sx) mod 8380417"
      by (simp add: mod_mult_left_eq)
    also have "\<dots> = (((4294967296 * zb) mod 8380417) * sx) mod 8380417"
      by (simp add: zr)
    also have "\<dots> = ((4294967296 * zb) * sx) mod 8380417"
      by (simp add: mod_mult_left_eq)
    also have "\<dots> = (4294967296 * (zb * sx)) mod 8380417"
      by (simp add: mult.assoc)
    finally show ?thesis .
  qed
  have comb: "(4294967296 * mr) mod 8380417 = (4294967296 * (zb * sx)) mod 8380417"
    using b e by simp
  have cop: "coprime (4294967296::int) 8380417"
  proof -
    have "gcd (4294967296::int) 8380417 = 1" by eval
    thus ?thesis by (simp add: coprime_iff_gcd_eq_1)
  qed
  have cong1: "[4294967296 * mr = 4294967296 * (zb * sx)] (mod 8380417)"
    using comb by (simp add: cong_def)
  have "[mr = zb * sx] (mod 8380417)"
    using cong1 cop by (simp add: cong_mult_lcancel)
  thus "mr mod 8380417 = (zb * sx) mod 8380417"
    by (simp add: cong_def)
qed

end
