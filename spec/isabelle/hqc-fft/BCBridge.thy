theory BCBridge
  imports IStageBridge "HQC_FFT_Math.IConv" HQC.FFTBC
begin

lemma pw_unsigned: "pw (unsigned (w :: 'a :: len word) :: 'b :: len word) = poly_cutoff LENGTH('b) (pw w)"
  by (rule poly_eqI) (auto simp: coeff_pw coeff_poly_cutoff bit_simps dest: bit_imp_le_length)

lemma mulBlock_list:
  fixes b :: "(2 \<times> 'L::len, bool) seq"
  assumes T: "2 * LENGTH('T::len) \<le> LENGTH('L)"
  shows "seq_to_list (FFTBC.mulBlock TY('L) TY('T) b)
       = map (\<lambda>((a, b'), c). a = (\<not> b') = (\<not> c))
           (zip (zip (take LENGTH('L) (seq_to_list b) @ replicate LENGTH('L) False)
                     (replicate (LENGTH('L) - LENGTH('T)) False @ take LENGTH('L) (seq_to_list b) @ replicate LENGTH('T) False))
                (replicate LENGTH('L) False @ drop LENGTH('L) (seq_to_list b)))"
proof -
  have g: "PRED(1 \<le> 'L, (2 \<times> 'T) \<le> 'L)" using T by (simp add: Suc_le_eq)
  have tl: "LENGTH('T) - LENGTH('L) = 0" "min LENGTH('T) (LENGTH('L) + LENGTH('L)) = LENGTH('T)" using T by simp_all
  show ?thesis
    by (simp add: FFTBC.mulBlock_def Let_def unguard_unfold_context[OF g] seq_to_list coerce_seq_len.rep_eq number_int
      left_shift_def2 shiftl_seq.rep_eq shiftl_list_def tl split_def)
qed

lemma bit_mulBlock:
  fixes b :: "(2 \<times> 'L::len, bool) seq"
  assumes T: "2 * LENGTH('T::len) \<le> LENGTH('L)"
  shows "bit (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b)) i
     \<longleftrightarrow> i < 2 * LENGTH('L) \<and> (bit (seq_to_word b) i \<noteq>
           (LENGTH('T) \<le> i \<and> i < LENGTH('L) + LENGTH('T) \<and> bit (seq_to_word b) (i - LENGTH('T) + LENGTH('L))))"
proof -
  define L where "L = LENGTH('L)"
  define T' where "T' = LENGTH('T)"
  define l where "l = seq_to_list b"
  have ll: "length l = 2 * L" by (simp add: l_def L_def)
  have TL: "2 * T' \<le> L" using T by (simp add: T'_def L_def)
  show ?thesis
  proof (cases "i < 2 * L")
    case False then show ?thesis by (simp add: bit_s2w L_def)
  next
    case True
    define k where "k = 2 * L - Suc i"
    have k: "k < 2 * L" using True by (simp add: k_def)
    have bb: "\<And>j. j < 2 * L \<Longrightarrow> bit (seq_to_word b) j = l ! (2 * L - Suc j)"
      by (simp add: bit_s2w l_def L_def)
    have res: "bit (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b)) i
        = (map (\<lambda>((a, b'), c). a = (\<not> b') = (\<not> c))
           (zip (zip (take L l @ replicate L False)
                     (replicate (L - T') False @ take L l @ replicate T' False))
                (replicate L False @ drop L l))) ! k"
      using True by (simp add: bit_s2w mulBlock_list[OF T] L_def T'_def l_def k_def)
    have A: "(take L l @ replicate L False) ! k = (if k < L then l ! k else False)"
      using ll k by (simp add: nth_append)
    have B: "(replicate (L - T') False @ take L l @ replicate T' False) ! k
        = (if k < L - T' then False else if k < 2 * L - T' then l ! (k - (L - T')) else False)"
      using ll k TL by (auto simp: nth_append)
    have C: "(replicate L False @ drop L l) ! k = (if k < L then False else l ! k)"
      using ll k by (auto simp: nth_append)
    have lens: "length (take L l @ replicate L False) = 2 * L"
      "length (replicate (L - T') False @ take L l @ replicate T' False) = 2 * L"
      "length (replicate L False @ drop L l) = 2 * L" using ll TL by simp_all
    have r: "bit (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b)) i
        = (((if k < L then l ! k else False) = (\<not> (if k < L - T' then False else if k < 2 * L - T' then l ! (k - (L - T')) else False)))
             = (\<not> (if k < L then False else l ! k)))"
      using res k lens by (simp add: nth_zip A B C)
    have bi: "bit (seq_to_word b) i = l ! k" using bb[OF True] by (simp add: k_def)
    have bj: "bit (seq_to_word b) (i - T' + L) = l ! (k - (L - T'))" if "T' \<le> i" "i < L + T'"
    proof -
      have "i - T' + L < 2 * L" using that TL by linarith
      then have "bit (seq_to_word b) (i - T' + L) = l ! (2 * L - Suc (i - T' + L))" by (rule bb)
      also have "2 * L - Suc (i - T' + L) = k - (L - T')" using that TL True by (simp add: k_def)
      finally show ?thesis .
    qed
    have c1: "k < L \<longleftrightarrow> L \<le> i" using True unfolding k_def by arith
    have c2: "k < L - T' \<longleftrightarrow> L + T' \<le> i" using True TL unfolding k_def by arith
    have c3: "k < 2 * L - T' \<longleftrightarrow> T' \<le> i" using True TL unfolding k_def by arith
    define P where "P = l ! k"
    define Q where "Q = l ! (k - (L - T'))"
    have r': "bit (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b)) i
        = (((if L \<le> i then P else False) = (\<not> (if L + T' \<le> i then False else if T' \<le> i then Q else False)))
             = (\<not> (if L \<le> i then False else P)))"
      by (simp only: r c1 c2 c3 P_def Q_def)
    have bQ: "T' \<le> i \<Longrightarrow> i < L + T' \<Longrightarrow> bit (seq_to_word b) (i - T' + L) = Q"
      by (simp only: bj Q_def)
    have goal: "(((if L \<le> i then P else False) = (\<not> (if L + T' \<le> i then False else if T' \<le> i then Q else False)))
             = (\<not> (if L \<le> i then False else P)))
        = (P \<noteq> (T' \<le> i \<and> i < L + T' \<and> Q))"
      by (cases "L \<le> i"; cases "L + T' \<le> i"; cases "T' \<le> i") auto
    have "bit (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b)) i
        = (bit (seq_to_word b) i \<noteq> (T' \<le> i \<and> i < L + T' \<and> bit (seq_to_word b) (i - T' + L)))"
      using bQ by (simp only: r' goal bi P_def[symmetric]) blast
    then show ?thesis using True by (simp add: L_def T'_def)
  qed
qed

lemma gf2_of_bool_xor: "(of_bool (a \<noteq> b) :: gf2) = of_bool a + of_bool b"
  by (cases a; cases b) simp_all

lemma pw_mulBlock:
  fixes b :: "(2 \<times> 'L::len, bool) seq"
  assumes T: "2 * LENGTH('T::len) \<le> LENGTH('L)"
  shows "pw (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b)) = BC.mulBlock LENGTH('L) LENGTH('T) (pw (seq_to_word b))"
proof (rule poly_eqI)
  fix i
  define L where "L = LENGTH('L)"
  define T' where "T' = LENGTH('T)"
  define f where "f = pw (seq_to_word b)"
  define B where "B = seq_to_word b"
  have fb: "coeff f j = of_bool (bit B j)" for j by (simp add: f_def B_def coeff_pw)
  have fz: "\<not> bit B j" if "j \<ge> 2 * L" for j using that by (simp add: B_def bit_s2w L_def)
  have TL: "2 * T' \<le> L" using T by (simp add: L_def T'_def)
  have lhs: "coeff (pw (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b))) i
      = of_bool (i < 2 * L \<and> (bit B i \<noteq> (T' \<le> i \<and> i < L + T' \<and> bit B (i - T' + L))))"
    by (simp add: coeff_pw bit_mulBlock[OF T] L_def T'_def B_def)
  have rhs: "coeff (BC.mulBlock L T' f) i
      = (if i < L then 0 else coeff f i) + (if i < T' then 0 else coeff f (i - T' + L)) + (if i < L then coeff f i else 0)"
  proof -
    have "coeff (BC.mulBlock L T' f) i
        = coeff (monom 1 L * poly_shift L f) i + coeff (monom 1 T' * poly_shift L f) i + coeff (poly_cutoff L f) i"
      by (simp only: BC.mulBlock_def distrib_left coeff_add mult.commute)
    also have "\<dots> = (if i < L then 0 else coeff f i) + (if i < T' then 0 else coeff f (i - T' + L)) + (if i < L then coeff f i else 0)"
      by (simp add: coeff_monom_mult coeff_poly_shift coeff_poly_cutoff)
    finally show ?thesis .
  qed
  have "coeff (pw (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b))) i = coeff (BC.mulBlock L T' f) i"
  proof (cases "i < 2 * L")
    case False
    have a: "\<not> bit B i" using False fz by simp
    have c: "\<not> bit B (i - T' + L)" if "T' \<le> i" using False that TL by (intro fz) linarith
    show ?thesis using False a c TL by (simp add: lhs rhs fb)
  next
    case True
    show ?thesis
    proof (cases "T' \<le> i \<and> i < L + T'")
      case True2: True
      then show ?thesis using True TL
        by (cases "i < L") (simp_all add: lhs rhs fb gf2_of_bool_xor)
    next
      case False2: False
      have z: "\<not> bit B (i - T' + L)" if "T' \<le> i" using False2 that TL by (intro fz) linarith
      show ?thesis using True False2 z
        by (cases "i < L"; cases "T' \<le> i") (simp_all add: lhs rhs fb gf2_of_bool_xor)
    qed
  qed
  then show "coeff (pw (seq_to_word (FFTBC.mulBlock TY('L) TY('T) b))) i = coeff (BC.mulBlock LENGTH('L) LENGTH('T) (pw (seq_to_word b))) i"
    by (simp add: L_def T'_def f_def)
qed

text \<open>A layer: the bit vector cut (most significant first) into K blocks of W bits, a block map
  applied to each. Block g of the list is block K - 1 - g of the polynomial.\<close>

lemma coeff_layer_list:
  fixes v :: "('n::len, bool) seq" and hb :: "('w::len, bool) seq \<Rightarrow> ('w, bool) seq"
  assumes N: "LENGTH('n) = K * LENGTH('w)" and i: "i < LENGTH('n)"
  defines "W \<equiv> LENGTH('w)"
  shows "concat (map (seq_to_list \<circ> hb \<circ> list_to_seq) (group_list K W (seq_to_list v))) ! (LENGTH('n) - Suc i)
       = bit (seq_to_word (hb (list_to_seq (group_list K W (seq_to_list v) ! (K - Suc (i div W)))))) (i mod W)"
proof -
  define l where "l = seq_to_list v"
  have W0: "0 < W" by (simp add: W_def)
  have ll: "length l = K * W" by (simp add: l_def N W_def)
  have lg: "\<forall>x\<in>set (map (seq_to_list \<circ> hb \<circ> list_to_seq) (group_list K W l)). length x = W"
    by (auto simp: W_def)
  define m where "m = LENGTH('n) - Suc i"
  have m: "m < length (map (seq_to_list \<circ> hb \<circ> list_to_seq) (group_list K W l)) * W"
    using i N by (simp add: m_def W_def)
  have id: "i div W < K" using i N by (simp add: W_def less_mult_imp_div_less)
  have md: "m div W = K - Suc (i div W)" and mm: "m mod W = W - Suc (i mod W)"
  proof -
    define q where "q = i div W"
    define r where "r = i mod W"
    have iq: "i = q * W + r" by (simp add: q_def r_def)
    have rW: "r < W" using W0 by (simp add: r_def)
    have k1: "K * W = (K - Suc q) * W + q * W + W"
    proof -
      have "K = (K - Suc q) + Suc q" using id by (simp add: q_def)
      then have "K * W = ((K - Suc q) + Suc q) * W" by simp
      also have "\<dots> = (K - Suc q) * W + q * W + W" by (simp add: algebra_simps)
      finally show ?thesis .
    qed
    have mN: "m = K * W - Suc i" by (simp add: m_def N W_def)
    have e: "m = (K - Suc (i div W)) * W + (W - Suc (i mod W))"
      unfolding q_def[symmetric] r_def[symmetric] using mN k1 iq rW by linarith
    have b: "W - Suc (i mod W) < W" using W0 by simp
    show "m div W = K - Suc (i div W)" "m mod W = W - Suc (i mod W)" by (simp_all only: e div_blk[OF b] mod_blk[OF b])
  qed
  have "concat (map (seq_to_list \<circ> hb \<circ> list_to_seq) (group_list K W l)) ! m
      = (map (seq_to_list \<circ> hb \<circ> list_to_seq) (group_list K W l)) ! (m div W) ! (m mod W)"
    by (rule nth_concat_eq_len[OF lg m])
  also have "\<dots> = seq_to_list (hb (list_to_seq (group_list K W l ! (K - Suc (i div W))))) ! (W - Suc (i mod W))"
    using id by (simp add: md mm)
  also have "\<dots> = bit (seq_to_word (hb (list_to_seq (group_list K W l ! (K - Suc (i div W)))))) (i mod W)"
    using W0 by (simp add: bit_s2w W_def)
  finally show ?thesis by (simp add: l_def m_def)
qed

lemma pw_group_block:
  fixes v :: "('n::len, bool) seq"
  assumes N: "LENGTH('n) = K * LENGTH('w::len)" and j: "j < K"
  shows "pw (seq_to_word (list_to_seq (group_list K LENGTH('w) (seq_to_list v) ! (K - Suc j)) :: ('w, bool) seq))
       = blk LENGTH('w) j (pw (seq_to_word v))"
proof (rule poly_eqI)
  fix r
  define W where "W = LENGTH('w)"
  define l where "l = seq_to_list v"
  have ll: "length l = K * W" by (simp add: l_def N W_def)
  have W0: "0 < W" by (simp add: W_def)
  have g: "group_list K W l ! (K - Suc j) = take W (drop ((K - Suc j) * W) l)"
    using ll j by (simp add: group_list_part)
  have lg: "length (group_list K W l ! (K - Suc j)) = W" using ll j by simp
  show "coeff (pw (seq_to_word (list_to_seq (group_list K LENGTH('w) (seq_to_list v) ! (K - Suc j)) :: ('w, bool) seq))) r
      = coeff (blk LENGTH('w) j (pw (seq_to_word v))) r"
  proof (cases "r < W")
    case False then show ?thesis by (simp add: coeff_pw bit_s2w blk_def coeff_poly_cutoff W_def)
  next
    case True
    have idx: "(K - Suc j) * W + (W - Suc r) = K * W - Suc (W * j + r)"
    proof -
      have "K * W = (K - Suc j) * W + j * W + W"
      proof -
        have "K = (K - Suc j) + Suc j" using j by simp
        then have "K * W = ((K - Suc j) + Suc j) * W" by simp
        then show ?thesis by (simp add: algebra_simps)
      qed
      then show ?thesis using True by (simp add: algebra_simps)
    qed
    have bnd: "W * j + r < K * W"
    proof -
      have "W * j + r < W * j + W" using True by simp
      also have "\<dots> = W * Suc j" by simp
      also have "\<dots> \<le> W * K" using j by (intro mult_le_mono2) simp
      finally show ?thesis by (simp add: mult.commute)
    qed
    have "coeff (pw (seq_to_word (list_to_seq (group_list K W l ! (K - Suc j)) :: ('w, bool) seq))) r
        = of_bool ((group_list K W l ! (K - Suc j)) ! (W - Suc r))"
      using True lg by (simp add: coeff_pw bit_s2w W_def)
    also have "\<dots> = of_bool (l ! ((K - Suc j) * W + (W - Suc r)))"
      using True ll j by (simp add: g)
    also have "\<dots> = of_bool (bit (seq_to_word v) (W * j + r))"
      using bnd by (simp only: idx) (simp add: bit_s2w l_def N W_def)
    also have "\<dots> = coeff (blk W j (pw (seq_to_word v))) r"
      using True by (simp add: blk_def coeff_poly_cutoff coeff_poly_shift coeff_pw add.commute)
    finally show ?thesis by (simp add: W_def l_def)
  qed
qed

lemma bnd_pw: "bnd LENGTH('a) (pw (w :: 'a :: len word))"
  by (simp add: bnd_def coeff_pw_ge)

theorem pw_layer:
  fixes v :: "('n::len, bool) seq" and hb :: "('w::len, bool) seq \<Rightarrow> ('w, bool) seq"
  assumes N: "LENGTH('n) = K * LENGTH('w)" and H: "\<And>u. pw (seq_to_word (hb u)) = H (pw (seq_to_word u))"
  shows "pw (seq_to_word (list_to_seq (concat (map (seq_to_list \<circ> hb \<circ> list_to_seq)
            (group_list K LENGTH('w) (seq_to_list v)))) :: ('n, bool) seq))
       = bmap K LENGTH('w) H (pw (seq_to_word v))"
proof (rule poly_eqI)
  fix i
  define W where "W = LENGTH('w)"
  define f where "f = pw (seq_to_word v)"
  define CL where "CL = concat (map (seq_to_list \<circ> hb \<circ> list_to_seq) (group_list K W (seq_to_list v)))"
  define blkg where "blkg = (\<lambda>j. list_to_seq (group_list K W (seq_to_list v) ! (K - Suc j)) :: ('w, bool) seq)"
  have W0: "0 < W" by (simp add: W_def)
  have lCL: "length CL = LENGTH('n)"
    by (simp add: CL_def length_concat comp_def map_replicate_const sum_list_replicate N W_def)
  have Hb: "H (blk W j f) = pw (seq_to_word (hb (blkg j)))" if "j < K" for j
    using pw_group_block[OF N that] H by (simp add: blkg_def W_def f_def)
  have bH: "bnd W (H (blk W j f))" if "j < K" for j
  proof -
    have "bnd W (pw (seq_to_word (hb (blkg j))))" unfolding W_def by (rule bnd_pw)
    then show ?thesis by (simp only: Hb[OF that])
  qed
  have rhs: "coeff (bmap K W H f) i = (if i div W < K then coeff (H (blk W (i div W) f)) (i mod W) else 0)"
  proof -
    have "coeff (bmap K W H f) i = coeff (\<Sum>j<K. H (blk W j f) * monom 1 (W * j)) (W * (i div W) + i mod W)"
      by (simp add: bmap_def mult.commute[of W])
    also have "\<dots> = (if i div W < K then coeff (H (blk W (i div W) f)) (i mod W) else 0)"
      by (rule coeff_packed) (simp_all add: bH W0)
    finally show ?thesis .
  qed
  show "coeff (pw (seq_to_word (list_to_seq CL :: ('n, bool) seq))) i = coeff (bmap K LENGTH('w) H (pw (seq_to_word v))) i"
  proof (cases "i < LENGTH('n)")
    case False
    then have "K * W \<le> i" using N by (simp add: W_def)
    then have "K * W div W \<le> i div W" by (rule div_le_mono)
    then have "\<not> i div W < K" using W0 by simp
    then show ?thesis using False by (simp add: coeff_pw bit_s2w rhs[unfolded W_def f_def] W_def CL_def)
  next
    case True
    have id: "i div W < K" using True N by (simp add: W_def less_mult_imp_div_less)
    have "coeff (pw (seq_to_word (list_to_seq CL :: ('n, bool) seq))) i = of_bool (CL ! (LENGTH('n) - Suc i))"
      using True lCL by (simp add: coeff_pw bit_s2w)
    also have "\<dots> = of_bool (bit (seq_to_word (hb (blkg (i div W)))) (i mod W))"
      using coeff_layer_list[OF N True, of hb] by (simp add: CL_def blkg_def W_def)
    also have "\<dots> = coeff (H (blk W (i div W) f)) (i mod W)"
      by (simp add: Hb[OF id] coeff_pw)
    finally show ?thesis using id by (simp add: rhs[unfolded W_def f_def] W_def f_def CL_def)
  qed
qed

theorem pw_mulLayer:
  fixes v :: "('k::len \<times> 2 \<times> 'L::len, bool) seq"
  assumes T: "2 * LENGTH('T::len) \<le> LENGTH('L)"
  shows "pw (seq_to_word (FFTBC.mulLayer TY('k) TY('L) TY('T) v))
       = bmap LENGTH('k) (2 * LENGTH('L)) (BC.mulBlock LENGTH('L) LENGTH('T)) (pw (seq_to_word v))"
proof -
  have g: "PRED(1 \<le> 'L, (2 \<times> 'T) \<le> 'L)" using T by (simp add: Suc_le_eq)
  have l: "seq_to_list (FFTBC.mulLayer TY('k) TY('L) TY('T) v)
      = concat (map (seq_to_list \<circ> (FFTBC.mulBlock TY('L) TY('T) \<circ> list_to_seq))
          (group_list LENGTH('k) (2 * LENGTH('L)) (seq_to_list v)))"
    by (simp add: FFTBC.mulLayer_def unguard_unfold_context[OF g] seq_to_list)
  have e: "FFTBC.mulLayer TY('k) TY('L) TY('T) v
      = list_to_seq (concat (map (seq_to_list \<circ> FFTBC.mulBlock TY('L) TY('T) \<circ> list_to_seq)
          (group_list LENGTH('k) (2 * LENGTH('L)) (seq_to_list v))))"
    by (metis l seq_preserved comp_assoc)
  show ?thesis
    unfolding e
    by (rule pw_layer[where 'w="2 \<times> 'L", simplified]) (simp_all add: pw_mulBlock[OF T])
qed

end
