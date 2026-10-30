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

end
