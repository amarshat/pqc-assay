theory DivBridge
  imports IbcBridge
begin

lemma divBlock_list:
  fixes b :: "(2 \<times> 'L::len, bool) seq"
  assumes T: "2 * LENGTH('T::len) \<le> LENGTH('L)"
  defines "l \<equiv> seq_to_list b" and "lenL \<equiv> LENGTH('L)" and "lenT \<equiv> LENGTH('T)"
  defines "q \<equiv> map (\<lambda>p. fst p = (\<not> snd p)) (zip (take lenL l) (replicate (lenL - lenT) False @ take lenT l))"
  shows "seq_to_list (FFTBC.divBlock TY('L) TY('T) b)
       = q @ map (\<lambda>p. fst p = (\<not> snd p)) (zip (drop lenL l) (drop lenT q @ replicate lenT False))"
proof -
  have g: "PRED(1 \<le> 'L, (2 \<times> 'T) \<le> 'L)" using T by (simp add: Suc_le_eq)
  have T0: "0 < LENGTH('T)" by simp
  have TL: "lenT < lenL" using T T0 unfolding lenL_def lenT_def by linarith
  have n: "nat (int lenL - int lenT) = lenL - lenT" "lenL - (lenL - lenT) = lenT" using TL by simp_all
  have ll: "list_len (lenL + lenL) l = l" by (rule list_len_noop) (simp add: l_def lenL_def)
  have lenl: "length l = lenL + lenL" by (simp add: l_def lenL_def)
  have lq: "length q = lenL" using TL lenl by (simp add: q_def)
  show ?thesis using TL
    by (simp add: FFTBC.divBlock_def Let_def unguard_unfold_context[OF g] seq_to_list coerce_seq_len.rep_eq number_int
      Cryptol_Syntax.number_def left_shift_def2 right_shift_def shiftl_seq.rep_eq shiftr_seq.rep_eq shiftl_list_def
      shiftr_list_def split_def n lenL_def[symmetric] lenT_def[symmetric] l_def[symmetric] q_def[symmetric] ll lenl lq)
qed

lemma mulBlock_divBlock:
  fixes b :: "(2 \<times> 'L::len, bool) seq"
  assumes T: "2 * LENGTH('T::len) \<le> LENGTH('L)"
  shows "FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b) = b"
proof -
  define l where "l = seq_to_list b"
  define lenL where "lenL = LENGTH('L)"
  define lenT where "lenT = LENGTH('T)"
  define q where "q = map (\<lambda>p. fst p = (\<not> snd p)) (zip (take lenL l) (replicate (lenL - lenT) False @ take lenT l))"
  define r where "r = map (\<lambda>p. fst p = (\<not> snd p)) (zip (drop lenL l) (drop lenT q @ replicate lenT False))"
  have T0: "0 < LENGTH('T)" by simp
  have TL: "2 * lenT \<le> lenL" "0 < lenT" using T T0 by (simp_all add: lenL_def lenT_def)
  have lenl: "length l = 2 * lenL" by (simp add: l_def lenL_def)
  have lq: "length q = lenL" using TL lenl by (simp add: q_def)
  have lr: "length r = lenL" using TL lenl lq by (simp add: r_def)
  have dl: "seq_to_list (FFTBC.divBlock TY('L) TY('T) b) = q @ r"
    using divBlock_list[OF T] by (simp add: q_def r_def l_def lenL_def lenT_def)
  have qk: "q ! k = (l ! k \<noteq> (if k < lenL - lenT then False else l ! (k - (lenL - lenT))))" if "k < lenL" for k
    using that TL lenl by (simp add: q_def nth_append)
  have rk: "r ! k = (l ! (lenL + k) \<noteq> (if k < lenL - lenT then q ! (k + lenT) else False))" if "k < lenL" for k
    using that TL lenl lq by (simp add: r_def nth_append add.commute)
  have m: "seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b))
      = map (\<lambda>((a, b'), c). a = (\<not> b') = (\<not> c))
           (zip (zip (q @ replicate lenL False) (replicate (lenL - lenT) False @ q @ replicate lenT False))
                (replicate lenL False @ r))"
    using mulBlock_list[OF T, of "FFTBC.divBlock TY('L) TY('T) b"] lq by (simp add: dl lenL_def lenT_def)
  have "seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b)) = l"
  proof (rule nth_equalityI)
    show "length (seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b))) = length l"
      by (simp add: lenl lenL_def)
  next
    fix k assume "k < length (seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b)))"
    then have k: "k < 2 * lenL" by (simp add: lenL_def)
    have A: "(q @ replicate lenL False) ! k = (if k < lenL then q ! k else False)" using k lq by (simp add: nth_append)
    have B: "(replicate (lenL - lenT) False @ q @ replicate lenT False) ! k
        = (if k < lenL - lenT then False else if k < 2 * lenL - lenT then q ! (k - (lenL - lenT)) else False)"
      using k lq TL by (auto simp: nth_append)
    have C: "(replicate lenL False @ r) ! k = (if k < lenL then False else r ! (k - lenL))" using k lr by (simp add: nth_append)
    have lens: "length (q @ replicate lenL False) = 2 * lenL" "length (replicate (lenL - lenT) False @ q @ replicate lenT False) = 2 * lenL"
      "length (replicate lenL False @ r) = 2 * lenL" using lq lr TL by simp_all
    have val: "seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b)) ! k
        = (((if k < lenL then q ! k else False) = (\<not> (if k < lenL - lenT then False else if k < 2 * lenL - lenT then q ! (k - (lenL - lenT)) else False)))
            = (\<not> (if k < lenL then False else r ! (k - lenL))))"
      using k lens by (simp add: m nth_zip A B C)
    show "seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b)) ! k = l ! k"
    proof (cases "k < lenL")
      case True
      show ?thesis
      proof (cases "k < lenL - lenT")
        case True2: True
        then show ?thesis using True by (simp add: val qk)
      next
        case False2: False
        define i2 where "i2 = k - (lenL - lenT)"
        have k2: "i2 < lenL - lenT" using True TL by (simp add: i2_def)
        have k3: "i2 < lenL" using True by (simp add: i2_def)
        have q2: "q ! i2 = l ! i2" using qk[OF k3] k2 by simp
        have q1: "q ! k = (l ! k \<noteq> l ! i2)" using qk[OF True] False2 by (simp add: i2_def)
        have kk: "k < 2 * lenL - lenT" using True TL by linarith
        have "seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b)) ! k
            = ((q ! k = (\<not> q ! i2)) = (\<not> False))"
          using True False2 kk by (simp only: val if_True if_False i2_def[symmetric])
        then show ?thesis using q1 q2 by auto
      qed
    next
      case False
      define j where "j = k - lenL"
      have j: "j < lenL" "k = lenL + j" using k False by (simp_all add: j_def)
      have c: "k < 2 * lenL - lenT \<longleftrightarrow> j < lenL - lenT" using j TL by linarith
      have e: "k - (lenL - lenT) = j + lenT" using j TL by linarith
      have kL: "k - lenL = j" by (simp add: j_def)
      have v2: "seq_to_list (FFTBC.mulBlock TY('L) TY('T) (FFTBC.divBlock TY('L) TY('T) b)) ! k
          = ((False = (\<not> (if j < lenL - lenT then q ! (j + lenT) else False))) = (\<not> r ! j))"
        using False TL by (simp only: val c e kL if_False) (cases "k < lenL - lenT"; simp)
      show ?thesis using rk[OF j(1)] by (simp only: v2 j(2)[symmetric]) auto
    qed
  qed
  then show ?thesis by (metis l_def seq_preserved)
qed

end
