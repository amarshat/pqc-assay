theory Wire
  imports Top3 HQC.FFTWire
begin

text \<open>The HQC integration of the additive-FFT multiplier (FFTWire.cry, the vect_mul of the artifact's
  cachekey gf2x.c) computes the product modulo x^n - 1: vmulF1/3/5 a b = (a * b) mod (x^n - 1) for
  inputs of degree below n. The padding of ring_to_fftform keeps the low bytes of the last word, which
  hold every coefficient below n; mulT*_correct gives the product of the padded operands; Fold's
  fold_mult_k gives the reduction. SAW proves the C vect_mul equal to vmulF (proof/hqc-fft/wire_*.saw).\<close>

lemma Pl_pad_word:
  fixes xs :: "64 word list"
  assumes len: "length xs = Suc k" and t: "t \<le> 64" and deg: "\<And>j. 64 * k + t \<le> j \<Longrightarrow> coeff (Pl xs) j = 0"
  shows "Pl (take k xs @ [xs ! k AND mask t] @ replicate r 0) = Pl xs"
proof (rule poly_eqI)
  fix j :: nat
  define q where "q = j div 64"
  define i where "i = j mod 64"
  have j: "j = 64 * q + i" and i: "i < 64" by (simp_all add: q_def i_def)
  define ys where "ys = take k xs @ [xs ! k AND mask t] @ (replicate r 0 :: 64 word list)"
  have "bitsof ys j = bitsof xs j"
  proof (cases "q < k")
    case True
    then have "ys ! q = xs ! q" using len by (simp add: ys_def nth_append)
    then show ?thesis using True len by (simp add: bitsof_def ys_def q_def[symmetric] i_def[symmetric])
  next
    case False
    show ?thesis
    proof (cases "q = k")
      case True
      have yk: "ys ! q = xs ! k AND mask t" using True len by (simp add: ys_def nth_append)
      show ?thesis
      proof (cases "i < t")
        case True
        then show ?thesis using \<open>q = k\<close> yk len i
          by (simp add: bitsof_def ys_def q_def[symmetric] i_def[symmetric] bit_and_iff bit_mask_iff)
      next
        case False
        then have "64 * k + t \<le> j" using j \<open>q = k\<close> by simp
        then have "\<not> bitsof xs j" using deg coeff_Pl[of xs j] by simp
        moreover have "\<not> bitsof ys j" using \<open>q = k\<close> yk False
          by (simp add: bitsof_def q_def[symmetric] i_def[symmetric] bit_and_iff bit_mask_iff)
        ultimately show ?thesis by simp
      qed
    next
      case False
      then have qk: "Suc k \<le> q" using \<open>\<not> q < k\<close> by simp
      have "\<not> bitsof xs j" using qk len by (simp add: bitsof_def q_def[symmetric])
      moreover have "\<not> bitsof ys j"
      proof (cases "q < length ys")
        case True
        then have "ys ! q = 0" using qk len by (simp add: ys_def nth_append)
        then show ?thesis by (simp add: bitsof_def q_def[symmetric] i_def[symmetric])
      next
        case False then show ?thesis by (simp add: bitsof_def q_def[symmetric])
      qed
      ultimately show ?thesis by simp
    qed
  qed
  then show "coeff (Pl (take k xs @ [xs ! k AND mask t] @ replicate r 0)) j = coeff (Pl xs) j"
    by (simp add: coeff_Pl ys_def)
qed

lemma s2w_and_zip: "seq_to_word (map_seq (\<lambda>(x, y). x \<and> y) (zip_seq (p :: w64) q)) = seq_to_word p AND seq_to_word q"
  using fun_cong[OF fun_cong[OF and_seq_conv, of p], of q] by simp

lemma L_singleton: "L (list_to_seq [w] :: (1, w64) seq) = [seq_to_word w]"
  by (simp add: L_def)

lemma L_nth: "i < LEN('n) \<Longrightarrow> L (a :: ('n, w64) seq) ! i = seq_to_word (nth_seq a i)"
  by (simp add: L_def nth_seq.rep_eq)

lemma s2w_masks: "seq_to_word (0xFF :: w64) = mask 8" "seq_to_word (0xFFFF :: w64) = mask 16"
    "seq_to_word (0xFFFFFFFFFF :: w64) = mask 40"
  by (simp_all add: numeral_seq_word_conv mask_eq_exp_minus_1)

lemma deg_coeff0: "degree (p :: gf2 poly) < n \<Longrightarrow> n \<le> j \<Longrightarrow> coeff p j = 0"
  by (simp add: coeff_eq_0)

lemma L_pad1: "L (FFTWire.pad1 a) = take 276 (L a) @ [(L a ! 276) AND mask 8] @ replicate 3 0"
  by (simp add: FFTWire.pad1_def L_append L_take L_zero L_coerce L_singleton s2w_and_zip L_nth s2w_masks)

lemma Pl_pad1: "degree (Pl (L a)) < 17669 \<Longrightarrow> Pl (L (FFTWire.pad1 a)) = Pl (L a)"
  unfolding L_pad1 by (rule Pl_pad_word) (simp_all add: deg_coeff0)

lemma prod1:
  fixes a b :: "(277, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode fx = FFTEnc.encodeIdx fx"
    and dec: "\<And>fx. FFTEnc.decode fx = FFTEnc.decodeIdx fx"
    and da: "degree (Pl (L a)) < 17669" and db: "degree (Pl (L b)) < 17669"
  shows "Pl (take 554 (L (FFTTop.mulT (FFTWire.pad1 a) (FFTWire.pad1 b) (FFTTop.inputT (FFTWire.pad1 a)) (FFTTop.inputT (FFTWire.pad1 b)))))
       = Pl (L a) * Pl (L b)"
proof -
  have e: "Pl (L (FFTTop.mulT (FFTWire.pad1 a) (FFTWire.pad1 b) (FFTTop.inputT (FFTWire.pad1 a)) (FFTTop.inputT (FFTWire.pad1 b))))
      = Pl (L a) * Pl (L b)"
    by (simp add: mulT_correct[OF enc dec] Pl_pad1 da db)
  have deg: "degree (Pl (L a) * Pl (L b)) < 64 * 554"
    using da db degree_mult_le[of "Pl (L a)" "Pl (L b)"] by simp
  show ?thesis
    apply (subst Pl_take_eq)
      apply simp
     apply (simp add: e, rule coeff_eq_0, use deg in linarith)
    apply (simp add: e)
    done
qed

theorem vmulF1_correct:
  fixes a b :: "(277, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode fx = FFTEnc.encodeIdx fx"
    and dec: "\<And>fx. FFTEnc.decode fx = FFTEnc.decodeIdx fx"
    and da: "degree (Pl (L a)) < 17669" and db: "degree (Pl (L b)) < 17669"
  shows "Pl (L (FFTWire.vmulF1 a b)) = (Pl (L a) * Pl (L b)) mod (monom 1 17669 - 1)"
  unfolding FFTWire.vmulF1_def
  apply (simp add: Let_def)
  apply (rule fold_mult_k)
      apply (simp_all add: L_coerce L_take prod1[OF enc dec da db] da db)
  done

lemma L_pad3: "L (FFTWire.pad3 a) = take 560 (L a) @ [(L a ! 560) AND mask 16] @ replicate 15 0"
  by (simp add: FFTWire.pad3_def L_append L_take L_zero L_coerce L_singleton s2w_and_zip L_nth s2w_masks)

lemma Pl_pad3: "degree (Pl (L a)) < 35851 \<Longrightarrow> Pl (L (FFTWire.pad3 a)) = Pl (L a)"
  unfolding L_pad3 by (rule Pl_pad_word) (simp_all add: deg_coeff0)

lemma prod3:
  fixes a b :: "(561, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode3 fx = FFTEnc.encodeIdx3 fx"
    and dec: "\<And>fx. FFTEnc.decode3 fx = FFTEnc.decodeIdx3 fx"
    and da: "degree (Pl (L a)) < 35851" and db: "degree (Pl (L b)) < 35851"
  shows "Pl (take 1122 (L (FFTTop3.mulT3 (FFTWire.pad3 a) (FFTWire.pad3 b) (FFTTop3.inputT3 (FFTWire.pad3 a)) (FFTTop3.inputT3 (FFTWire.pad3 b)))))
       = Pl (L a) * Pl (L b)"
proof -
  have e: "Pl (L (FFTTop3.mulT3 (FFTWire.pad3 a) (FFTWire.pad3 b) (FFTTop3.inputT3 (FFTWire.pad3 a)) (FFTTop3.inputT3 (FFTWire.pad3 b))))
      = Pl (L a) * Pl (L b)"
    by (simp add: mulT3_correct[OF enc dec] Pl_pad3 da db)
  have deg: "degree (Pl (L a) * Pl (L b)) < 64 * 1122"
    using da db degree_mult_le[of "Pl (L a)" "Pl (L b)"] by simp
  show ?thesis
    apply (subst Pl_take_eq)
      apply simp
     apply (simp add: e, rule coeff_eq_0, use deg in linarith)
    apply (simp add: e)
    done
qed

theorem vmulF3_correct:
  fixes a b :: "(561, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode3 fx = FFTEnc.encodeIdx3 fx"
    and dec: "\<And>fx. FFTEnc.decode3 fx = FFTEnc.decodeIdx3 fx"
    and da: "degree (Pl (L a)) < 35851" and db: "degree (Pl (L b)) < 35851"
  shows "Pl (L (FFTWire.vmulF3 a b)) = (Pl (L a) * Pl (L b)) mod (monom 1 35851 - 1)"
  unfolding FFTWire.vmulF3_def
  apply (simp add: Let_def)
  apply (rule fold_mult_k)
      apply (simp_all add: L_coerce L_take prod3[OF enc dec da db] da db)
  done


lemma L_pad5: "L (FFTWire.pad5 a) = take 900 (L a) @ [(L a ! 900) AND mask 40] @ replicate 123 0"
  by (simp add: FFTWire.pad5_def L_append L_take L_zero L_coerce L_singleton s2w_and_zip L_nth s2w_masks)

lemma Pl_pad5: "degree (Pl (L a)) < 57637 \<Longrightarrow> Pl (L (FFTWire.pad5 a)) = Pl (L a)"
  unfolding L_pad5 by (rule Pl_pad_word) (simp_all add: deg_coeff0)

lemma prod5:
  fixes a b :: "(901, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode5 fx = FFTEnc.encodeIdx5 fx"
    and dec: "\<And>fx. FFTEnc.decode5 fx = FFTEnc.decodeIdx5 fx"
    and da: "degree (Pl (L a)) < 57637" and db: "degree (Pl (L b)) < 57637"
  shows "Pl (take 1802 (L (FFTTop5.mulT5 (FFTTop5.inputT5 (FFTWire.pad5 a)) (FFTTop5.inputT5 (FFTWire.pad5 b)))))
       = Pl (L a) * Pl (L b)"
proof -
  have e: "Pl (L (FFTTop5.mulT5 (FFTTop5.inputT5 (FFTWire.pad5 a)) (FFTTop5.inputT5 (FFTWire.pad5 b))))
      = Pl (L a) * Pl (L b)"
    by (simp add: mulT5_correct[OF enc dec] Pl_pad5 da db)
  have deg: "degree (Pl (L a) * Pl (L b)) < 64 * 1802"
    using da db degree_mult_le[of "Pl (L a)" "Pl (L b)"] by simp
  show ?thesis
    apply (subst Pl_take_eq)
      apply simp
     apply (simp add: e, rule coeff_eq_0, use deg in linarith)
    apply (simp add: e)
    done
qed

theorem vmulF5_correct:
  fixes a b :: "(901, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode5 fx = FFTEnc.encodeIdx5 fx"
    and dec: "\<And>fx. FFTEnc.decode5 fx = FFTEnc.decodeIdx5 fx"
    and da: "degree (Pl (L a)) < 57637" and db: "degree (Pl (L b)) < 57637"
  shows "Pl (L (FFTWire.vmulF5 a b)) = (Pl (L a) * Pl (L b)) mod (monom 1 57637 - 1)"
  unfolding FFTWire.vmulF5_def
  apply (simp add: Let_def)
  apply (rule fold_mult_k)
      apply (simp_all add: L_coerce L_take prod5[OF enc dec da db] da db)
  done


end
