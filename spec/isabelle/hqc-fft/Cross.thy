theory Cross
  imports Forward HQC.AVX_Seq
begin

text \<open>The Karatsuba multipliers of FFTRef.cry (km1 = mull64 = clmul1, km2 .. km16 by kstep, km24 by
  k3step over km8) multiply.\<close>

lemma fkm1_correct: "Pl (L (FFTRef.km1 a b)) = Pl (L a) * Pl (L b)"
proof -
  have "FFTRef.km1 a b = GF2X.km1 a b" by (simp add: FFTRef.km1_def GF2X.km1_def FFTRef.mull64_def)
  then show ?thesis by (simp add: km1_correct)
qed

lemma fkm2_correct: "Pl (L (FFTRef.km2 a b)) = Pl (L a) * Pl (L b)"
  unfolding FFTRef.km2_def
  apply simp
  apply ((subst L_coerce, simp)?)
  apply (rule trans[OF kstep_correct])
       apply (simp_all add: L_coerce fkm1_correct)
  done

lemma fkm4_correct: "Pl (L (FFTRef.km4 a b)) = Pl (L a) * Pl (L b)"
  unfolding FFTRef.km4_def
  apply simp
  apply ((subst L_coerce, simp)?)
  apply (rule trans[OF kstep_correct])
       apply (simp_all add: L_coerce fkm2_correct)
  done

lemma fkm8_correct: "Pl (L (FFTRef.km8 a b)) = Pl (L a) * Pl (L b)"
  unfolding FFTRef.km8_def
  apply simp
  apply ((subst L_coerce, simp)?)
  apply (rule trans[OF kstep_correct])
       apply (simp_all add: L_coerce fkm4_correct)
  done

lemma fkm16_correct: "Pl (L (FFTRef.km16 a b)) = Pl (L a) * Pl (L b)"
  unfolding FFTRef.km16_def
  apply simp
  apply ((subst L_coerce, simp)?)
  apply (rule trans[OF kstep_correct])
       apply (simp_all add: L_coerce fkm8_correct)
  done

lemma fkm24_correct: "Pl (L (FFTRef.km24 a b)) = Pl (L a) * Pl (L b)"
  unfolding FFTRef.km24_def
  apply simp
  apply ((subst L_coerce, simp)?)
  apply (rule trans[OF k3step_correct])
       apply (simp_all add: L_coerce fkm8_correct)
  done

end
