theory Uncond
  imports Wire EncDec
begin

text \<open>The additive-FFT results with their two hypotheses discharged. mulT_correct, mulT3_correct,
  mulT5_correct and vmulF1/3/5_correct assume encode<p> = encodeIdx<p> and decode<p> = decodeIdx<p>;
  EncDec proves both at each size, so the theorems below hold with no hypothesis beyond the degree
  bounds of the HQC integration.\<close>

context includes cryptol_syntax begin

theorem mulT_correct_unc:
  fixes a b :: "(280, w64) seq"
  shows "Pl (L (FFTTop.mulT a b (FFTTop.inputT a) (FFTTop.inputT b))) = Pl (L a) * Pl (L b)"
  by (rule Assemble.mulT_correct[OF encode_eq_encodeIdx decode_eq_decodeIdx])

theorem mulT3_correct_unc:
  fixes a b :: "(576, w64) seq"
  shows "Pl (L (FFTTop3.mulT3 a b (FFTTop3.inputT3 a) (FFTTop3.inputT3 b))) = Pl (L a) * Pl (L b)"
  by (rule Top3.mulT3_correct[OF encode3_eq_encodeIdx3 decode3_eq_decodeIdx3])

theorem mulT5_correct_unc:
  fixes a b :: "(1024, w64) seq"
  shows "Pl (L (FFTTop5.mulT5 (FFTTop5.inputT5 a) (FFTTop5.inputT5 b))) = Pl (L a) * Pl (L b)"
  by (rule Top5.mulT5_correct[OF encode5_eq_encodeIdx5 decode5_eq_decodeIdx5])

theorem vmulF1_correct_unc:
  fixes a b :: "(277, w64) seq"
  assumes da: "degree (Pl (L a)) < 17669" and db: "degree (Pl (L b)) < 17669"
  shows "Pl (L (FFTWire.vmulF1 a b)) = (Pl (L a) * Pl (L b)) mod (monom 1 17669 - 1)"
  by (rule Wire.vmulF1_correct[OF encode_eq_encodeIdx decode_eq_decodeIdx da db])

theorem vmulF3_correct_unc:
  fixes a b :: "(561, w64) seq"
  assumes da: "degree (Pl (L a)) < 35851" and db: "degree (Pl (L b)) < 35851"
  shows "Pl (L (FFTWire.vmulF3 a b)) = (Pl (L a) * Pl (L b)) mod (monom 1 35851 - 1)"
  by (rule Wire.vmulF3_correct[OF encode3_eq_encodeIdx3 decode3_eq_decodeIdx3 da db])

theorem vmulF5_correct_unc:
  fixes a b :: "(901, w64) seq"
  assumes da: "degree (Pl (L a)) < 57637" and db: "degree (Pl (L b)) < 57637"
  shows "Pl (L (FFTWire.vmulF5 a b)) = (Pl (L a) * Pl (L b)) mod (monom 1 57637 - 1)"
  by (rule Wire.vmulF5_correct[OF encode5_eq_encodeIdx5 decode5_eq_decodeIdx5 da db])

end

end
