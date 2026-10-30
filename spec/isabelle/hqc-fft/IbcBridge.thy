theory IbcBridge
  imports BCBridge "HQC_FFT_Math.Flatten"
begin

instance bit :: char2
  by standard simp

lemma pw_coerce:
  "LENGTH('m) = LENGTH('n) \<Longrightarrow> pw (seq_to_word (coerce_seq_len (x :: ('n::len, bool) seq) :: ('m::len, bool) seq)) = pw (seq_to_word x)"
  by (simp add: seq_to_word.coerce_seq_len pw_ucast cutoff_pw)

lemma irepr32768_pw:
  fixes v :: "(32768, bool) seq"
  shows "pw (seq_to_word (FFTBC.irepr32768 v))
       = apl [(64,256,1),(32,512,2),(16,1024,4),(8,2048,8),(4,4096,16),(2,8192,32),(1,16384,64)] (pw (seq_to_word v))"
  by (simp add: FFTBC.irepr32768_def pw_coerce pw_mulLayer lay_def)

lemma ibc256of32768_pw:
  fixes v :: "(32768, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc256of32768 v))
       = apl [(32,512,256),(8,2048,1024),(16,1024,256),(8,2048,512),(2,8192,4096),(1,16384,4096),(4,4096,256),(2,8192,512),(1,16384,1024)]
             (pw (seq_to_word v))"
  by (simp add: FFTBC.ibc256of32768_def pw_coerce pw_mulLayer lay_def)

lemma ibc1of256_128_pw:
  fixes v :: "(256 \<times> 128, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc1of256 TY(128) v))
       = apl [(8192,2,1),(2048,8,4),(4096,4,1),(2048,8,2),(512,32,16),(128,128,64),(256,64,16),(128,128,32),
              (1024,16,1),(512,32,2),(256,64,4),(128,128,8)] (pw (seq_to_word v))"
  by (simp add: FFTBC.ibc1of256_def pw_coerce pw_mulLayer lay_def)

text \<open>The schedule trees of the hqc-1 conversions (C: bc_1 / ibc_1 on 2048 and 4096 bytes).\<close>

definition T2 :: sch where "T2 = Nd 0 (Lf 1) (Lf 1)"
definition T3 :: sch where "T3 = Nd 1 (Lf 1) T2"
definition T4 :: sch where "T4 = Nd 1 T2 T2"
definition T7 :: sch where "T7 = Nd 2 T3 T4"
definition T8 :: sch where "T8 = Nd 2 T4 T4"
definition T15 :: sch where "T15 = Nd 3 T7 T8"

lemma iradL_num: "iradL M u (numeral n) = map (scale 2) (iradL M u (pred_numeral n)) @ [(1, u * 2 ^ M * 2 ^ pred_numeral n, u * 2 ^ pred_numeral n)]"
  by (simp add: numeral_eq_Suc)

lemma T15_wf: "wf T15" and T15_sz: "sz T15 = 15"
  by (simp_all add: T15_def T7_def T8_def T3_def T4_def T2_def)

lemma T15_layers: "layers T15 1 =
  [(8192,2,1),(2048,8,4),(4096,4,1),(2048,8,2),(512,32,16),(128,128,64),(256,64,16),(128,128,32),
   (1024,16,1),(512,32,2),(256,64,4),(128,128,8)]
  @ [(32,512,256),(8,2048,1024),(16,1024,256),(8,2048,512),(2,8192,4096),(1,16384,4096),(4,4096,256),(2,8192,512),(1,16384,1024)]
  @ [(64,256,1),(32,512,2),(16,1024,4),(8,2048,8),(4,4096,16),(2,8192,32),(1,16384,64)]"
  by (simp add: T15_def T7_def T8_def T3_def T4_def T2_def scale_def iradL_num)

theorem ibc1_32768_iconv:
  fixes v :: "(32768, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc1_32768 v)) = iconv T15 1 (pw (seq_to_word v))"
proof -
  have "pw (seq_to_word (FFTBC.ibc1_32768 v)) = apl (layers T15 1) (pw (seq_to_word v))"
    unfolding T15_layers apl_append
    by (simp add: FFTBC.ibc1_32768_def pw_coerce irepr32768_pw ibc256of32768_pw ibc1of256_128_pw)
  also have "\<dots> = iconv T15 1 (pw (seq_to_word v))"
    by (rule iconv_flat[symmetric, OF T15_wf]) (simp add: T15_sz bnd_pw[of "seq_to_word v", simplified])
  finally show ?thesis .
qed

end
