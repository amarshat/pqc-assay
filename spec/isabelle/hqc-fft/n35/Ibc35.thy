theory Ibc35
  imports Commute "HQC_FFT.DivBridge"
begin

text \<open>The basis conversions at the hqc-3 and hqc-5 sizes. ibc_1 on 8192 bytes (the hqc-3 product)
  is the schedule tree T16; ibc_1 on 16384 bytes (the hqc-5 product, the C's generic path) runs the
  layers of T17 with the hi subtree first at the cvt nodes, which layersR_layers and swap_node show
  has the same effect. bc_1 at 65536 and 131072 bits is undone by ibc_1 layer by layer.\<close>

theorem ibc_bc_65536:
  fixes v :: "(65536, bool) seq"
  shows "FFTBC.ibc1_65536 (FFTBC.bc1_65536 v) = v"
  by (simp add: FFTBC.ibc1_65536_def FFTBC.bc1_65536_def FFTBC.irepr65536_def FFTBC.repr65536_def
      FFTBC.ibc256of65536_def FFTBC.bc256of65536_def FFTBC.ibc1of256_def FFTBC.bc1of256_def mulLayer_divLayer)

theorem ibc_bc_131072:
  fixes v :: "(131072, bool) seq"
  shows "FFTBC.ibc1_131072 (FFTBC.bc1_131072 v) = v"
  by (simp add: FFTBC.ibc1_131072_def FFTBC.bc1_131072_def FFTBC.irepr131072_def FFTBC.repr131072_def
      FFTBC.icvt131072_def FFTBC.cvt131072_def FFTBC.ibc1of256_def FFTBC.bc1of256_def mulLayer_divLayer)

subsection \<open>hqc-3: 65536 bits\<close>

lemma irepr65536_pw:
  fixes v :: "(65536, bool) seq"
  shows "pw (seq_to_word (FFTBC.irepr65536 v))
       = apl [(128,256,1),(64,512,2),(32,1024,4),(16,2048,8),(8,4096,16),(4,8192,32),(2,16384,64),(1,32768,128)] (pw (seq_to_word v))"
  by (simp add: FFTBC.irepr65536_def pw_coerce pw_mulLayer lay_def)

lemma ibc256of65536_pw:
  fixes v :: "(65536, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc256of65536 v))
       = apl [(64,512,256),(16,2048,1024),(32,1024,256),(16,2048,512),(4,8192,4096),(1,32768,16384),(2,16384,4096),(1,32768,8192),
              (8,4096,256),(4,8192,512),(2,16384,1024),(1,32768,2048)] (pw (seq_to_word v))"
  by (simp add: FFTBC.ibc256of65536_def pw_coerce pw_mulLayer lay_def)

lemma ibc1of256_256_pw:
  fixes v :: "(256 \<times> 256, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc1of256 TY(256) v))
       = apl [(16384,2,1),(4096,8,4),(8192,4,1),(4096,8,2),(1024,32,16),(256,128,64),(512,64,16),(256,128,32),
              (2048,16,1),(1024,32,2),(512,64,4),(256,128,8)] (pw (seq_to_word v))"
  by (simp add: FFTBC.ibc1of256_def pw_coerce pw_mulLayer lay_def)

definition T16 :: sch where "T16 = Nd 3 T8 T8"

lemma T16_wf: "wf T16" and T16_sz: "sz T16 = 16"
  by (simp_all add: T16_def T8_def T4_def T2_def)

lemma T16_layers: "layers T16 1 =
  [(16384,2,1),(4096,8,4),(8192,4,1),(4096,8,2),(1024,32,16),(256,128,64),(512,64,16),(256,128,32),
   (2048,16,1),(1024,32,2),(512,64,4),(256,128,8)]
  @ [(64,512,256),(16,2048,1024),(32,1024,256),(16,2048,512),(4,8192,4096),(1,32768,16384),(2,16384,4096),(1,32768,8192),
     (8,4096,256),(4,8192,512),(2,16384,1024),(1,32768,2048)]
  @ [(128,256,1),(64,512,2),(32,1024,4),(16,2048,8),(8,4096,16),(4,8192,32),(2,16384,64),(1,32768,128)]"
  by (simp add: T16_def T8_def T4_def T2_def scale_def iradL_num)

theorem ibc1_65536_iconv:
  fixes v :: "(65536, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc1_65536 v)) = iconv T16 1 (pw (seq_to_word v))"
proof -
  have "pw (seq_to_word (FFTBC.ibc1_65536 v)) = apl (layers T16 1) (pw (seq_to_word v))"
    unfolding T16_layers apl_append
    by (simp add: FFTBC.ibc1_65536_def pw_coerce irepr65536_pw ibc256of65536_pw ibc1of256_256_pw)
  also have "\<dots> = iconv T16 1 (pw (seq_to_word v))"
    by (rule iconv_flat[symmetric, OF T16_wf]) (simp add: T16_sz bnd_pw[of "seq_to_word v", simplified])
  finally show ?thesis .
qed

subsection \<open>hqc-5: 131072 bits\<close>

lemma irepr131072_pw:
  fixes v :: "(131072, bool) seq"
  shows "pw (seq_to_word (FFTBC.irepr131072 v))
       = apl [(256,256,1),(128,512,2),(64,1024,4),(32,2048,8),(16,4096,16),(8,8192,32),(4,16384,64),(2,32768,128),(1,65536,256)]
             (pw (seq_to_word v))"
  by (simp add: FFTBC.irepr131072_def pw_coerce pw_mulLayer lay_def)

lemma icvt131072_pw:
  fixes v :: "(131072, bool) seq"
  shows "pw (seq_to_word (FFTBC.icvt131072 v))
       = apl [(2,32768,16384),(8,8192,4096),(4,16384,4096),(2,32768,8192),(32,2048,1024),(128,512,256),(64,1024,256),
              (32,2048,512),(16,4096,256),(8,8192,512),(4,16384,1024),(2,32768,2048),(1,65536,256)] (pw (seq_to_word v))"
  by (simp add: FFTBC.icvt131072_def pw_coerce pw_mulLayer lay_def)

lemma ibc1of256_512_pw:
  fixes v :: "(256 \<times> 512, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc1of256 TY(512) v))
       = apl [(32768,2,1),(8192,8,4),(16384,4,1),(8192,8,2),(2048,32,16),(512,128,64),(1024,64,16),(512,128,32),
              (4096,16,1),(2048,32,2),(1024,64,4),(512,128,8)] (pw (seq_to_word v))"
  by (simp add: FFTBC.ibc1of256_def pw_coerce pw_mulLayer lay_def)

definition T9 :: sch where "T9 = Nd 3 (Lf 1) T8"
definition T17 :: sch where "T17 = Nd 3 T9 T8"

lemma T9_wf: "wf T9" and T9_sz: "sz T9 = 9" and T17_wf: "wf T17" and T17_sz: "sz T17 = 17"
  by (simp_all add: T17_def T9_def T8_def T4_def T2_def)

lemma C131072_layers:
  "[(2,32768,16384),(8,8192,4096),(4,16384,4096),(2,32768,8192),(32,2048,1024),(128,512,256),(64,1024,256),
    (32,2048,512),(16,4096,256),(8,8192,512),(4,16384,1024),(2,32768,2048),(1,65536,256)]
   @ [(32768,2,1),(8192,8,4),(16384,4,1),(8192,8,2),(2048,32,16),(512,128,64),(1024,64,16),(512,128,32),
      (4096,16,1),(2048,32,2),(1024,64,4),(512,128,8)]
   @ [(256,256,1),(128,512,2),(64,1024,4),(32,2048,8),(16,4096,16),(8,8192,32),(4,16384,64),(2,32768,128),(1,65536,256)]
   = layersR T9 256 @ map (scale 512) (layers T8 1) @ iradL 8 1 9"
  by (simp add: T9_def T8_def T4_def T2_def scale_def iradL_num)

lemma T17_order:
  fixes f :: "'a :: char2 poly"
  assumes f: "bnd 131072 f"
  shows "apl (layersR T9 256 @ map (scale 512) (layers T8 1) @ iradL 8 1 9) f = apl (layers T17 1) f"
proof -
  have r: "apl (layersR T9 256) f = apl (layers T9 256) f"
    by (rule layersR_layers[OF T9_wf]) (use f in \<open>simp_all add: T9_sz\<close>)
  have s: "apl (layers T9 (1 * 2 ^ 2 ^ 3) @ map (scale (2 ^ sz T9)) (layers T8 1)) f
         = apl (map (scale (2 ^ sz T9)) (layers T8 1) @ layers T9 (1 * 2 ^ 2 ^ 3)) f"
    by (rule swap_node[of 3 T9 T8 1, folded T17_def, OF T17_wf]) (use f in \<open>simp_all add: T17_sz\<close>)
  have "apl (layersR T9 256 @ map (scale 512) (layers T8 1) @ iradL 8 1 9) f
      = apl (iradL 8 1 9) (apl (layers T9 256 @ map (scale 512) (layers T8 1)) f)"
    by (simp add: apl_append r)
  also have "\<dots> = apl (iradL 8 1 9) (apl (map (scale 512) (layers T8 1) @ layers T9 256) f)"
    using s by (simp add: T9_sz)
  also have "\<dots> = apl (layers T17 1) f"
    by (simp add: T17_def T9_sz apl_append)
  finally show ?thesis .
qed

theorem ibc1_131072_iconv:
  fixes v :: "(131072, bool) seq"
  shows "pw (seq_to_word (FFTBC.ibc1_131072 v)) = iconv T17 1 (pw (seq_to_word v))"
proof -
  have b: "bnd 131072 (pw (seq_to_word v))" using bnd_pw[of "seq_to_word v"] by simp
  have "pw (seq_to_word (FFTBC.ibc1_131072 v)) = apl (layersR T9 256 @ map (scale 512) (layers T8 1) @ iradL 8 1 9) (pw (seq_to_word v))"
    unfolding C131072_layers[symmetric] apl_append
    by (simp add: FFTBC.ibc1_131072_def pw_coerce irepr131072_pw icvt131072_pw ibc1of256_512_pw)
  also have "\<dots> = apl (layers T17 1) (pw (seq_to_word v))" by (rule T17_order[OF b])
  also have "\<dots> = iconv T17 1 (pw (seq_to_word v))"
    by (rule iconv_flat[symmetric, OF T17_wf]) (simp add: T17_sz b)
  finally show ?thesis .
qed

end
