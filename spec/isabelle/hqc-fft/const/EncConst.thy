theory EncConst
  imports CantorConst HQC.FFTEnc
begin

text \<open>The rows of _enc_mat (FFTEnc.cry, from dencoder.c): row j is the product of beta_(32-t) over the
  set bits t of j, which is X_j(beta_32) in the novel basis. Each product step is a kernel-checked
  gfmulw on word literals (code_simp).\<close>

definition encw :: "64 word list" where
  "encw = [0x0000000000000001, 0xED57CE778F0D6244, 0xB66864E6EC14B4D2, 0x9CEDEBC39773A213,
    0x54E5BF3774B3F850, 0xAA41EC72ACA4D601, 0x4943D209FDC449B8, 0x6E9A7C0E6D89DC84,
    0xEB42E79F91F49F8C, 0x5DC314ADA2848BA2, 0x503CDEDAB981D32C, 0x21D93AB94919CFD3,
    0x4553B41BDA2FBEC8, 0xCB47A62D21DF0B4D, 0x4639691AA527DBBA, 0xE032E7A43C3D150F,
    0xB0F502E4CD60039A, 0xF8287767660AD2B4, 0x1DBF8D7727FC654E, 0x19B12A51DACBA79E,
    0xE691D7C0794C614D, 0x28CF418FAF97A29F, 0x0FC5C2BCA45C931C, 0x4CB433E14292028E,
    0x189B29840C130E7F, 0x315F35290C617710, 0x01F4A9DE7438026B, 0x6AEA5DF783DD08EF,
    0xB36AE8E530273635, 0x837B54AC6006165D, 0x49216693BB420E26, 0xFD50E246BA0FE1A8,
    0x57A3104FCD0E5F34, 0xBFBBCC4E6E818CE9, 0x4FF85CDBB8B5A385, 0xE5836AC7D88636FF,
    0xACAEE33D357E7115, 0xD5591C1E1FCD94AC, 0x5A80DDB4EB880892, 0x557FEEC300CDAAB7,
    0x5A3FD6353EE07E37, 0x5C467F7D2CAF0E9F, 0xEAAC97005F61500B, 0x9554E988C2331D19,
    0x46FC62831B042EEB, 0xE89BD07EBE5CBADC, 0x0E442A47D4AB744E, 0x492FCD9722316B93,
    0xB86431A85814F803, 0xA3C96AFF342C82B8, 0x4716CCF6CBC75A1A, 0x5B71BEA40E882374,
    0x54AC9EE9B21EBE6E, 0x1AAC7F922B29C823, 0x49A5F74A2ECB3E44, 0x4A5A968CC3B566D1,
    0x0641DDCF92A60AA5, 0xEE004D8F989DBA16, 0x1C2242E610C9CD6A, 0x59F1654505010E32,
    0x0D8DF39E76C0E7B7, 0x8CF8E69EB14ECFB4, 0x0CB8C5396572FC44, 0x3B278B84A916E44C]"

lemma encw_lifted: "L FFTEnc.encMat = encw"
  by code_simp

lemma m0: "gfmulw 0xED57CE778F0D6244 0xB66864E6EC14B4D2 = 0x9CEDEBC39773A213"
  by code_simp

lemma m1: "gfmulw 0xED57CE778F0D6244 0x54E5BF3774B3F850 = 0xAA41EC72ACA4D601"
  by code_simp

lemma m2: "gfmulw 0xB66864E6EC14B4D2 0x54E5BF3774B3F850 = 0x4943D209FDC449B8"
  by code_simp

lemma m3: "gfmulw 0x9CEDEBC39773A213 0x54E5BF3774B3F850 = 0x6E9A7C0E6D89DC84"
  by code_simp

lemma m4: "gfmulw 0xED57CE778F0D6244 0xEB42E79F91F49F8C = 0x5DC314ADA2848BA2"
  by code_simp

lemma m5: "gfmulw 0xB66864E6EC14B4D2 0xEB42E79F91F49F8C = 0x503CDEDAB981D32C"
  by code_simp

lemma m6: "gfmulw 0x9CEDEBC39773A213 0xEB42E79F91F49F8C = 0x21D93AB94919CFD3"
  by code_simp

lemma m7: "gfmulw 0x54E5BF3774B3F850 0xEB42E79F91F49F8C = 0x4553B41BDA2FBEC8"
  by code_simp

lemma m8: "gfmulw 0xAA41EC72ACA4D601 0xEB42E79F91F49F8C = 0xCB47A62D21DF0B4D"
  by code_simp

lemma m9: "gfmulw 0x4943D209FDC449B8 0xEB42E79F91F49F8C = 0x4639691AA527DBBA"
  by code_simp

lemma m10: "gfmulw 0x6E9A7C0E6D89DC84 0xEB42E79F91F49F8C = 0xE032E7A43C3D150F"
  by code_simp

lemma m11: "gfmulw 0xED57CE778F0D6244 0xB0F502E4CD60039A = 0xF8287767660AD2B4"
  by code_simp

lemma m12: "gfmulw 0xB66864E6EC14B4D2 0xB0F502E4CD60039A = 0x1DBF8D7727FC654E"
  by code_simp

lemma m13: "gfmulw 0x9CEDEBC39773A213 0xB0F502E4CD60039A = 0x19B12A51DACBA79E"
  by code_simp

lemma m14: "gfmulw 0x54E5BF3774B3F850 0xB0F502E4CD60039A = 0xE691D7C0794C614D"
  by code_simp

lemma m15: "gfmulw 0xAA41EC72ACA4D601 0xB0F502E4CD60039A = 0x28CF418FAF97A29F"
  by code_simp

lemma m16: "gfmulw 0x4943D209FDC449B8 0xB0F502E4CD60039A = 0x0FC5C2BCA45C931C"
  by code_simp

lemma m17: "gfmulw 0x6E9A7C0E6D89DC84 0xB0F502E4CD60039A = 0x4CB433E14292028E"
  by code_simp

lemma m18: "gfmulw 0xEB42E79F91F49F8C 0xB0F502E4CD60039A = 0x189B29840C130E7F"
  by code_simp

lemma m19: "gfmulw 0x5DC314ADA2848BA2 0xB0F502E4CD60039A = 0x315F35290C617710"
  by code_simp

lemma m20: "gfmulw 0x503CDEDAB981D32C 0xB0F502E4CD60039A = 0x01F4A9DE7438026B"
  by code_simp

lemma m21: "gfmulw 0x21D93AB94919CFD3 0xB0F502E4CD60039A = 0x6AEA5DF783DD08EF"
  by code_simp

lemma m22: "gfmulw 0x4553B41BDA2FBEC8 0xB0F502E4CD60039A = 0xB36AE8E530273635"
  by code_simp

lemma m23: "gfmulw 0xCB47A62D21DF0B4D 0xB0F502E4CD60039A = 0x837B54AC6006165D"
  by code_simp

lemma m24: "gfmulw 0x4639691AA527DBBA 0xB0F502E4CD60039A = 0x49216693BB420E26"
  by code_simp

lemma m25: "gfmulw 0xE032E7A43C3D150F 0xB0F502E4CD60039A = 0xFD50E246BA0FE1A8"
  by code_simp

lemma m26: "gfmulw 0xED57CE778F0D6244 0x57A3104FCD0E5F34 = 0xBFBBCC4E6E818CE9"
  by code_simp

lemma m27: "gfmulw 0xB66864E6EC14B4D2 0x57A3104FCD0E5F34 = 0x4FF85CDBB8B5A385"
  by code_simp

lemma m28: "gfmulw 0x9CEDEBC39773A213 0x57A3104FCD0E5F34 = 0xE5836AC7D88636FF"
  by code_simp

lemma m29: "gfmulw 0x54E5BF3774B3F850 0x57A3104FCD0E5F34 = 0xACAEE33D357E7115"
  by code_simp

lemma m30: "gfmulw 0xAA41EC72ACA4D601 0x57A3104FCD0E5F34 = 0xD5591C1E1FCD94AC"
  by code_simp

lemma m31: "gfmulw 0x4943D209FDC449B8 0x57A3104FCD0E5F34 = 0x5A80DDB4EB880892"
  by code_simp

lemma m32: "gfmulw 0x6E9A7C0E6D89DC84 0x57A3104FCD0E5F34 = 0x557FEEC300CDAAB7"
  by code_simp

lemma m33: "gfmulw 0xEB42E79F91F49F8C 0x57A3104FCD0E5F34 = 0x5A3FD6353EE07E37"
  by code_simp

lemma m34: "gfmulw 0x5DC314ADA2848BA2 0x57A3104FCD0E5F34 = 0x5C467F7D2CAF0E9F"
  by code_simp

lemma m35: "gfmulw 0x503CDEDAB981D32C 0x57A3104FCD0E5F34 = 0xEAAC97005F61500B"
  by code_simp

lemma m36: "gfmulw 0x21D93AB94919CFD3 0x57A3104FCD0E5F34 = 0x9554E988C2331D19"
  by code_simp

lemma m37: "gfmulw 0x4553B41BDA2FBEC8 0x57A3104FCD0E5F34 = 0x46FC62831B042EEB"
  by code_simp

lemma m38: "gfmulw 0xCB47A62D21DF0B4D 0x57A3104FCD0E5F34 = 0xE89BD07EBE5CBADC"
  by code_simp

lemma m39: "gfmulw 0x4639691AA527DBBA 0x57A3104FCD0E5F34 = 0x0E442A47D4AB744E"
  by code_simp

lemma m40: "gfmulw 0xE032E7A43C3D150F 0x57A3104FCD0E5F34 = 0x492FCD9722316B93"
  by code_simp

lemma m41: "gfmulw 0xB0F502E4CD60039A 0x57A3104FCD0E5F34 = 0xB86431A85814F803"
  by code_simp

lemma m42: "gfmulw 0xF8287767660AD2B4 0x57A3104FCD0E5F34 = 0xA3C96AFF342C82B8"
  by code_simp

lemma m43: "gfmulw 0x1DBF8D7727FC654E 0x57A3104FCD0E5F34 = 0x4716CCF6CBC75A1A"
  by code_simp

lemma m44: "gfmulw 0x19B12A51DACBA79E 0x57A3104FCD0E5F34 = 0x5B71BEA40E882374"
  by code_simp

lemma m45: "gfmulw 0xE691D7C0794C614D 0x57A3104FCD0E5F34 = 0x54AC9EE9B21EBE6E"
  by code_simp

lemma m46: "gfmulw 0x28CF418FAF97A29F 0x57A3104FCD0E5F34 = 0x1AAC7F922B29C823"
  by code_simp

lemma m47: "gfmulw 0x0FC5C2BCA45C931C 0x57A3104FCD0E5F34 = 0x49A5F74A2ECB3E44"
  by code_simp

lemma m48: "gfmulw 0x4CB433E14292028E 0x57A3104FCD0E5F34 = 0x4A5A968CC3B566D1"
  by code_simp

lemma m49: "gfmulw 0x189B29840C130E7F 0x57A3104FCD0E5F34 = 0x0641DDCF92A60AA5"
  by code_simp

lemma m50: "gfmulw 0x315F35290C617710 0x57A3104FCD0E5F34 = 0xEE004D8F989DBA16"
  by code_simp

lemma m51: "gfmulw 0x01F4A9DE7438026B 0x57A3104FCD0E5F34 = 0x1C2242E610C9CD6A"
  by code_simp

lemma m52: "gfmulw 0x6AEA5DF783DD08EF 0x57A3104FCD0E5F34 = 0x59F1654505010E32"
  by code_simp

lemma m53: "gfmulw 0xB36AE8E530273635 0x57A3104FCD0E5F34 = 0x0D8DF39E76C0E7B7"
  by code_simp

lemma m54: "gfmulw 0x837B54AC6006165D 0x57A3104FCD0E5F34 = 0x8CF8E69EB14ECFB4"
  by code_simp

lemma m55: "gfmulw 0x49216693BB420E26 0x57A3104FCD0E5F34 = 0x0CB8C5396572FC44"
  by code_simp

lemma m56: "gfmulw 0xFD50E246BA0FE1A8 0x57A3104FCD0E5F34 = 0x3B278B84A916E44C"
  by code_simp

text \<open>The rows as field elements.\<close>

lemma beta_lit: "beta j = gfw (cbw ! j)" by (simp add: beta_def)

lemma enc_row_0: "gfw (encw ! 0) = 1"
  by (simp add: encw_def gfw_one)

lemma enc_row_1: "gfw (encw ! 1) = beta 32"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric]  mult.assoc)

lemma enc_row_2: "gfw (encw ! 2) = beta 31"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric]  mult.assoc)

lemma enc_row_3: "gfw (encw ! 3) = beta 32 * beta 31"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 mult.assoc)

lemma enc_row_4: "gfw (encw ! 4) = beta 30"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric]  mult.assoc)

lemma enc_row_5: "gfw (encw ! 5) = beta 32 * beta 30"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 mult.assoc)

lemma enc_row_6: "gfw (encw ! 6) = beta 31 * beta 30"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 mult.assoc)

lemma enc_row_7: "gfw (encw ! 7) = beta 32 * beta 31 * beta 30"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 mult.assoc)

lemma enc_row_8: "gfw (encw ! 8) = beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric]  mult.assoc)

lemma enc_row_9: "gfw (encw ! 9) = beta 32 * beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m4 mult.assoc)

lemma enc_row_10: "gfw (encw ! 10) = beta 31 * beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m5 mult.assoc)

lemma enc_row_11: "gfw (encw ! 11) = beta 32 * beta 31 * beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m6 mult.assoc)

lemma enc_row_12: "gfw (encw ! 12) = beta 30 * beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m7 mult.assoc)

lemma enc_row_13: "gfw (encw ! 13) = beta 32 * beta 30 * beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 m8 mult.assoc)

lemma enc_row_14: "gfw (encw ! 14) = beta 31 * beta 30 * beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 m9 mult.assoc)

lemma enc_row_15: "gfw (encw ! 15) = beta 32 * beta 31 * beta 30 * beta 29"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 m10 mult.assoc)

lemma enc_row_16: "gfw (encw ! 16) = beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric]  mult.assoc)

lemma enc_row_17: "gfw (encw ! 17) = beta 32 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m11 mult.assoc)

lemma enc_row_18: "gfw (encw ! 18) = beta 31 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m12 mult.assoc)

lemma enc_row_19: "gfw (encw ! 19) = beta 32 * beta 31 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m13 mult.assoc)

lemma enc_row_20: "gfw (encw ! 20) = beta 30 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m14 mult.assoc)

lemma enc_row_21: "gfw (encw ! 21) = beta 32 * beta 30 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 m15 mult.assoc)

lemma enc_row_22: "gfw (encw ! 22) = beta 31 * beta 30 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 m16 mult.assoc)

lemma enc_row_23: "gfw (encw ! 23) = beta 32 * beta 31 * beta 30 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 m17 mult.assoc)

lemma enc_row_24: "gfw (encw ! 24) = beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m18 mult.assoc)

lemma enc_row_25: "gfw (encw ! 25) = beta 32 * beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m4 m19 mult.assoc)

lemma enc_row_26: "gfw (encw ! 26) = beta 31 * beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m5 m20 mult.assoc)

lemma enc_row_27: "gfw (encw ! 27) = beta 32 * beta 31 * beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m6 m21 mult.assoc)

lemma enc_row_28: "gfw (encw ! 28) = beta 30 * beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m7 m22 mult.assoc)

lemma enc_row_29: "gfw (encw ! 29) = beta 32 * beta 30 * beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 m8 m23 mult.assoc)

lemma enc_row_30: "gfw (encw ! 30) = beta 31 * beta 30 * beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 m9 m24 mult.assoc)

lemma enc_row_31: "gfw (encw ! 31) = beta 32 * beta 31 * beta 30 * beta 29 * beta 28"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 m10 m25 mult.assoc)

lemma enc_row_32: "gfw (encw ! 32) = beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric]  mult.assoc)

lemma enc_row_33: "gfw (encw ! 33) = beta 32 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m26 mult.assoc)

lemma enc_row_34: "gfw (encw ! 34) = beta 31 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m27 mult.assoc)

lemma enc_row_35: "gfw (encw ! 35) = beta 32 * beta 31 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m28 mult.assoc)

lemma enc_row_36: "gfw (encw ! 36) = beta 30 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m29 mult.assoc)

lemma enc_row_37: "gfw (encw ! 37) = beta 32 * beta 30 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 m30 mult.assoc)

lemma enc_row_38: "gfw (encw ! 38) = beta 31 * beta 30 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 m31 mult.assoc)

lemma enc_row_39: "gfw (encw ! 39) = beta 32 * beta 31 * beta 30 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 m32 mult.assoc)

lemma enc_row_40: "gfw (encw ! 40) = beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m33 mult.assoc)

lemma enc_row_41: "gfw (encw ! 41) = beta 32 * beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m4 m34 mult.assoc)

lemma enc_row_42: "gfw (encw ! 42) = beta 31 * beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m5 m35 mult.assoc)

lemma enc_row_43: "gfw (encw ! 43) = beta 32 * beta 31 * beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m6 m36 mult.assoc)

lemma enc_row_44: "gfw (encw ! 44) = beta 30 * beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m7 m37 mult.assoc)

lemma enc_row_45: "gfw (encw ! 45) = beta 32 * beta 30 * beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 m8 m38 mult.assoc)

lemma enc_row_46: "gfw (encw ! 46) = beta 31 * beta 30 * beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 m9 m39 mult.assoc)

lemma enc_row_47: "gfw (encw ! 47) = beta 32 * beta 31 * beta 30 * beta 29 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 m10 m40 mult.assoc)

lemma enc_row_48: "gfw (encw ! 48) = beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m41 mult.assoc)

lemma enc_row_49: "gfw (encw ! 49) = beta 32 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m11 m42 mult.assoc)

lemma enc_row_50: "gfw (encw ! 50) = beta 31 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m12 m43 mult.assoc)

lemma enc_row_51: "gfw (encw ! 51) = beta 32 * beta 31 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m13 m44 mult.assoc)

lemma enc_row_52: "gfw (encw ! 52) = beta 30 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m14 m45 mult.assoc)

lemma enc_row_53: "gfw (encw ! 53) = beta 32 * beta 30 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 m15 m46 mult.assoc)

lemma enc_row_54: "gfw (encw ! 54) = beta 31 * beta 30 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 m16 m47 mult.assoc)

lemma enc_row_55: "gfw (encw ! 55) = beta 32 * beta 31 * beta 30 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 m17 m48 mult.assoc)

lemma enc_row_56: "gfw (encw ! 56) = beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m18 m49 mult.assoc)

lemma enc_row_57: "gfw (encw ! 57) = beta 32 * beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m4 m19 m50 mult.assoc)

lemma enc_row_58: "gfw (encw ! 58) = beta 31 * beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m5 m20 m51 mult.assoc)

lemma enc_row_59: "gfw (encw ! 59) = beta 32 * beta 31 * beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m6 m21 m52 mult.assoc)

lemma enc_row_60: "gfw (encw ! 60) = beta 30 * beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m7 m22 m53 mult.assoc)

lemma enc_row_61: "gfw (encw ! 61) = beta 32 * beta 30 * beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m1 m8 m23 m54 mult.assoc)

lemma enc_row_62: "gfw (encw ! 62) = beta 31 * beta 30 * beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m2 m9 m24 m55 mult.assoc)

lemma enc_row_63: "gfw (encw ! 63) = beta 32 * beta 31 * beta 30 * beta 29 * beta 28 * beta 27"
  by (simp add: encw_def beta_def cbw_def gfmulw_gf[symmetric] m0 m3 m10 m25 m56 mult.assoc)

end
