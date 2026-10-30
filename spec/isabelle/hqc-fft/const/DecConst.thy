theory DecConst
  imports EncConst
begin

text \<open>_dec_mat (FFTEnc.cry, from dencoder.c) inverts _enc_mat: applied to row j of _enc_mat it gives
  the unit vector 2^j. Kernel-checked by code_simp.\<close>

definition decw :: "64 word list" where
  "decw = [0x0000000000000001, 0x08961B8A7841BFC6, 0xFD56DC6306E45EC6, 0x77332469D0404105,
    0xD110EB4A970FEAF5, 0x9C94931DE38226FE, 0x52BF8C5BA0978896, 0xBCE2B823BEBF0166,
    0x7AF3356B5D818E41, 0x1E7B94C935B698D0, 0xBCB73D9AABDD6DDF, 0x5F75970481F366A8,
    0xB33F7074D9B6E3FE, 0x2ADB64D29A93EF96, 0x59DAB92A69394E60, 0x3C8004790328459C,
    0xADCB0001CDAA3D05, 0x9BB38FD76D5E0C0B, 0xABCADD426CB54B4D, 0xF042A8F93E8A48B9,
    0x47B25AAB146986F6, 0xE750955BE42931A1, 0x9BF1D4A1535A0D17, 0x91564F9A406D933C,
    0xDED3254B42D33AAA, 0xBD1F32C59E84E45D, 0xFA018660E3165396, 0xA2F911A00F5BAA7B,
    0xE958695BC8926ACD, 0xC8C10606A8EC8D6B, 0x8E6CFEF54B2E9AC6, 0x88007D210E507CF4,
    0x17A89B9796A48397, 0x1BDD636A99F218BE, 0x7CB821D83481A449, 0xFF39584957728D46,
    0x9CD7C0F7B4D02DE7, 0x779FCA946B676EDB, 0x5235A7728B715838, 0x70EF0482C08984A5,
    0xBB1C3DBFE2B5150B, 0xEE767356051FE0E1, 0x1B5C98D75CC93FE8, 0x4C25EE1FB1C8CEB6,
    0xB7310079067F9E51, 0x4BE2A5AE359E2594, 0x0FE86864026631C3, 0x5B4CD59958434683,
    0xE550B2539A848707, 0x6E50D13B6A7A5997, 0x7FD8FB00A5AEF99A, 0xCDBD262AC16E806B,
    0xC021427B4F7646E0, 0xD7F262605A9BCDD0, 0x0B046630A7EFEDDC, 0xA869F3DFCBE24FAB,
    0xA00150323BE9B1DE, 0x01294D8724AE3D0D, 0x4AB517F07F03A4B1, 0xFDC5AF3BB370E266,
    0x2AFF63EFA8285238, 0xFBA0ACE42227357A, 0xC208107E1C3E5AC1, 0xB2DBB5CB68D0DC74]"

lemma decw_lifted: "L FFTEnc.decMat = decw"
  by code_simp

definition linw :: "64 word list \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "linw mat v = foldl (XOR) 0 (map (\<lambda>j. if bit v j then mat ! j else 0) [0..<64])"

lemma dec_enc_0: "linw decw (encw ! 0) = 2 ^ 0"
  by code_simp

lemma dec_enc_1: "linw decw (encw ! 1) = 2 ^ 1"
  by code_simp

lemma dec_enc_2: "linw decw (encw ! 2) = 2 ^ 2"
  by code_simp

lemma dec_enc_3: "linw decw (encw ! 3) = 2 ^ 3"
  by code_simp

lemma dec_enc_4: "linw decw (encw ! 4) = 2 ^ 4"
  by code_simp

lemma dec_enc_5: "linw decw (encw ! 5) = 2 ^ 5"
  by code_simp

lemma dec_enc_6: "linw decw (encw ! 6) = 2 ^ 6"
  by code_simp

lemma dec_enc_7: "linw decw (encw ! 7) = 2 ^ 7"
  by code_simp

lemma dec_enc_8: "linw decw (encw ! 8) = 2 ^ 8"
  by code_simp

lemma dec_enc_9: "linw decw (encw ! 9) = 2 ^ 9"
  by code_simp

lemma dec_enc_10: "linw decw (encw ! 10) = 2 ^ 10"
  by code_simp

lemma dec_enc_11: "linw decw (encw ! 11) = 2 ^ 11"
  by code_simp

lemma dec_enc_12: "linw decw (encw ! 12) = 2 ^ 12"
  by code_simp

lemma dec_enc_13: "linw decw (encw ! 13) = 2 ^ 13"
  by code_simp

lemma dec_enc_14: "linw decw (encw ! 14) = 2 ^ 14"
  by code_simp

lemma dec_enc_15: "linw decw (encw ! 15) = 2 ^ 15"
  by code_simp

lemma dec_enc_16: "linw decw (encw ! 16) = 2 ^ 16"
  by code_simp

lemma dec_enc_17: "linw decw (encw ! 17) = 2 ^ 17"
  by code_simp

lemma dec_enc_18: "linw decw (encw ! 18) = 2 ^ 18"
  by code_simp

lemma dec_enc_19: "linw decw (encw ! 19) = 2 ^ 19"
  by code_simp

lemma dec_enc_20: "linw decw (encw ! 20) = 2 ^ 20"
  by code_simp

lemma dec_enc_21: "linw decw (encw ! 21) = 2 ^ 21"
  by code_simp

lemma dec_enc_22: "linw decw (encw ! 22) = 2 ^ 22"
  by code_simp

lemma dec_enc_23: "linw decw (encw ! 23) = 2 ^ 23"
  by code_simp

lemma dec_enc_24: "linw decw (encw ! 24) = 2 ^ 24"
  by code_simp

lemma dec_enc_25: "linw decw (encw ! 25) = 2 ^ 25"
  by code_simp

lemma dec_enc_26: "linw decw (encw ! 26) = 2 ^ 26"
  by code_simp

lemma dec_enc_27: "linw decw (encw ! 27) = 2 ^ 27"
  by code_simp

lemma dec_enc_28: "linw decw (encw ! 28) = 2 ^ 28"
  by code_simp

lemma dec_enc_29: "linw decw (encw ! 29) = 2 ^ 29"
  by code_simp

lemma dec_enc_30: "linw decw (encw ! 30) = 2 ^ 30"
  by code_simp

lemma dec_enc_31: "linw decw (encw ! 31) = 2 ^ 31"
  by code_simp

lemma dec_enc_32: "linw decw (encw ! 32) = 2 ^ 32"
  by code_simp

lemma dec_enc_33: "linw decw (encw ! 33) = 2 ^ 33"
  by code_simp

lemma dec_enc_34: "linw decw (encw ! 34) = 2 ^ 34"
  by code_simp

lemma dec_enc_35: "linw decw (encw ! 35) = 2 ^ 35"
  by code_simp

lemma dec_enc_36: "linw decw (encw ! 36) = 2 ^ 36"
  by code_simp

lemma dec_enc_37: "linw decw (encw ! 37) = 2 ^ 37"
  by code_simp

lemma dec_enc_38: "linw decw (encw ! 38) = 2 ^ 38"
  by code_simp

lemma dec_enc_39: "linw decw (encw ! 39) = 2 ^ 39"
  by code_simp

lemma dec_enc_40: "linw decw (encw ! 40) = 2 ^ 40"
  by code_simp

lemma dec_enc_41: "linw decw (encw ! 41) = 2 ^ 41"
  by code_simp

lemma dec_enc_42: "linw decw (encw ! 42) = 2 ^ 42"
  by code_simp

lemma dec_enc_43: "linw decw (encw ! 43) = 2 ^ 43"
  by code_simp

lemma dec_enc_44: "linw decw (encw ! 44) = 2 ^ 44"
  by code_simp

lemma dec_enc_45: "linw decw (encw ! 45) = 2 ^ 45"
  by code_simp

lemma dec_enc_46: "linw decw (encw ! 46) = 2 ^ 46"
  by code_simp

lemma dec_enc_47: "linw decw (encw ! 47) = 2 ^ 47"
  by code_simp

lemma dec_enc_48: "linw decw (encw ! 48) = 2 ^ 48"
  by code_simp

lemma dec_enc_49: "linw decw (encw ! 49) = 2 ^ 49"
  by code_simp

lemma dec_enc_50: "linw decw (encw ! 50) = 2 ^ 50"
  by code_simp

lemma dec_enc_51: "linw decw (encw ! 51) = 2 ^ 51"
  by code_simp

lemma dec_enc_52: "linw decw (encw ! 52) = 2 ^ 52"
  by code_simp

lemma dec_enc_53: "linw decw (encw ! 53) = 2 ^ 53"
  by code_simp

lemma dec_enc_54: "linw decw (encw ! 54) = 2 ^ 54"
  by code_simp

lemma dec_enc_55: "linw decw (encw ! 55) = 2 ^ 55"
  by code_simp

lemma dec_enc_56: "linw decw (encw ! 56) = 2 ^ 56"
  by code_simp

lemma dec_enc_57: "linw decw (encw ! 57) = 2 ^ 57"
  by code_simp

lemma dec_enc_58: "linw decw (encw ! 58) = 2 ^ 58"
  by code_simp

lemma dec_enc_59: "linw decw (encw ! 59) = 2 ^ 59"
  by code_simp

lemma dec_enc_60: "linw decw (encw ! 60) = 2 ^ 60"
  by code_simp

lemma dec_enc_61: "linw decw (encw ! 61) = 2 ^ 61"
  by code_simp

lemma dec_enc_62: "linw decw (encw ! 62) = 2 ^ 62"
  by code_simp

lemma dec_enc_63: "linw decw (encw ! 63) = 2 ^ 63"
  by code_simp

end
