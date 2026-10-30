theory CantorConst
  imports GFMul "HQC_FFT_Math.Encode"
begin

text \<open>The 64 constants of cantorBasis (FFTRef.cry, from cantor_to_gf264.c) form a Cantor basis of
  GF(2^64): beta_0 = 1 and beta_(j+1)^2 + beta_(j+1) = beta_j. Checked in the kernel by code_simp
  on the executable product gfmulw.\<close>

definition cbw :: "64 word list" where
  "cbw = [0x0000000000000001, 0x19C9369F278ADC02, 0xA181E7D66F5FF794, 0x5DB84357CE785D08,
    0xB973D466F5C9D0CA, 0x521AC889831A075E, 0x033CE8BEDDC8A656, 0xB5846C4E07B91010,
    0x4087B8CBB37A32EC, 0x00D0D3888C0AE17C, 0xAFD5AC70237F2222, 0xE3F5AF99CC3AAAF8,
    0x5A1DB3B16A0B58B8, 0x09947C54FE7EE248, 0x0E8EAF0E0068F544, 0xA2A113500B4B4F5A,
    0xE96F9805D6CE0BB0, 0x53496F8B5C9EDD4C, 0xAD325CB6F4AC2A9E, 0x4A8DCF8BD7EDE826,
    0xA3E9C552B6434210, 0x5FA92AD9C9BC7ED0, 0xA389F910CD7734DE, 0xE916F3DFCA4609D8,
    0xF89578714BD28F96, 0x564DDA59237A3352, 0xAD33BC6CC75AED38, 0x57A3104FCD0E5F34,
    0xB0F502E4CD60039A, 0xEB42E79F91F49F8C, 0x54E5BF3774B3F850, 0xB66864E6EC14B4D2,
    0xED57CE778F0D6244, 0x523AAF9D6148BA24, 0xA8FCBFAAC14940C6, 0xE503EACFCEF77780,
    0xF3746C7B5183A372, 0xEC50D77D2F416218, 0xF9CDF54569FE87E6, 0xE576269915705E2C,
    0xEE2A197148FA8C72, 0x49E31453575F365A, 0xB86698D88ADD0BC0, 0x4F35FB218E7F37C0,
    0xA306FEEA8A242832, 0x5E5F06A9DAEAD6E6, 0xBE13089ECC784EA0, 0xFE1A10738739C892,
    0xE2266CEB0C5BC774, 0xF490E6ED40D1DD1A, 0xF3F5F515077E92F0, 0x467C20312E7EB0F0,
    0xB06CAA4295D350C2, 0x5C5916D98A583C16, 0xA04DE5B4C7A1CEAC, 0x41430183D6E85EC0,
    0xB361D8DABE3B3632, 0x4357375D88B88B56, 0xB057DCC8A19FBC9C, 0xF26E1791BE4B37C2,
    0xE9F744031BFE63E4, 0xE50803875E9AB776, 0x44EE098F4D56753E, 0x9DC338F8399031B4]"

lemma length_cbw [simp]: "length cbw = 64"
  by (simp add: cbw_def)

lemma cbw_lifted: "L cantorBasis = cbw"
  by code_simp

definition relok :: "nat \<Rightarrow> bool" where
  "relok j \<longleftrightarrow> gfmulw (cbw ! Suc j) (cbw ! Suc j) XOR (cbw ! Suc j) = cbw ! j"

lemma cbw_rel_0: "relok 0"
  unfolding relok_def by code_simp

lemma cbw_rel_1: "relok 1"
  unfolding relok_def by code_simp

lemma cbw_rel_2: "relok 2"
  unfolding relok_def by code_simp

lemma cbw_rel_3: "relok 3"
  unfolding relok_def by code_simp

lemma cbw_rel_4: "relok 4"
  unfolding relok_def by code_simp

lemma cbw_rel_5: "relok 5"
  unfolding relok_def by code_simp

lemma cbw_rel_6: "relok 6"
  unfolding relok_def by code_simp

lemma cbw_rel_7: "relok 7"
  unfolding relok_def by code_simp

lemma cbw_rel_8: "relok 8"
  unfolding relok_def by code_simp

lemma cbw_rel_9: "relok 9"
  unfolding relok_def by code_simp

lemma cbw_rel_10: "relok 10"
  unfolding relok_def by code_simp

lemma cbw_rel_11: "relok 11"
  unfolding relok_def by code_simp

lemma cbw_rel_12: "relok 12"
  unfolding relok_def by code_simp

lemma cbw_rel_13: "relok 13"
  unfolding relok_def by code_simp

lemma cbw_rel_14: "relok 14"
  unfolding relok_def by code_simp

lemma cbw_rel_15: "relok 15"
  unfolding relok_def by code_simp

lemma cbw_rel_16: "relok 16"
  unfolding relok_def by code_simp

lemma cbw_rel_17: "relok 17"
  unfolding relok_def by code_simp

lemma cbw_rel_18: "relok 18"
  unfolding relok_def by code_simp

lemma cbw_rel_19: "relok 19"
  unfolding relok_def by code_simp

lemma cbw_rel_20: "relok 20"
  unfolding relok_def by code_simp

lemma cbw_rel_21: "relok 21"
  unfolding relok_def by code_simp

lemma cbw_rel_22: "relok 22"
  unfolding relok_def by code_simp

lemma cbw_rel_23: "relok 23"
  unfolding relok_def by code_simp

lemma cbw_rel_24: "relok 24"
  unfolding relok_def by code_simp

lemma cbw_rel_25: "relok 25"
  unfolding relok_def by code_simp

lemma cbw_rel_26: "relok 26"
  unfolding relok_def by code_simp

lemma cbw_rel_27: "relok 27"
  unfolding relok_def by code_simp

lemma cbw_rel_28: "relok 28"
  unfolding relok_def by code_simp

lemma cbw_rel_29: "relok 29"
  unfolding relok_def by code_simp

lemma cbw_rel_30: "relok 30"
  unfolding relok_def by code_simp

lemma cbw_rel_31: "relok 31"
  unfolding relok_def by code_simp

lemma cbw_rel_32: "relok 32"
  unfolding relok_def by code_simp

lemma cbw_rel_33: "relok 33"
  unfolding relok_def by code_simp

lemma cbw_rel_34: "relok 34"
  unfolding relok_def by code_simp

lemma cbw_rel_35: "relok 35"
  unfolding relok_def by code_simp

lemma cbw_rel_36: "relok 36"
  unfolding relok_def by code_simp

lemma cbw_rel_37: "relok 37"
  unfolding relok_def by code_simp

lemma cbw_rel_38: "relok 38"
  unfolding relok_def by code_simp

lemma cbw_rel_39: "relok 39"
  unfolding relok_def by code_simp

lemma cbw_rel_40: "relok 40"
  unfolding relok_def by code_simp

lemma cbw_rel_41: "relok 41"
  unfolding relok_def by code_simp

lemma cbw_rel_42: "relok 42"
  unfolding relok_def by code_simp

lemma cbw_rel_43: "relok 43"
  unfolding relok_def by code_simp

lemma cbw_rel_44: "relok 44"
  unfolding relok_def by code_simp

lemma cbw_rel_45: "relok 45"
  unfolding relok_def by code_simp

lemma cbw_rel_46: "relok 46"
  unfolding relok_def by code_simp

lemma cbw_rel_47: "relok 47"
  unfolding relok_def by code_simp

lemma cbw_rel_48: "relok 48"
  unfolding relok_def by code_simp

lemma cbw_rel_49: "relok 49"
  unfolding relok_def by code_simp

lemma cbw_rel_50: "relok 50"
  unfolding relok_def by code_simp

lemma cbw_rel_51: "relok 51"
  unfolding relok_def by code_simp

lemma cbw_rel_52: "relok 52"
  unfolding relok_def by code_simp

lemma cbw_rel_53: "relok 53"
  unfolding relok_def by code_simp

lemma cbw_rel_54: "relok 54"
  unfolding relok_def by code_simp

lemma cbw_rel_55: "relok 55"
  unfolding relok_def by code_simp

lemma cbw_rel_56: "relok 56"
  unfolding relok_def by code_simp

lemma cbw_rel_57: "relok 57"
  unfolding relok_def by code_simp

lemma cbw_rel_58: "relok 58"
  unfolding relok_def by code_simp

lemma cbw_rel_59: "relok 59"
  unfolding relok_def by code_simp

lemma cbw_rel_60: "relok 60"
  unfolding relok_def by code_simp

lemma cbw_rel_61: "relok 61"
  unfolding relok_def by code_simp

lemma cbw_rel_62: "relok 62"
  unfolding relok_def by code_simp

lemma all_0: "\<forall>j<(0::nat). relok j" by simp
lemma all_1: "\<forall>j<(1::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 1"
  then have "j < 0 \<or> j = 0" by linarith
  then show "relok j" using all_0 cbw_rel_0 by auto
qed
lemma all_2: "\<forall>j<(2::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 2"
  then have "j < 1 \<or> j = 1" by linarith
  then show "relok j" using all_1 cbw_rel_1 by auto
qed
lemma all_3: "\<forall>j<(3::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 3"
  then have "j < 2 \<or> j = 2" by linarith
  then show "relok j" using all_2 cbw_rel_2 by auto
qed
lemma all_4: "\<forall>j<(4::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 4"
  then have "j < 3 \<or> j = 3" by linarith
  then show "relok j" using all_3 cbw_rel_3 by auto
qed
lemma all_5: "\<forall>j<(5::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 5"
  then have "j < 4 \<or> j = 4" by linarith
  then show "relok j" using all_4 cbw_rel_4 by auto
qed
lemma all_6: "\<forall>j<(6::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 6"
  then have "j < 5 \<or> j = 5" by linarith
  then show "relok j" using all_5 cbw_rel_5 by auto
qed
lemma all_7: "\<forall>j<(7::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 7"
  then have "j < 6 \<or> j = 6" by linarith
  then show "relok j" using all_6 cbw_rel_6 by auto
qed
lemma all_8: "\<forall>j<(8::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 8"
  then have "j < 7 \<or> j = 7" by linarith
  then show "relok j" using all_7 cbw_rel_7 by auto
qed
lemma all_9: "\<forall>j<(9::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 9"
  then have "j < 8 \<or> j = 8" by linarith
  then show "relok j" using all_8 cbw_rel_8 by auto
qed
lemma all_10: "\<forall>j<(10::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 10"
  then have "j < 9 \<or> j = 9" by linarith
  then show "relok j" using all_9 cbw_rel_9 by auto
qed
lemma all_11: "\<forall>j<(11::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 11"
  then have "j < 10 \<or> j = 10" by linarith
  then show "relok j" using all_10 cbw_rel_10 by auto
qed
lemma all_12: "\<forall>j<(12::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 12"
  then have "j < 11 \<or> j = 11" by linarith
  then show "relok j" using all_11 cbw_rel_11 by auto
qed
lemma all_13: "\<forall>j<(13::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 13"
  then have "j < 12 \<or> j = 12" by linarith
  then show "relok j" using all_12 cbw_rel_12 by auto
qed
lemma all_14: "\<forall>j<(14::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 14"
  then have "j < 13 \<or> j = 13" by linarith
  then show "relok j" using all_13 cbw_rel_13 by auto
qed
lemma all_15: "\<forall>j<(15::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 15"
  then have "j < 14 \<or> j = 14" by linarith
  then show "relok j" using all_14 cbw_rel_14 by auto
qed
lemma all_16: "\<forall>j<(16::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 16"
  then have "j < 15 \<or> j = 15" by linarith
  then show "relok j" using all_15 cbw_rel_15 by auto
qed
lemma all_17: "\<forall>j<(17::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 17"
  then have "j < 16 \<or> j = 16" by linarith
  then show "relok j" using all_16 cbw_rel_16 by auto
qed
lemma all_18: "\<forall>j<(18::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 18"
  then have "j < 17 \<or> j = 17" by linarith
  then show "relok j" using all_17 cbw_rel_17 by auto
qed
lemma all_19: "\<forall>j<(19::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 19"
  then have "j < 18 \<or> j = 18" by linarith
  then show "relok j" using all_18 cbw_rel_18 by auto
qed
lemma all_20: "\<forall>j<(20::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 20"
  then have "j < 19 \<or> j = 19" by linarith
  then show "relok j" using all_19 cbw_rel_19 by auto
qed
lemma all_21: "\<forall>j<(21::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 21"
  then have "j < 20 \<or> j = 20" by linarith
  then show "relok j" using all_20 cbw_rel_20 by auto
qed
lemma all_22: "\<forall>j<(22::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 22"
  then have "j < 21 \<or> j = 21" by linarith
  then show "relok j" using all_21 cbw_rel_21 by auto
qed
lemma all_23: "\<forall>j<(23::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 23"
  then have "j < 22 \<or> j = 22" by linarith
  then show "relok j" using all_22 cbw_rel_22 by auto
qed
lemma all_24: "\<forall>j<(24::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 24"
  then have "j < 23 \<or> j = 23" by linarith
  then show "relok j" using all_23 cbw_rel_23 by auto
qed
lemma all_25: "\<forall>j<(25::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 25"
  then have "j < 24 \<or> j = 24" by linarith
  then show "relok j" using all_24 cbw_rel_24 by auto
qed
lemma all_26: "\<forall>j<(26::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 26"
  then have "j < 25 \<or> j = 25" by linarith
  then show "relok j" using all_25 cbw_rel_25 by auto
qed
lemma all_27: "\<forall>j<(27::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 27"
  then have "j < 26 \<or> j = 26" by linarith
  then show "relok j" using all_26 cbw_rel_26 by auto
qed
lemma all_28: "\<forall>j<(28::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 28"
  then have "j < 27 \<or> j = 27" by linarith
  then show "relok j" using all_27 cbw_rel_27 by auto
qed
lemma all_29: "\<forall>j<(29::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 29"
  then have "j < 28 \<or> j = 28" by linarith
  then show "relok j" using all_28 cbw_rel_28 by auto
qed
lemma all_30: "\<forall>j<(30::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 30"
  then have "j < 29 \<or> j = 29" by linarith
  then show "relok j" using all_29 cbw_rel_29 by auto
qed
lemma all_31: "\<forall>j<(31::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 31"
  then have "j < 30 \<or> j = 30" by linarith
  then show "relok j" using all_30 cbw_rel_30 by auto
qed
lemma all_32: "\<forall>j<(32::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 32"
  then have "j < 31 \<or> j = 31" by linarith
  then show "relok j" using all_31 cbw_rel_31 by auto
qed
lemma all_33: "\<forall>j<(33::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 33"
  then have "j < 32 \<or> j = 32" by linarith
  then show "relok j" using all_32 cbw_rel_32 by auto
qed
lemma all_34: "\<forall>j<(34::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 34"
  then have "j < 33 \<or> j = 33" by linarith
  then show "relok j" using all_33 cbw_rel_33 by auto
qed
lemma all_35: "\<forall>j<(35::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 35"
  then have "j < 34 \<or> j = 34" by linarith
  then show "relok j" using all_34 cbw_rel_34 by auto
qed
lemma all_36: "\<forall>j<(36::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 36"
  then have "j < 35 \<or> j = 35" by linarith
  then show "relok j" using all_35 cbw_rel_35 by auto
qed
lemma all_37: "\<forall>j<(37::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 37"
  then have "j < 36 \<or> j = 36" by linarith
  then show "relok j" using all_36 cbw_rel_36 by auto
qed
lemma all_38: "\<forall>j<(38::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 38"
  then have "j < 37 \<or> j = 37" by linarith
  then show "relok j" using all_37 cbw_rel_37 by auto
qed
lemma all_39: "\<forall>j<(39::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 39"
  then have "j < 38 \<or> j = 38" by linarith
  then show "relok j" using all_38 cbw_rel_38 by auto
qed
lemma all_40: "\<forall>j<(40::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 40"
  then have "j < 39 \<or> j = 39" by linarith
  then show "relok j" using all_39 cbw_rel_39 by auto
qed
lemma all_41: "\<forall>j<(41::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 41"
  then have "j < 40 \<or> j = 40" by linarith
  then show "relok j" using all_40 cbw_rel_40 by auto
qed
lemma all_42: "\<forall>j<(42::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 42"
  then have "j < 41 \<or> j = 41" by linarith
  then show "relok j" using all_41 cbw_rel_41 by auto
qed
lemma all_43: "\<forall>j<(43::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 43"
  then have "j < 42 \<or> j = 42" by linarith
  then show "relok j" using all_42 cbw_rel_42 by auto
qed
lemma all_44: "\<forall>j<(44::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 44"
  then have "j < 43 \<or> j = 43" by linarith
  then show "relok j" using all_43 cbw_rel_43 by auto
qed
lemma all_45: "\<forall>j<(45::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 45"
  then have "j < 44 \<or> j = 44" by linarith
  then show "relok j" using all_44 cbw_rel_44 by auto
qed
lemma all_46: "\<forall>j<(46::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 46"
  then have "j < 45 \<or> j = 45" by linarith
  then show "relok j" using all_45 cbw_rel_45 by auto
qed
lemma all_47: "\<forall>j<(47::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 47"
  then have "j < 46 \<or> j = 46" by linarith
  then show "relok j" using all_46 cbw_rel_46 by auto
qed
lemma all_48: "\<forall>j<(48::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 48"
  then have "j < 47 \<or> j = 47" by linarith
  then show "relok j" using all_47 cbw_rel_47 by auto
qed
lemma all_49: "\<forall>j<(49::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 49"
  then have "j < 48 \<or> j = 48" by linarith
  then show "relok j" using all_48 cbw_rel_48 by auto
qed
lemma all_50: "\<forall>j<(50::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 50"
  then have "j < 49 \<or> j = 49" by linarith
  then show "relok j" using all_49 cbw_rel_49 by auto
qed
lemma all_51: "\<forall>j<(51::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 51"
  then have "j < 50 \<or> j = 50" by linarith
  then show "relok j" using all_50 cbw_rel_50 by auto
qed
lemma all_52: "\<forall>j<(52::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 52"
  then have "j < 51 \<or> j = 51" by linarith
  then show "relok j" using all_51 cbw_rel_51 by auto
qed
lemma all_53: "\<forall>j<(53::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 53"
  then have "j < 52 \<or> j = 52" by linarith
  then show "relok j" using all_52 cbw_rel_52 by auto
qed
lemma all_54: "\<forall>j<(54::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 54"
  then have "j < 53 \<or> j = 53" by linarith
  then show "relok j" using all_53 cbw_rel_53 by auto
qed
lemma all_55: "\<forall>j<(55::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 55"
  then have "j < 54 \<or> j = 54" by linarith
  then show "relok j" using all_54 cbw_rel_54 by auto
qed
lemma all_56: "\<forall>j<(56::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 56"
  then have "j < 55 \<or> j = 55" by linarith
  then show "relok j" using all_55 cbw_rel_55 by auto
qed
lemma all_57: "\<forall>j<(57::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 57"
  then have "j < 56 \<or> j = 56" by linarith
  then show "relok j" using all_56 cbw_rel_56 by auto
qed
lemma all_58: "\<forall>j<(58::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 58"
  then have "j < 57 \<or> j = 57" by linarith
  then show "relok j" using all_57 cbw_rel_57 by auto
qed
lemma all_59: "\<forall>j<(59::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 59"
  then have "j < 58 \<or> j = 58" by linarith
  then show "relok j" using all_58 cbw_rel_58 by auto
qed
lemma all_60: "\<forall>j<(60::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 60"
  then have "j < 59 \<or> j = 59" by linarith
  then show "relok j" using all_59 cbw_rel_59 by auto
qed
lemma all_61: "\<forall>j<(61::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 61"
  then have "j < 60 \<or> j = 60" by linarith
  then show "relok j" using all_60 cbw_rel_60 by auto
qed
lemma all_62: "\<forall>j<(62::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 62"
  then have "j < 61 \<or> j = 61" by linarith
  then show "relok j" using all_61 cbw_rel_61 by auto
qed
lemma all_63: "\<forall>j<(63::nat). relok j"
proof (intro allI impI)
  fix j :: nat assume "j < 63"
  then have "j < 62 \<or> j = 62" by linarith
  then show "relok j" using all_62 cbw_rel_62 by auto
qed

lemma cbw_relation: "j < 63 \<Longrightarrow> gfmulw (cbw ! Suc j) (cbw ! Suc j) XOR (cbw ! Suc j) = cbw ! j"
  using all_63 by (simp add: relok_def)

lemma cbw_0: "cbw ! 0 = 1"
  by (simp add: cbw_def)

definition beta :: "nat \<Rightarrow> gf64" where
  "beta j = gfw (cbw ! j)"

lemma pw_one: "pw (1 :: 'a :: len word) = 1"
  by (rule poly_eqI) (auto simp: coeff_pw bit_1_iff coeff_1)

lemma gfw_one: "gfw 1 = 1"
  by (metis Rep_gf64_inject Rep_gfw one_gf64.rep_eq pw_one)

theorem beta_cantor: "cantor_basis 64 beta"
  unfolding cantor_basis_def
proof (intro conjI allI impI)
  show "beta 0 = 1" by (simp add: beta_def cbw_0 gfw_one)
next
  fix j assume "Suc j < 64"
  then have "gfmulw (cbw ! Suc j) (cbw ! Suc j) XOR (cbw ! Suc j) = cbw ! j" by (intro cbw_relation) simp
  then have "gfw (gfmulw (cbw ! Suc j) (cbw ! Suc j) XOR (cbw ! Suc j)) = gfw (cbw ! j)" by simp
  then show "beta (Suc j) * beta (Suc j) + beta (Suc j) = beta j"
    by (simp add: beta_def gfw_xor gfmulw_gf)
qed

end
