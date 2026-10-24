theory "AVX1"
imports "Cryptol.Cryptol" AVXK Fold GF2X KM1 Toom
begin

context includes cryptol_translation_syntax begin
cryptol_definition km16 :: "([16][64]) \<Rightarrow> (([16][64]) \<Rightarrow> ([32][64]))" where
"km16  \<equiv> GF2X.kstep`{8,8} KM1.km8 KM1.km8"

cryptol_definition km32 :: "([32][64]) \<Rightarrow> (([32][64]) \<Rightarrow> ([64][64]))" where
"km32  \<equiv> GF2X.kstep`{16,16} km16 km16"

cryptol_definition km96 :: "([96][64]) \<Rightarrow> (([96][64]) \<Rightarrow> ([192][64]))" where
"km96  \<equiv> AVXK.k3step`{32} km32"

cryptol_definition tm1 :: "([282][64]) \<Rightarrow> (([282][64]) \<Rightarrow> ([568][64]))" where
"tm1  \<equiv> Toom.toom3`{94} km96"

cryptol_definition vmulA :: "([284][64]) \<Rightarrow> (([284][64]) \<Rightarrow> ([277][64]))" where
"vmulA a b \<equiv> Fold.fold`{17669,277} (take`{554,14,[64]} (tm1`{} (take`{282,2,[64]} a) (take`{282,2,[64]} b)))"

cryptol_definition vmulBytes :: "([284][64]) \<Rightarrow> (([284][64]) \<Rightarrow> ([2209][8]))" where
"vmulBytes a b \<equiv> take`{2209,7,[8]} (join`{277,8,[8]} (seq_compr`{277,[64],[8][8]} (\<lambda>(x :: [64]). (reverse`{8,[8]} (split`{8,8,Bit} x))) (vmulA`{} a b)))"

end
end
