theory "AVX3"
imports "Cryptol.Cryptol" AVXK Fold GF2X KM3 Toom
begin

context includes cryptol_translation_syntax begin
cryptol_definition km16 :: "([16][64]) \<Rightarrow> (([16][64]) \<Rightarrow> ([32][64]))" where
"km16  \<equiv> GF2X.kstep`{8,8} KM3.km8 KM3.km8"

cryptol_definition km32 :: "([32][64]) \<Rightarrow> (([32][64]) \<Rightarrow> ([64][64]))" where
"km32  \<equiv> GF2X.kstep`{16,16} km16 km16"

cryptol_definition km64 :: "([64][64]) \<Rightarrow> (([64][64]) \<Rightarrow> ([128][64]))" where
"km64  \<equiv> GF2X.kstep`{32,32} km32 km32"

cryptol_definition km192 :: "([192][64]) \<Rightarrow> (([192][64]) \<Rightarrow> ([384][64]))" where
"km192  \<equiv> AVXK.k3step`{64} km64"

cryptol_definition tm3 :: "([570][64]) \<Rightarrow> (([570][64]) \<Rightarrow> ([1144][64]))" where
"tm3  \<equiv> Toom.toom3`{190} km192"

cryptol_definition vmulA :: "([572][64]) \<Rightarrow> (([572][64]) \<Rightarrow> ([561][64]))" where
"vmulA a b \<equiv> Fold.fold`{35851,561} (take`{1122,22,[64]} (tm3`{} (take`{570,2,[64]} a) (take`{570,2,[64]} b)))"

cryptol_definition vmulBytes :: "([572][64]) \<Rightarrow> (([572][64]) \<Rightarrow> ([4482][8]))" where
"vmulBytes a b \<equiv> take`{4482,6,[8]} (join`{561,8,[8]} (seq_compr`{561,[64],[8][8]} (\<lambda>(x :: [64]). (reverse`{8,[8]} (split`{8,8,Bit} x))) (vmulA`{} a b)))"

end
end
