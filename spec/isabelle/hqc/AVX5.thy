theory "AVX5"
imports "Cryptol.Cryptol" AVXK Fold GF2X KM5 Toom5
begin

context includes cryptol_translation_syntax begin
cryptol_definition km16 :: "([16][64]) \<Rightarrow> (([16][64]) \<Rightarrow> ([32][64]))" where
"km16  \<equiv> GF2X.kstep`{8,8} KM5.km8 KM5.km8"

cryptol_definition km32 :: "([32][64]) \<Rightarrow> (([32][64]) \<Rightarrow> ([64][64]))" where
"km32  \<equiv> GF2X.kstep`{16,16} km16 km16"

cryptol_definition km64 :: "([64][64]) \<Rightarrow> (([64][64]) \<Rightarrow> ([128][64]))" where
"km64  \<equiv> GF2X.kstep`{32,32} km32 km32"

cryptol_definition km320 :: "([320][64]) \<Rightarrow> (([320][64]) \<Rightarrow> ([640][64]))" where
"km320  \<equiv> AVXK.k5step`{64} km64"

cryptol_definition tm5 :: "([936][64]) \<Rightarrow> (([936][64]) \<Rightarrow> ([1872][64]))" where
"tm5  \<equiv> Toom5.toom5`{} km320"

cryptol_definition vmulA :: "([936][64]) \<Rightarrow> (([936][64]) \<Rightarrow> ([901][64]))" where
"vmulA a b \<equiv> Fold.fold`{57637,901} (take`{1802,70,[64]} (tm5`{} a b))"

cryptol_definition vmulBytes :: "([936][64]) \<Rightarrow> (([936][64]) \<Rightarrow> ([7205][8]))" where
"vmulBytes a b \<equiv> take`{7205,3,[8]} (join`{901,8,[8]} (seq_compr`{901,[64],[8][8]} (\<lambda>(x :: [64]). (reverse`{8,[8]} (split`{8,8,Bit} x))) (vmulA`{} a b)))"

end
end
