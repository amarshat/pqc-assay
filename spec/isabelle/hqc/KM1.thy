theory "KM1"
imports "Cryptol.Cryptol" Fold GF2X
begin

context includes cryptol_translation_syntax begin
cryptol_definition km2 :: "([2][64]) \<Rightarrow> (([2][64]) \<Rightarrow> ([4][64]))" where
"km2  \<equiv> GF2X.kstep`{1,1} GF2X.km1 GF2X.km1"

cryptol_definition km3 :: "([3][64]) \<Rightarrow> (([3][64]) \<Rightarrow> ([6][64]))" where
"km3  \<equiv> GF2X.kstep`{1,2} GF2X.km1 km2"

cryptol_definition km5 :: "([5][64]) \<Rightarrow> (([5][64]) \<Rightarrow> ([10][64]))" where
"km5  \<equiv> GF2X.kstep`{2,3} km2 km3"

cryptol_definition km4 :: "([4][64]) \<Rightarrow> (([4][64]) \<Rightarrow> ([8][64]))" where
"km4  \<equiv> GF2X.kstep`{2,2} km2 km2"

cryptol_definition km9 :: "([9][64]) \<Rightarrow> (([9][64]) \<Rightarrow> ([18][64]))" where
"km9  \<equiv> GF2X.kstep`{4,5} km4 km5"

cryptol_definition km18 :: "([18][64]) \<Rightarrow> (([18][64]) \<Rightarrow> ([36][64]))" where
"km18  \<equiv> GF2X.kstep`{9,9} km9 km9"

cryptol_definition km8 :: "([8][64]) \<Rightarrow> (([8][64]) \<Rightarrow> ([16][64]))" where
"km8  \<equiv> GF2X.kstep`{4,4} km4 km4"

cryptol_definition km17 :: "([17][64]) \<Rightarrow> (([17][64]) \<Rightarrow> ([34][64]))" where
"km17  \<equiv> GF2X.kstep`{8,9} km8 km9"

cryptol_definition km35 :: "([35][64]) \<Rightarrow> (([35][64]) \<Rightarrow> ([70][64]))" where
"km35  \<equiv> GF2X.kstep`{17,18} km17 km18"

cryptol_definition km34 :: "([34][64]) \<Rightarrow> (([34][64]) \<Rightarrow> ([68][64]))" where
"km34  \<equiv> GF2X.kstep`{17,17} km17 km17"

cryptol_definition km69 :: "([69][64]) \<Rightarrow> (([69][64]) \<Rightarrow> ([138][64]))" where
"km69  \<equiv> GF2X.kstep`{34,35} km34 km35"

cryptol_definition km138 :: "([138][64]) \<Rightarrow> (([138][64]) \<Rightarrow> ([276][64]))" where
"km138  \<equiv> GF2X.kstep`{69,69} km69 km69"

cryptol_definition km70 :: "([70][64]) \<Rightarrow> (([70][64]) \<Rightarrow> ([140][64]))" where
"km70  \<equiv> GF2X.kstep`{35,35} km35 km35"

cryptol_definition km139 :: "([139][64]) \<Rightarrow> (([139][64]) \<Rightarrow> ([278][64]))" where
"km139  \<equiv> GF2X.kstep`{69,70} km69 km70"

cryptol_definition km277 :: "([277][64]) \<Rightarrow> (([277][64]) \<Rightarrow> ([554][64]))" where
"km277  \<equiv> GF2X.kstep`{138,139} km138 km139"

cryptol_definition vmul :: "([277][64]) \<Rightarrow> (([277][64]) \<Rightarrow> ([277][64]))" where
"vmul a b \<equiv> Fold.fold`{17669,277} (km277`{} a b)"

end
end
