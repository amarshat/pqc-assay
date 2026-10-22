theory "KM3"
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

cryptol_definition km70 :: "([70][64]) \<Rightarrow> (([70][64]) \<Rightarrow> ([140][64]))" where
"km70  \<equiv> GF2X.kstep`{35,35} km35 km35"

cryptol_definition km140 :: "([140][64]) \<Rightarrow> (([140][64]) \<Rightarrow> ([280][64]))" where
"km140  \<equiv> GF2X.kstep`{70,70} km70 km70"

cryptol_definition km36 :: "([36][64]) \<Rightarrow> (([36][64]) \<Rightarrow> ([72][64]))" where
"km36  \<equiv> GF2X.kstep`{18,18} km18 km18"

cryptol_definition km71 :: "([71][64]) \<Rightarrow> (([71][64]) \<Rightarrow> ([142][64]))" where
"km71  \<equiv> GF2X.kstep`{35,36} km35 km36"

cryptol_definition km141 :: "([141][64]) \<Rightarrow> (([141][64]) \<Rightarrow> ([282][64]))" where
"km141  \<equiv> GF2X.kstep`{70,71} km70 km71"

cryptol_definition km280 :: "([280][64]) \<Rightarrow> (([280][64]) \<Rightarrow> ([560][64]))" where
"km280  \<equiv> GF2X.kstep`{140,140} km140 km140"

cryptol_definition km281 :: "([281][64]) \<Rightarrow> (([281][64]) \<Rightarrow> ([562][64]))" where
"km281  \<equiv> GF2X.kstep`{140,141} km140 km141"

cryptol_definition km561 :: "([561][64]) \<Rightarrow> (([561][64]) \<Rightarrow> ([1122][64]))" where
"km561  \<equiv> GF2X.kstep`{280,281} km280 km281"

cryptol_definition vmul :: "([561][64]) \<Rightarrow> (([561][64]) \<Rightarrow> ([561][64]))" where
"vmul a b \<equiv> Fold.fold`{35851,561} (km561`{} a b)"

end
end
