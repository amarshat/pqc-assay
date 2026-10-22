theory "KM5"
imports "Cryptol.Cryptol" Fold GF2X
begin

context includes cryptol_translation_syntax begin
cryptol_definition km2 :: "([2][64]) \<Rightarrow> (([2][64]) \<Rightarrow> ([4][64]))" where
"km2  \<equiv> GF2X.kstep`{1,1} GF2X.km1 GF2X.km1"

cryptol_definition km4 :: "([4][64]) \<Rightarrow> (([4][64]) \<Rightarrow> ([8][64]))" where
"km4  \<equiv> GF2X.kstep`{2,2} km2 km2"

cryptol_definition km3 :: "([3][64]) \<Rightarrow> (([3][64]) \<Rightarrow> ([6][64]))" where
"km3  \<equiv> GF2X.kstep`{1,2} GF2X.km1 km2"

cryptol_definition km7 :: "([7][64]) \<Rightarrow> (([7][64]) \<Rightarrow> ([14][64]))" where
"km7  \<equiv> GF2X.kstep`{3,4} km3 km4"

cryptol_definition km14 :: "([14][64]) \<Rightarrow> (([14][64]) \<Rightarrow> ([28][64]))" where
"km14  \<equiv> GF2X.kstep`{7,7} km7 km7"

cryptol_definition km28 :: "([28][64]) \<Rightarrow> (([28][64]) \<Rightarrow> ([56][64]))" where
"km28  \<equiv> GF2X.kstep`{14,14} km14 km14"

cryptol_definition km56 :: "([56][64]) \<Rightarrow> (([56][64]) \<Rightarrow> ([112][64]))" where
"km56  \<equiv> GF2X.kstep`{28,28} km28 km28"

cryptol_definition km112 :: "([112][64]) \<Rightarrow> (([112][64]) \<Rightarrow> ([224][64]))" where
"km112  \<equiv> GF2X.kstep`{56,56} km56 km56"

cryptol_definition km8 :: "([8][64]) \<Rightarrow> (([8][64]) \<Rightarrow> ([16][64]))" where
"km8  \<equiv> GF2X.kstep`{4,4} km4 km4"

cryptol_definition km15 :: "([15][64]) \<Rightarrow> (([15][64]) \<Rightarrow> ([30][64]))" where
"km15  \<equiv> GF2X.kstep`{7,8} km7 km8"

cryptol_definition km29 :: "([29][64]) \<Rightarrow> (([29][64]) \<Rightarrow> ([58][64]))" where
"km29  \<equiv> GF2X.kstep`{14,15} km14 km15"

cryptol_definition km57 :: "([57][64]) \<Rightarrow> (([57][64]) \<Rightarrow> ([114][64]))" where
"km57  \<equiv> GF2X.kstep`{28,29} km28 km29"

cryptol_definition km113 :: "([113][64]) \<Rightarrow> (([113][64]) \<Rightarrow> ([226][64]))" where
"km113  \<equiv> GF2X.kstep`{56,57} km56 km57"

cryptol_definition km225 :: "([225][64]) \<Rightarrow> (([225][64]) \<Rightarrow> ([450][64]))" where
"km225  \<equiv> GF2X.kstep`{112,113} km112 km113"

cryptol_definition km226 :: "([226][64]) \<Rightarrow> (([226][64]) \<Rightarrow> ([452][64]))" where
"km226  \<equiv> GF2X.kstep`{113,113} km113 km113"

cryptol_definition km450 :: "([450][64]) \<Rightarrow> (([450][64]) \<Rightarrow> ([900][64]))" where
"km450  \<equiv> GF2X.kstep`{225,225} km225 km225"

cryptol_definition km451 :: "([451][64]) \<Rightarrow> (([451][64]) \<Rightarrow> ([902][64]))" where
"km451  \<equiv> GF2X.kstep`{225,226} km225 km226"

cryptol_definition km901 :: "([901][64]) \<Rightarrow> (([901][64]) \<Rightarrow> ([1802][64]))" where
"km901  \<equiv> GF2X.kstep`{450,451} km450 km451"

cryptol_definition vmul :: "([901][64]) \<Rightarrow> (([901][64]) \<Rightarrow> ([901][64]))" where
"vmul a b \<equiv> Fold.fold`{57637,901} (km901`{} a b)"

end
end
