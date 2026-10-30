theory "FFTWire"
imports "Cryptol.Cryptol" FFTTop FFTTop3 FFTTop5 Fold
begin

context includes cryptol_translation_syntax begin
cryptol_definition input17920 :: "([280][64]) \<Rightarrow> ([792][64])" where
"input17920 a \<equiv> (FFTTop.inputT`{} a) #`{512,280,[64]} a"

cryptol_definition input36864 :: "([576][64]) \<Rightarrow> ([1600][64])" where
"input36864 a \<equiv> (FFTTop3.inputT3`{} a) #`{1024,576,[64]} a"

cryptol_definition mul17920 :: "([792][64]) \<Rightarrow> (([792][64]) \<Rightarrow> ([560][64]))" where
"mul17920 af bf \<equiv> FFTTop.mulT`{} (drop`{512,280,[64]} af) (drop`{512,280,[64]} bf) (take`{512,280,[64]} af) (take`{512,280,[64]} bf)"

cryptol_definition mul36864 :: "([1600][64]) \<Rightarrow> (([1600][64]) \<Rightarrow> ([1152][64]))" where
"mul36864 af bf \<equiv> FFTTop3.mulT3`{} (drop`{1024,576,[64]} af) (drop`{1024,576,[64]} bf) (take`{1024,576,[64]} af) (take`{1024,576,[64]} bf)"

cryptol_definition pad1 :: "([277][64]) \<Rightarrow> ([280][64])" where
"pad1 v \<equiv> (take`{276,1,[64]} v) #`{276,4,[64]} ((list_to_seq [((v @`{277,[64],Integer} (276 :: Integer)) &&`{[64]} (0xff :: [64])) : ([64])] :: [1][64]) #`{1,3,[64]} (zero`{[3][64]}))"

cryptol_definition pad3 :: "([561][64]) \<Rightarrow> ([576][64])" where
"pad3 v \<equiv> (take`{560,1,[64]} v) #`{560,16,[64]} ((list_to_seq [((v @`{561,[64],Integer} (560 :: Integer)) &&`{[64]} (0xffff :: [64])) : ([64])] :: [1][64]) #`{1,15,[64]} (zero`{[15][64]}))"

cryptol_definition pad5 :: "([901][64]) \<Rightarrow> ([1024][64])" where
"pad5 v \<equiv> (take`{900,1,[64]} v) #`{900,124,[64]} ((list_to_seq [((v @`{901,[64],Integer} (900 :: Integer)) &&`{[64]} (0xffffffffff :: [64])) : ([64])] :: [1][64]) #`{1,123,[64]} (zero`{[123][64]}))"

cryptol_definition vmulF1 :: "([277][64]) \<Rightarrow> (([277][64]) \<Rightarrow> ([277][64]))" where
"vmulF1 a b \<equiv> 
  let
    pa = ((pad1`{} a) : ([280][64]));
    pb = ((pad1`{} b) : ([280][64]))
  in (Fold.fold`{17669,277} (take`{554,6,[64]} (FFTTop.mulT`{} pa pb (FFTTop.inputT`{} pa) (FFTTop.inputT`{} pb))))"

cryptol_definition vmulF3 :: "([561][64]) \<Rightarrow> (([561][64]) \<Rightarrow> ([561][64]))" where
"vmulF3 a b \<equiv> 
  let
    pa = ((pad3`{} a) : ([576][64]));
    pb = ((pad3`{} b) : ([576][64]))
  in (Fold.fold`{35851,561} (take`{1122,30,[64]} (FFTTop3.mulT3`{} pa pb (FFTTop3.inputT3`{} pa) (FFTTop3.inputT3`{} pb))))"

cryptol_definition vmulF5 :: "([901][64]) \<Rightarrow> (([901][64]) \<Rightarrow> ([901][64]))" where
"vmulF5 a b \<equiv> Fold.fold`{57637,901} (take`{1802,246,[64]} (FFTTop5.mulT5`{} (FFTTop5.inputT5`{} (pad5`{} a)) (FFTTop5.inputT5`{} (pad5`{} b))))"

end
end
