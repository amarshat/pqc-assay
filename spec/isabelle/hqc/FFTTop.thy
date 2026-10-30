theory "FFTTop"
imports "Cryptol.Cryptol" FFTBC FFTEnc FFTRef
begin

context includes cryptol_translation_syntax begin
cryptol_definition as32 :: "{'n} ((fin 'n) =?> ((['n][64]) \<Rightarrow> ([2 * 'n][32])))" where
"as32 v \<equiv> join`{'n,2,[32]} (seq_compr`{'n,[64],[2][32]} (\<lambda>(x :: [64]). (list_to_seq [(drop`{32,32,Bit} x) : ([32]),(take`{32,32,Bit} x) : ([32])] :: [2][32])) v)"

cryptol_definition as64 :: "{'n} ((fin 'n) =?> (([2 * 'n][32]) \<Rightarrow> (['n][64])))" where
"as64 v \<equiv> seq_compr`{'n,[2][32],[64]} (\<lambda>(i__p0 :: [2][32]). (
  let
    lo = ((i__p0 @`{2,[32],Integer} (0 :: Integer)) : ([32]));
    hi = ((i__p0 @`{2,[32],Integer} (1 :: Integer)) : ([32]))
  in (hi #`{32,32,Bit} lo))) (split`{'n,2,[32]} v)"

cryptol_definition inputT :: "([280][64]) \<Rightarrow> ([512][64])" where
"inputT a \<equiv> FFTRef.btfy9`{} ((0x1 :: [64]) <<`{64,Integer,Bit} (41 :: Integer)) (FFTEnc.encode`{} (as64`{256} (FFTBC.bc1w`{} (as32`{256} (take`{256,24,[64]} a)))))"

cryptol_definition seg :: "{'o,'n,'r} ((fin 'o,fin 'n,fin 'r) =?> (([('o + 'n) + 'r][64]) \<Rightarrow> (['n][64])))" where
"seg v \<equiv> take`{'n,'r,[64]} (drop`{'o,'n + 'r,[64]} v)"

cryptol_definition pl :: "{'o,'n} ((fin 'o,fin 'n,('o + 'n) <= 560) =?> ((['n][64]) \<Rightarrow> ([560][64])))" where
"pl v \<equiv> (zero`{['o][64]}) #`{'o,(560 - ('o + 'n)) + 'n,[64]} (v #`{'n,560 - ('o + 'n),[64]} (zero`{[560 - ('o + 'n)][64]}))"

cryptol_definition mulT :: "([280][64]) \<Rightarrow> (([280][64]) \<Rightarrow> (([512][64]) \<Rightarrow> (([512][64]) \<Rightarrow> ([560][64]))))" where
"mulT a b afft bfft \<equiv> 
  let
    fftpart = ((as64`{512} (FFTBC.ibc1_32768w`{} (as32`{512} (FFTEnc.decode`{} (FFTRef.ibtfy9`{} ((0x1 :: [64]) <<`{64,Integer,Bit} (41 :: Integer)) (FFTRef.gf264v`{512} afft bfft)))))) : ([512][64]));
    arem = ((drop`{256,24,[64]} a) : ([24][64]));
    brem = ((drop`{256,24,[64]} b) : ([24][64]));
    cross = (((((((((((((((pl`{512,48} (FFTRef.km24`{} arem brem)) ^`{[560][64]} (pl`{256,48} ((FFTRef.km24`{} (seg`{0,24,256} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{0,24,256} b) arem)))) ^`{[560][64]} (pl`{280,48} ((FFTRef.km24`{} (seg`{24,24,232} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{24,24,232} b) arem)))) ^`{[560][64]} (pl`{304,48} ((FFTRef.km24`{} (seg`{48,24,208} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{48,24,208} b) arem)))) ^`{[560][64]} (pl`{328,48} ((FFTRef.km24`{} (seg`{72,24,184} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{72,24,184} b) arem)))) ^`{[560][64]} (pl`{352,48} ((FFTRef.km24`{} (seg`{96,24,160} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{96,24,160} b) arem)))) ^`{[560][64]} (pl`{376,48} ((FFTRef.km24`{} (seg`{120,24,136} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{120,24,136} b) arem)))) ^`{[560][64]} (pl`{400,48} ((FFTRef.km24`{} (seg`{144,24,112} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{144,24,112} b) arem)))) ^`{[560][64]} (pl`{424,48} ((FFTRef.km24`{} (seg`{168,24,88} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{168,24,88} b) arem)))) ^`{[560][64]} (pl`{448,48} ((FFTRef.km24`{} (seg`{192,24,64} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{192,24,64} b) arem)))) ^`{[560][64]} (pl`{472,48} ((FFTRef.km24`{} (seg`{216,24,40} a) brem) ^`{[48][64]} (FFTRef.km24`{} (seg`{216,24,40} b) arem)))) ^`{[560][64]} (pl`{496,32} ((FFTRef.km16`{} (seg`{240,16,24} a) (take`{16,8,[64]} brem)) ^`{[32][64]} (FFTRef.km16`{} (seg`{240,16,24} b) (take`{16,8,[64]} arem))))) ^`{[560][64]} (pl`{512,16} ((FFTRef.km8`{} (seg`{240,8,32} a) (drop`{16,8,[64]} brem)) ^`{[16][64]} (FFTRef.km8`{} (seg`{240,8,32} b) (drop`{16,8,[64]} arem))))) ^`{[560][64]} (pl`{520,16} ((FFTRef.km8`{} (seg`{248,8,24} a) (drop`{16,8,[64]} brem)) ^`{[16][64]} (FFTRef.km8`{} (seg`{248,8,24} b) (drop`{16,8,[64]} arem))))) : ([560][64]))
  in ((fftpart #`{512,48,[64]} (zero`{[48][64]})) ^`{[560][64]} cross)"

end
end
