theory "FFTTop3"
imports "Cryptol.Cryptol" FFTBC FFTEnc FFTRef FFTTop
begin

context includes cryptol_translation_syntax begin
cryptol_definition inputT3 :: "([576][64]) \<Rightarrow> ([1024][64])" where
"inputT3 a \<equiv> FFTRef.btfy10`{} ((0x1 :: [64]) <<`{64,Integer,Bit} (42 :: Integer)) (FFTEnc.encode3`{} (FFTTop.as64`{512} (FFTBC.bc1_32768wc`{} (FFTTop.as32`{512} (take`{512,64,[64]} a)))))"

cryptol_definition seg3 :: "{'o,'n,'r} ((fin 'o,fin 'n,fin 'r) =?> (([('o + 'n) + 'r][64]) \<Rightarrow> (['n][64])))" where
"seg3 v \<equiv> take`{'n,'r,[64]} (drop`{'o,'n + 'r,[64]} v)"

cryptol_definition pl3 :: "{'o,'n} ((fin 'o,fin 'n,('o + 'n) <= 1152) =?> ((['n][64]) \<Rightarrow> ([1152][64])))" where
"pl3 v \<equiv> (zero`{['o][64]}) #`{'o,(1152 - ('o + 'n)) + 'n,[64]} (v #`{'n,1152 - ('o + 'n),[64]} (zero`{[1152 - ('o + 'n)][64]}))"

cryptol_definition mulT3 :: "([576][64]) \<Rightarrow> (([576][64]) \<Rightarrow> (([1024][64]) \<Rightarrow> (([1024][64]) \<Rightarrow> ([1152][64]))))" where
"mulT3 a b afft bfft \<equiv> 
  let
    fftpart = ((FFTTop.as64`{1024} (FFTBC.ibc1_65536w`{} (FFTTop.as32`{1024} (FFTEnc.decode3`{} (FFTRef.ibtfy10`{} ((0x1 :: [64]) <<`{64,Integer,Bit} (42 :: Integer)) (FFTRef.gf264v`{1024} afft bfft)))))) : ([1024][64]));
    arem = ((drop`{512,64,[64]} a) : ([64][64]));
    brem = ((drop`{512,64,[64]} b) : ([64][64]));
    cross = ((((((((((pl3`{1024,128} (FFTRef.km64`{} arem brem)) ^`{[1152][64]} (pl3`{512,128} ((FFTRef.km64`{} (seg3`{0,64,512} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{0,64,512} b) arem)))) ^`{[1152][64]} (pl3`{576,128} ((FFTRef.km64`{} (seg3`{64,64,448} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{64,64,448} b) arem)))) ^`{[1152][64]} (pl3`{640,128} ((FFTRef.km64`{} (seg3`{128,64,384} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{128,64,384} b) arem)))) ^`{[1152][64]} (pl3`{704,128} ((FFTRef.km64`{} (seg3`{192,64,320} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{192,64,320} b) arem)))) ^`{[1152][64]} (pl3`{768,128} ((FFTRef.km64`{} (seg3`{256,64,256} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{256,64,256} b) arem)))) ^`{[1152][64]} (pl3`{832,128} ((FFTRef.km64`{} (seg3`{320,64,192} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{320,64,192} b) arem)))) ^`{[1152][64]} (pl3`{896,128} ((FFTRef.km64`{} (seg3`{384,64,128} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{384,64,128} b) arem)))) ^`{[1152][64]} (pl3`{960,128} ((FFTRef.km64`{} (seg3`{448,64,64} a) brem) ^`{[128][64]} (FFTRef.km64`{} (seg3`{448,64,64} b) arem)))) : ([1152][64]))
  in ((fftpart #`{1024,128,[64]} (zero`{[128][64]})) ^`{[1152][64]} cross)"

end
end
