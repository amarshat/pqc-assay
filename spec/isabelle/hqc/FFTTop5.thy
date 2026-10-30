theory "FFTTop5"
imports "Cryptol.Cryptol" FFTBC FFTEnc FFTRef FFTTop
begin

context includes cryptol_translation_syntax begin
cryptol_definition inputT5 :: "([1024][64]) \<Rightarrow> ([2048][64])" where
"inputT5 a \<equiv> FFTRef.btfy11`{} ((0x1 :: [64]) <<`{64,Integer,Bit} (43 :: Integer)) (FFTEnc.encode5`{} (FFTTop.as64`{1024} (FFTBC.bc1_65536wc`{} (FFTTop.as32`{1024} a))))"

cryptol_definition mulT5 :: "([2048][64]) \<Rightarrow> (([2048][64]) \<Rightarrow> ([2048][64]))" where
"mulT5 afft bfft \<equiv> FFTTop.as64`{2048} (FFTBC.ibc1_131072w`{} (FFTTop.as32`{2048} (FFTEnc.decode5`{} (FFTRef.ibtfy11`{} ((0x1 :: [64]) <<`{64,Integer,Bit} (43 :: Integer)) (FFTRef.gf264v`{2048} afft bfft)))))"

end
end
