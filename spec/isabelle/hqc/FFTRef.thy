theory "FFTRef"
imports "Cryptol.Cryptol" AVXK GF2X
begin

context includes cryptol_translation_syntax begin
cryptol_definition cantorBasis :: "[64][64]" where
"cantorBasis  \<equiv> list_to_seq [0x1 :: [64],0x19c9369f278adc02 :: [64],0xa181e7d66f5ff794 :: [64],0x5db84357ce785d08 :: [64],0xb973d466f5c9d0ca :: [64],0x521ac889831a075e :: [64],0x33ce8beddc8a656 :: [64],0xb5846c4e07b91010 :: [64],0x4087b8cbb37a32ec :: [64],0xd0d3888c0ae17c :: [64],0xafd5ac70237f2222 :: [64],0xe3f5af99cc3aaaf8 :: [64],0x5a1db3b16a0b58b8 :: [64],0x9947c54fe7ee248 :: [64],0xe8eaf0e0068f544 :: [64],0xa2a113500b4b4f5a :: [64],0xe96f9805d6ce0bb0 :: [64],0x53496f8b5c9edd4c :: [64],0xad325cb6f4ac2a9e :: [64],0x4a8dcf8bd7ede826 :: [64],0xa3e9c552b6434210 :: [64],0x5fa92ad9c9bc7ed0 :: [64],0xa389f910cd7734de :: [64],0xe916f3dfca4609d8 :: [64],0xf89578714bd28f96 :: [64],0x564dda59237a3352 :: [64],0xad33bc6cc75aed38 :: [64],0x57a3104fcd0e5f34 :: [64],0xb0f502e4cd60039a :: [64],0xeb42e79f91f49f8c :: [64],0x54e5bf3774b3f850 :: [64],0xb66864e6ec14b4d2 :: [64],0xed57ce778f0d6244 :: [64],0x523aaf9d6148ba24 :: [64],0xa8fcbfaac14940c6 :: [64],0xe503eacfcef77780 :: [64],0xf3746c7b5183a372 :: [64],0xec50d77d2f416218 :: [64],0xf9cdf54569fe87e6 :: [64],0xe576269915705e2c :: [64],0xee2a197148fa8c72 :: [64],0x49e31453575f365a :: [64],0xb86698d88add0bc0 :: [64],0x4f35fb218e7f37c0 :: [64],0xa306feea8a242832 :: [64],0x5e5f06a9daead6e6 :: [64],0xbe13089ecc784ea0 :: [64],0xfe1a10738739c892 :: [64],0xe2266ceb0c5bc774 :: [64],0xf490e6ed40d1dd1a :: [64],0xf3f5f515077e92f0 :: [64],0x467c20312e7eb0f0 :: [64],0xb06caa4295d350c2 :: [64],0x5c5916d98a583c16 :: [64],0xa04de5b4c7a1ceac :: [64],0x41430183d6e85ec0 :: [64],0xb361d8dabe3b3632 :: [64],0x4357375d88b88b56 :: [64],0xb057dcc8a19fbc9c :: [64],0xf26e1791be4b37c2 :: [64],0xe9f744031bfe63e4 :: [64],0xe50803875e9ab776 :: [64],0x44ee098f4d56753e :: [64],0x9dc338f8399031b4 :: [64]] :: [64][64]"

cryptol_definition cantor :: "([64]) \<Rightarrow> ([64])" where
"cantor v \<equiv> foldl`{64,[64],[64]} (\<lblot>^`{[64]}\<rblot>) (0x0 :: [64]) (seq_compr`{64,Integer,[64]} (\<lambda>(i :: Integer). (if v !`{64,Bit,Integer} i then (cantorBasis @`{64,[64],Integer} i) else coerce (0x0 :: [64]))) (fromTo`{0,63,Integer}))"

cryptol_definition fold64 :: "([64]) \<Rightarrow> ([128])" where
"fold64 h \<equiv> 
  let
    z = (((zero`{[64]}) #`{64,64,Bit} h) : ([128]))
  in (((z ^`{[128]} (z <<`{128,Integer,Bit} (1 :: Integer))) ^`{[128]} (z <<`{128,Integer,Bit} (3 :: Integer))) ^`{[128]} (z <<`{128,Integer,Bit} (4 :: Integer)))"

cryptol_definition red128 :: "([128]) \<Rightarrow> ([64])" where
"red128 v \<equiv> 
  let
    w = ((((zero`{[64]}) #`{64,64,Bit} (drop`{64,64,Bit} v)) ^`{[128]} (fold64`{} (take`{64,64,Bit} v))) : ([128]))
  in (drop`{64,64,Bit} (w ^`{[128]} (fold64`{} (take`{64,64,Bit} w))))"

cryptol_definition mull64 :: "([64]) \<Rightarrow> (([64]) \<Rightarrow> ([2][64]))" where
"mull64  \<equiv> GF2X.clmul1"

cryptol_definition gf264 :: "([64]) \<Rightarrow> (([64]) \<Rightarrow> ([64]))" where
"gf264 a b \<equiv> 
  let
    i__p0 = ((mull64`{} a b) : ([2][64]));
    lo = ((i__p0 @`{2,[64],Integer} (0 :: Integer)) : ([64]));
    hi = ((i__p0 @`{2,[64],Integer} (1 :: Integer)) : ([64]))
  in (red128`{} (hi #`{64,64,Bit} lo))"

cryptol_definition butterfly :: "{'h} ((fin 'h) =?> (([64]) \<Rightarrow> (([2 * 'h][64]) \<Rightarrow> ([2 * 'h][64]))))" where
"butterfly a p \<equiv> 
  let
    lo = ((take`{'h,(2 * 'h) - 'h,[64]} p) : (['h][64]));
    hi = ((drop`{'h,'h,[64]} p) : (['h][64]));
    lo' = ((lo ^`{['h][64]} (seq_compr`{'h,[64],[64]} (\<lambda>(x :: [64]). (gf264`{} x a)) hi)) : (['h][64]));
    hi' = ((hi ^`{['h][64]} lo') : (['h][64]))
  in (lo' #`{'h,'h,[64]} hi')"

cryptol_definition stage :: "{'h,'k} ((fin 'h,fin 'k,'k <= (2 ^ 32)) =?> (([64]) \<Rightarrow> ((['k * (2 * 'h)][64]) \<Rightarrow> (['k * (2 * 'h)][64]))))" where
"stage s p \<equiv> join`{'k,2 * 'h,[64]} (seq_compr`{'k,(([2 * 'h][64])) \<times> (([64])),[2 * 'h][64]} (\<lambda>((u :: [2 * 'h][64]),(m :: [64])). (butterfly`{'h} (cantor`{} (((0x2 :: [64]) *`{[64]} m) ^`{[64]} s)) u)) (zip`{'k,([2 * 'h][64]),([64])} (seq_compr`{'k,[2 * 'h][64],([2 * 'h][64])} (\<lambda>(u :: [2 * 'h][64]). ((u))) (split`{'k,2 * 'h,[64]} p)) (seq_compr`{'k,[64],([64])} (\<lambda>(m :: [64]). ((m))) (fromToLessThan`{0,'k,[64]}))))"

cryptol_definition btfy10 :: "([64]) \<Rightarrow> (([1024][64]) \<Rightarrow> ([1024][64]))" where
"btfy10 scalar p \<equiv> stage`{1,512} (scalar >>`{64,Integer,Bit} (0 :: Integer)) (stage`{2,256} (scalar >>`{64,Integer,Bit} (1 :: Integer)) (stage`{4,128} (scalar >>`{64,Integer,Bit} (2 :: Integer)) (stage`{8,64} (scalar >>`{64,Integer,Bit} (3 :: Integer)) (stage`{16,32} (scalar >>`{64,Integer,Bit} (4 :: Integer)) (stage`{32,16} (scalar >>`{64,Integer,Bit} (5 :: Integer)) (stage`{64,8} (scalar >>`{64,Integer,Bit} (6 :: Integer)) (stage`{128,4} (scalar >>`{64,Integer,Bit} (7 :: Integer)) (stage`{256,2} (scalar >>`{64,Integer,Bit} (8 :: Integer)) (stage`{512,1} (scalar >>`{64,Integer,Bit} (9 :: Integer)) p)))))))))"

cryptol_definition btfy11 :: "([64]) \<Rightarrow> (([2048][64]) \<Rightarrow> ([2048][64]))" where
"btfy11 scalar p \<equiv> stage`{1,1024} (scalar >>`{64,Integer,Bit} (0 :: Integer)) (stage`{2,512} (scalar >>`{64,Integer,Bit} (1 :: Integer)) (stage`{4,256} (scalar >>`{64,Integer,Bit} (2 :: Integer)) (stage`{8,128} (scalar >>`{64,Integer,Bit} (3 :: Integer)) (stage`{16,64} (scalar >>`{64,Integer,Bit} (4 :: Integer)) (stage`{32,32} (scalar >>`{64,Integer,Bit} (5 :: Integer)) (stage`{64,16} (scalar >>`{64,Integer,Bit} (6 :: Integer)) (stage`{128,8} (scalar >>`{64,Integer,Bit} (7 :: Integer)) (stage`{256,4} (scalar >>`{64,Integer,Bit} (8 :: Integer)) (stage`{512,2} (scalar >>`{64,Integer,Bit} (9 :: Integer)) (stage`{1024,1} (scalar >>`{64,Integer,Bit} (10 :: Integer)) p))))))))))"

cryptol_definition btfy9 :: "([64]) \<Rightarrow> (([512][64]) \<Rightarrow> ([512][64]))" where
"btfy9 scalar p \<equiv> stage`{1,256} (scalar >>`{64,Integer,Bit} (0 :: Integer)) (stage`{2,128} (scalar >>`{64,Integer,Bit} (1 :: Integer)) (stage`{4,64} (scalar >>`{64,Integer,Bit} (2 :: Integer)) (stage`{8,32} (scalar >>`{64,Integer,Bit} (3 :: Integer)) (stage`{16,16} (scalar >>`{64,Integer,Bit} (4 :: Integer)) (stage`{32,8} (scalar >>`{64,Integer,Bit} (5 :: Integer)) (stage`{64,4} (scalar >>`{64,Integer,Bit} (6 :: Integer)) (stage`{128,2} (scalar >>`{64,Integer,Bit} (7 :: Integer)) (stage`{256,1} (scalar >>`{64,Integer,Bit} (8 :: Integer)) p))))))))"

cryptol_definition gf264v :: "{'n} ((fin 'n) =?> ((['n][64]) \<Rightarrow> ((['n][64]) \<Rightarrow> (['n][64]))))" where
"gf264v a b \<equiv> seq_compr`{'n,(([64])) \<times> (([64])),[64]} (\<lambda>((x :: [64]),(y :: [64])). (gf264`{} x y)) (zip`{'n,([64]),([64])} (seq_compr`{'n,[64],([64])} (\<lambda>(x :: [64]). ((x))) a) (seq_compr`{'n,[64],([64])} (\<lambda>(y :: [64]). ((y))) b))"

cryptol_definition ibutterfly :: "{'h} ((fin 'h) =?> (([64]) \<Rightarrow> (([2 * 'h][64]) \<Rightarrow> ([2 * 'h][64]))))" where
"ibutterfly a p \<equiv> 
  let
    lo = ((take`{'h,(2 * 'h) - 'h,[64]} p) : (['h][64]));
    hi = ((drop`{'h,'h,[64]} p) : (['h][64]));
    hi' = ((hi ^`{['h][64]} lo) : (['h][64]));
    lo' = ((lo ^`{['h][64]} (seq_compr`{'h,[64],[64]} (\<lambda>(x :: [64]). (gf264`{} x a)) hi')) : (['h][64]))
  in (lo' #`{'h,'h,[64]} hi')"

cryptol_definition istage :: "{'h,'k} ((fin 'h,fin 'k,'k <= (2 ^ 32)) =?> (([64]) \<Rightarrow> ((['k * (2 * 'h)][64]) \<Rightarrow> (['k * (2 * 'h)][64]))))" where
"istage s p \<equiv> join`{'k,2 * 'h,[64]} (seq_compr`{'k,(([2 * 'h][64])) \<times> (([64])),[2 * 'h][64]} (\<lambda>((u :: [2 * 'h][64]),(m :: [64])). (ibutterfly`{'h} (cantor`{} (((0x2 :: [64]) *`{[64]} m) ^`{[64]} s)) u)) (zip`{'k,([2 * 'h][64]),([64])} (seq_compr`{'k,[2 * 'h][64],([2 * 'h][64])} (\<lambda>(u :: [2 * 'h][64]). ((u))) (split`{'k,2 * 'h,[64]} p)) (seq_compr`{'k,[64],([64])} (\<lambda>(m :: [64]). ((m))) (fromToLessThan`{0,'k,[64]}))))"

cryptol_definition ibtfy10 :: "([64]) \<Rightarrow> (([1024][64]) \<Rightarrow> ([1024][64]))" where
"ibtfy10 scalar p \<equiv> istage`{512,1} (scalar >>`{64,Integer,Bit} (9 :: Integer)) (istage`{256,2} (scalar >>`{64,Integer,Bit} (8 :: Integer)) (istage`{128,4} (scalar >>`{64,Integer,Bit} (7 :: Integer)) (istage`{64,8} (scalar >>`{64,Integer,Bit} (6 :: Integer)) (istage`{32,16} (scalar >>`{64,Integer,Bit} (5 :: Integer)) (istage`{16,32} (scalar >>`{64,Integer,Bit} (4 :: Integer)) (istage`{8,64} (scalar >>`{64,Integer,Bit} (3 :: Integer)) (istage`{4,128} (scalar >>`{64,Integer,Bit} (2 :: Integer)) (istage`{2,256} (scalar >>`{64,Integer,Bit} (1 :: Integer)) (istage`{1,512} (scalar >>`{64,Integer,Bit} (0 :: Integer)) p)))))))))"

cryptol_definition ibtfy11 :: "([64]) \<Rightarrow> (([2048][64]) \<Rightarrow> ([2048][64]))" where
"ibtfy11 scalar p \<equiv> istage`{1024,1} (scalar >>`{64,Integer,Bit} (10 :: Integer)) (istage`{512,2} (scalar >>`{64,Integer,Bit} (9 :: Integer)) (istage`{256,4} (scalar >>`{64,Integer,Bit} (8 :: Integer)) (istage`{128,8} (scalar >>`{64,Integer,Bit} (7 :: Integer)) (istage`{64,16} (scalar >>`{64,Integer,Bit} (6 :: Integer)) (istage`{32,32} (scalar >>`{64,Integer,Bit} (5 :: Integer)) (istage`{16,64} (scalar >>`{64,Integer,Bit} (4 :: Integer)) (istage`{8,128} (scalar >>`{64,Integer,Bit} (3 :: Integer)) (istage`{4,256} (scalar >>`{64,Integer,Bit} (2 :: Integer)) (istage`{2,512} (scalar >>`{64,Integer,Bit} (1 :: Integer)) (istage`{1,1024} (scalar >>`{64,Integer,Bit} (0 :: Integer)) p))))))))))"

cryptol_definition ibtfy9 :: "([64]) \<Rightarrow> (([512][64]) \<Rightarrow> ([512][64]))" where
"ibtfy9 scalar p \<equiv> istage`{256,1} (scalar >>`{64,Integer,Bit} (8 :: Integer)) (istage`{128,2} (scalar >>`{64,Integer,Bit} (7 :: Integer)) (istage`{64,4} (scalar >>`{64,Integer,Bit} (6 :: Integer)) (istage`{32,8} (scalar >>`{64,Integer,Bit} (5 :: Integer)) (istage`{16,16} (scalar >>`{64,Integer,Bit} (4 :: Integer)) (istage`{8,32} (scalar >>`{64,Integer,Bit} (3 :: Integer)) (istage`{4,64} (scalar >>`{64,Integer,Bit} (2 :: Integer)) (istage`{2,128} (scalar >>`{64,Integer,Bit} (1 :: Integer)) (istage`{1,256} (scalar >>`{64,Integer,Bit} (0 :: Integer)) p))))))))"

cryptol_definition km1 :: "([1][64]) \<Rightarrow> (([1][64]) \<Rightarrow> ([2][64]))" where
"km1 a b \<equiv> mull64`{} (a @`{1,[64],Integer} (0 :: Integer)) (b @`{1,[64],Integer} (0 :: Integer))"

cryptol_definition km2 :: "([2][64]) \<Rightarrow> (([2][64]) \<Rightarrow> ([4][64]))" where
"km2  \<equiv> GF2X.kstep`{1,1} km1 km1"

cryptol_definition km4 :: "([4][64]) \<Rightarrow> (([4][64]) \<Rightarrow> ([8][64]))" where
"km4  \<equiv> GF2X.kstep`{2,2} km2 km2"

cryptol_definition km8 :: "([8][64]) \<Rightarrow> (([8][64]) \<Rightarrow> ([16][64]))" where
"km8  \<equiv> GF2X.kstep`{4,4} km4 km4"

cryptol_definition km16 :: "([16][64]) \<Rightarrow> (([16][64]) \<Rightarrow> ([32][64]))" where
"km16  \<equiv> GF2X.kstep`{8,8} km8 km8"

cryptol_definition km24 :: "([24][64]) \<Rightarrow> (([24][64]) \<Rightarrow> ([48][64]))" where
"km24  \<equiv> AVXK.k3step`{8} km8"

cryptol_definition km32 :: "([32][64]) \<Rightarrow> (([32][64]) \<Rightarrow> ([64][64]))" where
"km32  \<equiv> GF2X.kstep`{16,16} km16 km16"

cryptol_definition km64 :: "([64][64]) \<Rightarrow> (([64][64]) \<Rightarrow> ([128][64]))" where
"km64  \<equiv> GF2X.kstep`{32,32} km32 km32"

end
end
