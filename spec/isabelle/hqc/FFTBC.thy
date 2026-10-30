theory "FFTBC"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition divBlock :: "{'L,'T} ((fin 'L,fin 'T,'L \<ge> 1,(2 * 'T) <= 'L) =?> (([2 * 'L]) \<Rightarrow> ([2 * 'L])))" where
"divBlock f \<equiv> 
  let
    hi = ((take`{'L,(2 * 'L) - 'L,Bit} f) : (['L]));
    lo = ((drop`{'L,'L,Bit} f) : (['L]));
    q = ((hi ^`{['L]} (hi >>`{'L,Integer,Bit} (number`{'L - 'T,Integer}))) : (['L]));
    r = ((lo ^`{['L]} (q <<`{'L,Integer,Bit} (number`{'T,Integer}))) : (['L]))
  in (q #`{'L,'L,Bit} r)"

cryptol_definition divLayer :: "{'k,'L,'T} ((fin 'k,fin 'L,fin 'T,'L \<ge> 1,(2 * 'T) <= 'L) =?> ((['k * (2 * 'L)]) \<Rightarrow> (['k * (2 * 'L)])))" where
"divLayer v \<equiv> join`{'k,2 * 'L,Bit} (seq_compr`{'k,[2 * 'L],[2 * 'L]} (\<lambda>(b :: [2 * 'L]). (divBlock`{'L,'T} b)) (split`{'k,2 * 'L,Bit} v))"

cryptol_definition repr16384 :: "([16384]) \<Rightarrow> ([16384])" where
"repr16384 v \<equiv> divLayer`{32,256,1} (divLayer`{16,512,2} (divLayer`{8,1024,4} (divLayer`{4,2048,8} (divLayer`{2,4096,16} (divLayer`{1,8192,32} v)))))"

cryptol_definition bc256of16384 :: "([16384]) \<Rightarrow> ([16384])" where
"bc256of16384 v \<equiv> divLayer`{16,512,256} (divLayer`{4,2048,1024} (divLayer`{8,1024,256} (divLayer`{4,2048,512} (divLayer`{1,8192,4096} (divLayer`{2,4096,256} (divLayer`{1,8192,512} v))))))"

cryptol_definition bc1of256 :: "{'k} ((fin 'k) =?> (([256 * 'k]) \<Rightarrow> ([256 * 'k])))" where
"bc1of256 v \<equiv> divLayer`{64 * 'k,2,1} (divLayer`{16 * 'k,8,4} (divLayer`{32 * 'k,4,1} (divLayer`{16 * 'k,8,2} (divLayer`{4 * 'k,32,16} (divLayer`{'k,128,64} (divLayer`{2 * 'k,64,16} (divLayer`{'k,128,32} (divLayer`{8 * 'k,16,1} (divLayer`{4 * 'k,32,2} (divLayer`{2 * 'k,64,4} (divLayer`{'k,128,8} v)))))))))))"

cryptol_definition bc1 :: "([16384]) \<Rightarrow> ([16384])" where
"bc1 v \<equiv> bc1of256`{64} (bc256of16384`{} (repr16384`{} v))"

cryptol_definition repr131072 :: "([131072]) \<Rightarrow> ([131072])" where
"repr131072 v \<equiv> divLayer`{256,256,1} (divLayer`{128,512,2} (divLayer`{64,1024,4} (divLayer`{32,2048,8} (divLayer`{16,4096,16} (divLayer`{8,8192,32} (divLayer`{4,16384,64} (divLayer`{2,32768,128} (divLayer`{1,65536,256} v))))))))"

cryptol_definition cvt131072 :: "([131072]) \<Rightarrow> ([131072])" where
"cvt131072 v \<equiv> divLayer`{2,32768,16384} (divLayer`{8,8192,4096} (divLayer`{4,16384,4096} (divLayer`{2,32768,8192} (divLayer`{32,2048,1024} (divLayer`{128,512,256} (divLayer`{64,1024,256} (divLayer`{32,2048,512} (divLayer`{16,4096,256} (divLayer`{8,8192,512} (divLayer`{4,16384,1024} (divLayer`{2,32768,2048} (divLayer`{1,65536,256} v))))))))))))"

cryptol_definition bc1_131072 :: "([131072]) \<Rightarrow> ([131072])" where
"bc1_131072 v \<equiv> cvt131072`{} (bc1of256`{512} (repr131072`{} v))"

cryptol_definition flat32 :: "{'n} ((fin 'n) =?> ((['n][32]) \<Rightarrow> ([32 * 'n])))" where
"flat32 v \<equiv> join`{'n,32,Bit} (reverse`{'n,[32]} v)"

cryptol_definition unflat32 :: "{'n} ((fin 'n) =?> (([32 * 'n]) \<Rightarrow> (['n][32])))" where
"unflat32 v \<equiv> reverse`{'n,[32]} (split`{'n,32,Bit} v)"

cryptol_definition bc1_131072w :: "([4096][32]) \<Rightarrow> ([4096][32])" where
"bc1_131072w v \<equiv> unflat32`{4096} (bc1_131072`{} (flat32`{4096} v))"

cryptol_definition repr32768 :: "([32768]) \<Rightarrow> ([32768])" where
"repr32768 v \<equiv> divLayer`{64,256,1} (divLayer`{32,512,2} (divLayer`{16,1024,4} (divLayer`{8,2048,8} (divLayer`{4,4096,16} (divLayer`{2,8192,32} (divLayer`{1,16384,64} v))))))"

cryptol_definition bc256of32768 :: "([32768]) \<Rightarrow> ([32768])" where
"bc256of32768 v \<equiv> divLayer`{32,512,256} (divLayer`{8,2048,1024} (divLayer`{16,1024,256} (divLayer`{8,2048,512} (divLayer`{2,8192,4096} (divLayer`{1,16384,4096} (divLayer`{4,4096,256} (divLayer`{2,8192,512} (divLayer`{1,16384,1024} v))))))))"

cryptol_definition bc1_32768 :: "([32768]) \<Rightarrow> ([32768])" where
"bc1_32768 v \<equiv> bc1of256`{128} (bc256of32768`{} (repr32768`{} v))"

cryptol_definition bc1_32768w :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"bc1_32768w v \<equiv> unflat32`{1024} (bc1_32768`{} (flat32`{1024} v))"

cryptol_definition repr32W :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"repr32W v \<equiv> unflat32`{1024} (repr32768`{} (flat32`{1024} v))"

cryptol_definition bc256of32W :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"bc256of32W v \<equiv> unflat32`{1024} (bc256of32768`{} (flat32`{1024} v))"

cryptol_definition bc1of256of32W :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"bc1of256of32W v \<equiv> unflat32`{1024} (bc1of256`{128} (flat32`{1024} v))"

cryptol_definition bc1_32768wc :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"bc1_32768wc v \<equiv> bc1of256of32W`{} (bc256of32W`{} (repr32W`{} v))"

cryptol_definition repr65536 :: "([65536]) \<Rightarrow> ([65536])" where
"repr65536 v \<equiv> divLayer`{128,256,1} (divLayer`{64,512,2} (divLayer`{32,1024,4} (divLayer`{16,2048,8} (divLayer`{8,4096,16} (divLayer`{4,8192,32} (divLayer`{2,16384,64} (divLayer`{1,32768,128} v)))))))"

cryptol_definition bc256of65536 :: "([65536]) \<Rightarrow> ([65536])" where
"bc256of65536 v \<equiv> divLayer`{64,512,256} (divLayer`{16,2048,1024} (divLayer`{32,1024,256} (divLayer`{16,2048,512} (divLayer`{4,8192,4096} (divLayer`{1,32768,16384} (divLayer`{2,16384,4096} (divLayer`{1,32768,8192} (divLayer`{8,4096,256} (divLayer`{4,8192,512} (divLayer`{2,16384,1024} (divLayer`{1,32768,2048} v)))))))))))"

cryptol_definition bc1_65536 :: "([65536]) \<Rightarrow> ([65536])" where
"bc1_65536 v \<equiv> bc1of256`{256} (bc256of65536`{} (repr65536`{} v))"

cryptol_definition bc1_65536w :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"bc1_65536w v \<equiv> unflat32`{2048} (bc1_65536`{} (flat32`{2048} v))"

cryptol_definition repr64W :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"repr64W v \<equiv> unflat32`{2048} (repr65536`{} (flat32`{2048} v))"

cryptol_definition bc256of64W :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"bc256of64W v \<equiv> unflat32`{2048} (bc256of65536`{} (flat32`{2048} v))"

cryptol_definition bc1of256of64W :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"bc1of256of64W v \<equiv> unflat32`{2048} (bc1of256`{256} (flat32`{2048} v))"

cryptol_definition bc1_65536wc :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"bc1_65536wc v \<equiv> bc1of256of64W`{} (bc256of64W`{} (repr64W`{} v))"

cryptol_definition bc1of256W :: "([512][32]) \<Rightarrow> ([512][32])" where
"bc1of256W v \<equiv> unflat32`{512} (bc1of256`{64} (flat32`{512} v))"

cryptol_definition reprW :: "([512][32]) \<Rightarrow> ([512][32])" where
"reprW v \<equiv> unflat32`{512} (repr16384`{} (flat32`{512} v))"

cryptol_definition bc256W :: "([512][32]) \<Rightarrow> ([512][32])" where
"bc256W v \<equiv> unflat32`{512} (bc256of16384`{} (flat32`{512} v))"

cryptol_definition bc1w :: "([512][32]) \<Rightarrow> ([512][32])" where
"bc1w v \<equiv> bc1of256W`{} (bc256W`{} (reprW`{} v))"

cryptol_definition bc1w_is_bc1 :: "([512][32]) \<Rightarrow> Bit" where
"bc1w_is_bc1 v \<equiv> (bc1w`{} v) ==`{[512][32]} (unflat32`{512} (bc1`{} (flat32`{512} v)))"

cryptol_definition mulBlock :: "{'L,'T} ((fin 'L,fin 'T,'L \<ge> 1,(2 * 'T) <= 'L) =?> (([2 * 'L]) \<Rightarrow> ([2 * 'L])))" where
"mulBlock b \<equiv> 
  let
    q = ((take`{'L,(2 * 'L) - 'L,Bit} b) : (['L]));
    r = ((drop`{'L,(2 * 'L) - 'L,Bit} b) : ([(2 * 'L) - 'L]))
  in (((q #`{'L,'L,Bit} (zero`{['L]})) ^`{[2 * 'L]} (((zero`{['L]}) #`{'L,'L,Bit} q) <<`{2 * 'L,Integer,Bit} (number`{'T,Integer}))) ^`{[2 * 'L]} ((zero`{['L]}) #`{'L,(2 * 'L) - 'L,Bit} r))"

cryptol_definition mulLayer :: "{'k,'L,'T} ((fin 'k,fin 'L,fin 'T,'L \<ge> 1,(2 * 'T) <= 'L) =?> ((['k * (2 * 'L)]) \<Rightarrow> (['k * (2 * 'L)])))" where
"mulLayer v \<equiv> join`{'k,2 * 'L,Bit} (seq_compr`{'k,[2 * 'L],[2 * 'L]} (\<lambda>(b :: [2 * 'L]). (mulBlock`{'L,'T} b)) (split`{'k,2 * 'L,Bit} v))"

cryptol_definition ibc1of256 :: "{'k} ((fin 'k) =?> (([256 * 'k]) \<Rightarrow> ([256 * 'k])))" where
"ibc1of256 v \<equiv> mulLayer`{'k,128,8} (mulLayer`{2 * 'k,64,4} (mulLayer`{4 * 'k,32,2} (mulLayer`{8 * 'k,16,1} (mulLayer`{'k,128,32} (mulLayer`{2 * 'k,64,16} (mulLayer`{'k,128,64} (mulLayer`{4 * 'k,32,16} (mulLayer`{16 * 'k,8,2} (mulLayer`{32 * 'k,4,1} (mulLayer`{16 * 'k,8,4} (mulLayer`{64 * 'k,2,1} v)))))))))))"

cryptol_definition ibc256of16384 :: "([16384]) \<Rightarrow> ([16384])" where
"ibc256of16384 v \<equiv> mulLayer`{1,8192,512} (mulLayer`{2,4096,256} (mulLayer`{1,8192,4096} (mulLayer`{4,2048,512} (mulLayer`{8,1024,256} (mulLayer`{4,2048,1024} (mulLayer`{16,512,256} v))))))"

cryptol_definition irepr16384 :: "([16384]) \<Rightarrow> ([16384])" where
"irepr16384 v \<equiv> mulLayer`{1,8192,32} (mulLayer`{2,4096,16} (mulLayer`{4,2048,8} (mulLayer`{8,1024,4} (mulLayer`{16,512,2} (mulLayer`{32,256,1} v)))))"

cryptol_definition ibc1 :: "([16384]) \<Rightarrow> ([16384])" where
"ibc1 v \<equiv> irepr16384`{} (ibc256of16384`{} (ibc1of256`{64} v))"

cryptol_definition icvt131072 :: "([131072]) \<Rightarrow> ([131072])" where
"icvt131072 v \<equiv> mulLayer`{1,65536,256} (mulLayer`{2,32768,2048} (mulLayer`{4,16384,1024} (mulLayer`{8,8192,512} (mulLayer`{16,4096,256} (mulLayer`{32,2048,512} (mulLayer`{64,1024,256} (mulLayer`{128,512,256} (mulLayer`{32,2048,1024} (mulLayer`{2,32768,8192} (mulLayer`{4,16384,4096} (mulLayer`{8,8192,4096} (mulLayer`{2,32768,16384} v))))))))))))"

cryptol_definition irepr131072 :: "([131072]) \<Rightarrow> ([131072])" where
"irepr131072 v \<equiv> mulLayer`{1,65536,256} (mulLayer`{2,32768,128} (mulLayer`{4,16384,64} (mulLayer`{8,8192,32} (mulLayer`{16,4096,16} (mulLayer`{32,2048,8} (mulLayer`{64,1024,4} (mulLayer`{128,512,2} (mulLayer`{256,256,1} v))))))))"

cryptol_definition ibc1_131072 :: "([131072]) \<Rightarrow> ([131072])" where
"ibc1_131072 v \<equiv> irepr131072`{} (ibc1of256`{512} (icvt131072`{} v))"

cryptol_definition icvt128W :: "([4096][32]) \<Rightarrow> ([4096][32])" where
"icvt128W v \<equiv> unflat32`{4096} (icvt131072`{} (flat32`{4096} v))"

cryptol_definition ibc1of256of128W :: "([4096][32]) \<Rightarrow> ([4096][32])" where
"ibc1of256of128W v \<equiv> unflat32`{4096} (ibc1of256`{512} (flat32`{4096} v))"

cryptol_definition irepr128W :: "([4096][32]) \<Rightarrow> ([4096][32])" where
"irepr128W v \<equiv> unflat32`{4096} (irepr131072`{} (flat32`{4096} v))"

cryptol_definition ibc1_131072w :: "([4096][32]) \<Rightarrow> ([4096][32])" where
"ibc1_131072w v \<equiv> irepr128W`{} (ibc1of256of128W`{} (icvt128W`{} v))"

cryptol_definition ibc256of32768 :: "([32768]) \<Rightarrow> ([32768])" where
"ibc256of32768 v \<equiv> mulLayer`{1,16384,1024} (mulLayer`{2,8192,512} (mulLayer`{4,4096,256} (mulLayer`{1,16384,4096} (mulLayer`{2,8192,4096} (mulLayer`{8,2048,512} (mulLayer`{16,1024,256} (mulLayer`{8,2048,1024} (mulLayer`{32,512,256} v))))))))"

cryptol_definition irepr32768 :: "([32768]) \<Rightarrow> ([32768])" where
"irepr32768 v \<equiv> mulLayer`{1,16384,64} (mulLayer`{2,8192,32} (mulLayer`{4,4096,16} (mulLayer`{8,2048,8} (mulLayer`{16,1024,4} (mulLayer`{32,512,2} (mulLayer`{64,256,1} v))))))"

cryptol_definition ibc1_32768 :: "([32768]) \<Rightarrow> ([32768])" where
"ibc1_32768 v \<equiv> irepr32768`{} (ibc256of32768`{} (ibc1of256`{128} v))"

cryptol_definition ibc1of256of32W :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"ibc1of256of32W v \<equiv> unflat32`{1024} (ibc1of256`{128} (flat32`{1024} v))"

cryptol_definition ibc256of32W :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"ibc256of32W v \<equiv> unflat32`{1024} (ibc256of32768`{} (flat32`{1024} v))"

cryptol_definition irepr32W :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"irepr32W v \<equiv> unflat32`{1024} (irepr32768`{} (flat32`{1024} v))"

cryptol_definition ibc1_32768w :: "([1024][32]) \<Rightarrow> ([1024][32])" where
"ibc1_32768w v \<equiv> irepr32W`{} (ibc256of32W`{} (ibc1of256of32W`{} v))"

cryptol_definition ibc256of65536 :: "([65536]) \<Rightarrow> ([65536])" where
"ibc256of65536 v \<equiv> mulLayer`{1,32768,2048} (mulLayer`{2,16384,1024} (mulLayer`{4,8192,512} (mulLayer`{8,4096,256} (mulLayer`{1,32768,8192} (mulLayer`{2,16384,4096} (mulLayer`{1,32768,16384} (mulLayer`{4,8192,4096} (mulLayer`{16,2048,512} (mulLayer`{32,1024,256} (mulLayer`{16,2048,1024} (mulLayer`{64,512,256} v)))))))))))"

cryptol_definition irepr65536 :: "([65536]) \<Rightarrow> ([65536])" where
"irepr65536 v \<equiv> mulLayer`{1,32768,128} (mulLayer`{2,16384,64} (mulLayer`{4,8192,32} (mulLayer`{8,4096,16} (mulLayer`{16,2048,8} (mulLayer`{32,1024,4} (mulLayer`{64,512,2} (mulLayer`{128,256,1} v)))))))"

cryptol_definition ibc1_65536 :: "([65536]) \<Rightarrow> ([65536])" where
"ibc1_65536 v \<equiv> irepr65536`{} (ibc256of65536`{} (ibc1of256`{256} v))"

cryptol_definition ibc1of256of64W :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"ibc1of256of64W v \<equiv> unflat32`{2048} (ibc1of256`{256} (flat32`{2048} v))"

cryptol_definition ibc256of64W :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"ibc256of64W v \<equiv> unflat32`{2048} (ibc256of65536`{} (flat32`{2048} v))"

cryptol_definition irepr64W :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"irepr64W v \<equiv> unflat32`{2048} (irepr65536`{} (flat32`{2048} v))"

cryptol_definition ibc1_65536w :: "([2048][32]) \<Rightarrow> ([2048][32])" where
"ibc1_65536w v \<equiv> irepr64W`{} (ibc256of64W`{} (ibc1of256of64W`{} v))"

cryptol_definition ibc1of256W :: "([512][32]) \<Rightarrow> ([512][32])" where
"ibc1of256W v \<equiv> unflat32`{512} (ibc1of256`{64} (flat32`{512} v))"

cryptol_definition ibc256W :: "([512][32]) \<Rightarrow> ([512][32])" where
"ibc256W v \<equiv> unflat32`{512} (ibc256of16384`{} (flat32`{512} v))"

cryptol_definition ireprW :: "([512][32]) \<Rightarrow> ([512][32])" where
"ireprW v \<equiv> unflat32`{512} (irepr16384`{} (flat32`{512} v))"

cryptol_definition ibc1w :: "([512][32]) \<Rightarrow> ([512][32])" where
"ibc1w v \<equiv> ireprW`{} (ibc256W`{} (ibc1of256W`{} v))"

cryptol_definition layer_inverse_small :: "([64]) \<Rightarrow> Bit" where
"layer_inverse_small v \<equiv> (mulLayer`{2,16,1} (divLayer`{2,16,1} v)) ==`{[64]} v"

end
end
