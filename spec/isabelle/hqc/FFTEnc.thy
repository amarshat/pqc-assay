theory "FFTEnc"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition byteOf :: "([64]) \<Rightarrow> (([3]) \<Rightarrow> ([8]))" where
"byteOf w k \<equiv> (reverse`{8,[8]} (split`{8,8,Bit} w)) @`{8,[8],[3]} k"

cryptol_definition transpose8 :: "([8][8]) \<Rightarrow> ([8][8])" where
"transpose8 m \<equiv> seq_compr`{8,[3],[8]} (\<lambda>(j :: [3]). (seq_compr`{8,[3],Bit} (\<lambda>(c :: [3]). ((m @`{8,[8],[3]} c) !`{8,Bit,[3]} j)) (fromThenTo`{7,6,0,[3],8}))) (fromTo`{0,7,[3]})"

cryptol_definition decMat :: "[64][64]" where
"decMat  \<equiv> list_to_seq [0x1 :: [64],0x8961b8a7841bfc6 :: [64],0xfd56dc6306e45ec6 :: [64],0x77332469d0404105 :: [64],0xd110eb4a970feaf5 :: [64],0x9c94931de38226fe :: [64],0x52bf8c5ba0978896 :: [64],0xbce2b823bebf0166 :: [64],0x7af3356b5d818e41 :: [64],0x1e7b94c935b698d0 :: [64],0xbcb73d9aabdd6ddf :: [64],0x5f75970481f366a8 :: [64],0xb33f7074d9b6e3fe :: [64],0x2adb64d29a93ef96 :: [64],0x59dab92a69394e60 :: [64],0x3c8004790328459c :: [64],0xadcb0001cdaa3d05 :: [64],0x9bb38fd76d5e0c0b :: [64],0xabcadd426cb54b4d :: [64],0xf042a8f93e8a48b9 :: [64],0x47b25aab146986f6 :: [64],0xe750955be42931a1 :: [64],0x9bf1d4a1535a0d17 :: [64],0x91564f9a406d933c :: [64],0xded3254b42d33aaa :: [64],0xbd1f32c59e84e45d :: [64],0xfa018660e3165396 :: [64],0xa2f911a00f5baa7b :: [64],0xe958695bc8926acd :: [64],0xc8c10606a8ec8d6b :: [64],0x8e6cfef54b2e9ac6 :: [64],0x88007d210e507cf4 :: [64],0x17a89b9796a48397 :: [64],0x1bdd636a99f218be :: [64],0x7cb821d83481a449 :: [64],0xff39584957728d46 :: [64],0x9cd7c0f7b4d02de7 :: [64],0x779fca946b676edb :: [64],0x5235a7728b715838 :: [64],0x70ef0482c08984a5 :: [64],0xbb1c3dbfe2b5150b :: [64],0xee767356051fe0e1 :: [64],0x1b5c98d75cc93fe8 :: [64],0x4c25ee1fb1c8ceb6 :: [64],0xb7310079067f9e51 :: [64],0x4be2a5ae359e2594 :: [64],0xfe86864026631c3 :: [64],0x5b4cd59958434683 :: [64],0xe550b2539a848707 :: [64],0x6e50d13b6a7a5997 :: [64],0x7fd8fb00a5aef99a :: [64],0xcdbd262ac16e806b :: [64],0xc021427b4f7646e0 :: [64],0xd7f262605a9bcdd0 :: [64],0xb046630a7efeddc :: [64],0xa869f3dfcbe24fab :: [64],0xa00150323be9b1de :: [64],0x1294d8724ae3d0d :: [64],0x4ab517f07f03a4b1 :: [64],0xfdc5af3bb370e266 :: [64],0x2aff63efa8285238 :: [64],0xfba0ace42227357a :: [64],0xc208107e1c3e5ac1 :: [64],0xb2dbb5cb68d0dc74 :: [64]] :: [64][64]"

cryptol_definition linmap :: "{'n} ((fin 'n,'n <= 64) =?> (([64][64]) \<Rightarrow> ((['n]) \<Rightarrow> ([64]))))" where
"linmap mat v \<equiv> foldl`{'n,[64],[64]} (\<lblot>^`{[64]}\<rblot>) (0x0 :: [64]) (seq_compr`{'n,Integer,[64]} (\<lambda>(j :: Integer). (if v !`{'n,Bit,Integer} j then (mat @`{64,[64],Integer} j) else coerce (0x0 :: [64]))) (fromToLessThan`{0,'n,Integer}))"

cryptol_definition decBatch3 :: "([1024][64]) \<Rightarrow> (([7]) \<Rightarrow> ([8][8][8]))" where
"decBatch3 x i \<equiv> 
  let
    rr = ((seq_compr`{8,[64],[64]} (\<lambda>(e :: [64]). (linmap`{64} decMat e)) ((split`{128,8,[64]} x) @`{128,[8][64],[7]} i)) : ([8][64]))
  in (seq_compr`{8,[3],[8][8]} (\<lambda>(kb :: [3]). (transpose8`{} (seq_compr`{8,[64],[8]} (\<lambda>(r :: [64]). (byteOf`{} r kb)) rr))) (fromTo`{0,7,[3]}))"

cryptol_definition dbytes3 :: "([1024][64]) \<Rightarrow> (([7]) \<Rightarrow> (([6]) \<Rightarrow> ([32][8])))" where
"dbytes3 x i0 t \<equiv> seq_compr`{32,[7],[8]} (\<lambda>(i :: [7]). (((decBatch3`{} x i) @`{8,[8][8],[6]} (t >>`{6,Integer,Bit} (3 :: Integer))) @`{8,[8],[3]} (drop`{3,3,Bit} t))) (seq_compr`{32,[7],[7]} (\<lambda>(k :: [7]). (i0 +`{[7]} k)) (fromTo`{0,31,[7]}))"

cryptol_definition asm3 :: "([1024][64]) \<Rightarrow> ([1024][64])" where
"asm3 x \<equiv> 
  let
    ob = ((seq_compr`{8192,[13],[8]} (\<lambda>(b :: [13]). ((dbytes3`{} x ((drop`{6,7,Bit} b) &&`{[7]} (0x60 :: [7])) (take`{6,7,Bit} b)) @`{32,[8],[7]} ((drop`{6,7,Bit} b) &&`{[7]} (0x1f :: [7])))) (fromToLessThan`{0,8192,[13]})) : ([8192][8]))
  in (reverse`{1024,[64]} (split`{1024,64,Bit} (join`{8192,8,Bit} (reverse`{8192,[8]} ob))))"

cryptol_definition decBatch5 :: "([2048][64]) \<Rightarrow> (([8]) \<Rightarrow> ([8][8][8]))" where
"decBatch5 x i \<equiv> 
  let
    rr = ((seq_compr`{8,[64],[64]} (\<lambda>(e :: [64]). (linmap`{64} decMat e)) ((split`{256,8,[64]} x) @`{256,[8][64],[8]} i)) : ([8][64]))
  in (seq_compr`{8,[3],[8][8]} (\<lambda>(kb :: [3]). (transpose8`{} (seq_compr`{8,[64],[8]} (\<lambda>(r :: [64]). (byteOf`{} r kb)) rr))) (fromTo`{0,7,[3]}))"

cryptol_definition dbytes5 :: "([2048][64]) \<Rightarrow> (([8]) \<Rightarrow> (([6]) \<Rightarrow> ([32][8])))" where
"dbytes5 x i0 t \<equiv> seq_compr`{32,[8],[8]} (\<lambda>(i :: [8]). (((decBatch5`{} x i) @`{8,[8][8],[6]} (t >>`{6,Integer,Bit} (3 :: Integer))) @`{8,[8],[3]} (drop`{3,3,Bit} t))) (seq_compr`{32,[8],[8]} (\<lambda>(k :: [8]). (i0 +`{[8]} k)) (fromTo`{0,31,[8]}))"

cryptol_definition asm5 :: "([2048][64]) \<Rightarrow> ([2048][64])" where
"asm5 x \<equiv> 
  let
    ob = ((seq_compr`{16384,[14],[8]} (\<lambda>(b :: [14]). ((dbytes5`{} x ((drop`{6,8,Bit} b) &&`{[8]} (0xe0 :: [8])) (take`{6,8,Bit} b)) @`{32,[8],[8]} ((drop`{6,8,Bit} b) &&`{[8]} (0x1f :: [8])))) (fromToLessThan`{0,16384,[14]})) : ([16384][8]))
  in (reverse`{2048,[64]} (split`{2048,64,Bit} (join`{16384,8,Bit} (reverse`{16384,[8]} ob))))"

cryptol_definition collect128 :: "([512][64]) \<Rightarrow> (([13]) \<Rightarrow> ([32][8]))" where
"collect128 fx i \<equiv> seq_concat_map`{1,[13],32,[8]} (\<lambda>(j :: [13]). (seq_compr`{1,[13],[8]} (\<lambda>(q :: [13]). (byteOf`{} (fx @`{512,[64],[13]} (q >>`{13,Integer,Bit} (3 :: Integer))) (drop`{10,3,Bit} q))) (list_to_seq [((j *`{[13]} (0x80 :: [13])) +`{[13]} i) : ([13])] :: [1][13]))) (fromToLessThan`{0,32,[13]})"

cryptol_definition collect256 :: "([1024][64]) \<Rightarrow> (([14]) \<Rightarrow> ([32][8]))" where
"collect256 fx i \<equiv> seq_concat_map`{1,[14],32,[8]} (\<lambda>(j :: [14]). (seq_compr`{1,[14],[8]} (\<lambda>(q :: [14]). (byteOf`{} (fx @`{1024,[64],[14]} (q >>`{14,Integer,Bit} (3 :: Integer))) (drop`{11,3,Bit} q))) (list_to_seq [((j *`{[14]} (0x100 :: [14])) +`{[14]} i) : ([14])] :: [1][14]))) (fromToLessThan`{0,32,[14]})"

cryptol_definition collect64 :: "([256][64]) \<Rightarrow> (([12]) \<Rightarrow> ([32][8]))" where
"collect64 fx i \<equiv> seq_concat_map`{1,[12],32,[8]} (\<lambda>(j :: [12]). (seq_compr`{1,[12],[8]} (\<lambda>(q :: [12]). (byteOf`{} (fx @`{256,[64],[12]} (q >>`{12,Integer,Bit} (3 :: Integer))) (drop`{9,3,Bit} q))) (list_to_seq [((j *`{[12]} (0x40 :: [12])) +`{[12]} i) : ([12])] :: [1][12]))) (fromToLessThan`{0,32,[12]})"

cryptol_definition unflat23 :: "([65536]) \<Rightarrow> ([1024][64])" where
"unflat23 v \<equiv> reverse`{1024,[64]} (split`{1024,64,Bit} v)"

cryptol_definition decode3 :: "([1024][64]) \<Rightarrow> ([1024][64])" where
"decode3 fx \<equiv> 
  let
    rows = ((seq_compr`{128,[8][64],[8][64]} (\<lambda>(blk :: [8][64]). (seq_compr`{8,[64],[64]} (\<lambda>(x :: [64]). (linmap`{64} decMat x)) blk)) (split`{128,8,[64]} fx)) : ([128][8][64]));
    outByte = ((\<lambda>(q :: [13]). (
    let
      i = ((drop`{6,7,Bit} q) : ([7]));
      t = ((take`{6,7,Bit} q) : ([6]));
      k = ((take`{3,3,Bit} t) : ([3]));
      j = ((drop`{3,3,Bit} t) : ([3]));
      rr = ((rows @`{128,[8][64],[7]} i) : ([8][64]))
    in ((transpose8`{} (seq_compr`{8,[64],[8]} (\<lambda>(r :: [64]). (byteOf`{} r k)) rr)) @`{8,[8],[3]} j))) : (([13]) \<Rightarrow> ([8])))
  in (unflat23`{} (join`{8192,8,Bit} (reverse`{8192,[8]} (seq_compr`{8192,[13],[8]} (\<lambda>(q :: [13]). (outByte`{} q)) (fromToLessThan`{0,8192,[13]})))))"

cryptol_definition dbytes3_cover :: "([1024][64]) \<Rightarrow> Bit" where
"dbytes3_cover x \<equiv> 
  let
    obytes = ((reverse`{8192,[8]} (split`{8192,8,Bit} (join`{1024,64,Bit} (reverse`{1024,[64]} (decode3`{} x))))) : ([8192][8]))
  in (and`{256} (seq_concat_map`{64,[7],4,Bit} (\<lambda>(i0 :: [7]). (seq_compr`{64,[6],Bit} (\<lambda>(t :: [6]). ((dbytes3`{} x i0 t) ==`{[32][8]} (seq_compr`{32,[13],[8]} (\<lambda>(j :: [13]). (obytes @`{8192,[8],[13]} (((zext`{13,7} i0) +`{[13]} ((0x80 :: [13]) *`{[13]} (zext`{13,6} t))) +`{[13]} j))) (fromToLessThan`{0,32,[13]})))) (fromTo`{0,63,[6]}))) (fromThenTo`{0,32,96,[7],4})))"

cryptol_definition unflat25 :: "([131072]) \<Rightarrow> ([2048][64])" where
"unflat25 v \<equiv> reverse`{2048,[64]} (split`{2048,64,Bit} v)"

cryptol_definition decode5 :: "([2048][64]) \<Rightarrow> ([2048][64])" where
"decode5 fx \<equiv> 
  let
    rows = ((seq_compr`{256,[8][64],[8][64]} (\<lambda>(blk :: [8][64]). (seq_compr`{8,[64],[64]} (\<lambda>(x :: [64]). (linmap`{64} decMat x)) blk)) (split`{256,8,[64]} fx)) : ([256][8][64]));
    outByte = ((\<lambda>(q :: [14]). (
    let
      i = ((drop`{6,8,Bit} q) : ([8]));
      t = ((take`{6,8,Bit} q) : ([6]));
      k = ((take`{3,3,Bit} t) : ([3]));
      j = ((drop`{3,3,Bit} t) : ([3]));
      rr = ((rows @`{256,[8][64],[8]} i) : ([8][64]))
    in ((transpose8`{} (seq_compr`{8,[64],[8]} (\<lambda>(r :: [64]). (byteOf`{} r k)) rr)) @`{8,[8],[3]} j))) : (([14]) \<Rightarrow> ([8])))
  in (unflat25`{} (join`{16384,8,Bit} (reverse`{16384,[8]} (seq_compr`{16384,[14],[8]} (\<lambda>(q :: [14]). (outByte`{} q)) (fromToLessThan`{0,16384,[14]})))))"

cryptol_definition dbytes5_cover :: "([2048][64]) \<Rightarrow> Bit" where
"dbytes5_cover x \<equiv> 
  let
    obytes = ((reverse`{16384,[8]} (split`{16384,8,Bit} (join`{2048,64,Bit} (reverse`{2048,[64]} (decode5`{} x))))) : ([16384][8]))
  in (and`{512} (seq_concat_map`{64,[8],8,Bit} (\<lambda>(i0 :: [8]). (seq_compr`{64,[6],Bit} (\<lambda>(t :: [6]). ((dbytes5`{} x i0 t) ==`{[32][8]} (seq_compr`{32,[14],[8]} (\<lambda>(j :: [14]). (obytes @`{16384,[8],[14]} (((zext`{14,8} i0) +`{[14]} ((0x100 :: [14]) *`{[14]} (zext`{14,6} t))) +`{[14]} j))) (fromToLessThan`{0,32,[14]})))) (fromTo`{0,63,[6]}))) (fromThenTo`{0,32,224,[8],8})))"

cryptol_definition dbytes5_is_decode5 :: "([2048][64]) \<Rightarrow> Bit" where
"dbytes5_is_decode5 x \<equiv> 
  let
    obytes = ((reverse`{16384,[8]} (split`{16384,8,Bit} (join`{2048,64,Bit} (reverse`{2048,[64]} (decode5`{} x))))) : ([16384][8]))
  in (and`{3} (seq_compr`{3,([8]) \<times> ([6]),Bit} (\<lambda>(i__p0 :: ([8]) \<times> ([6])). (
  let
    i0 = ((\<lambda>(x,_). x) i__p0 :: [8]);
    t = ((\<lambda>(_,x). x) i__p0 :: [6])
  in ((dbytes5`{} x i0 t) ==`{[32][8]} (seq_compr`{32,[14],[8]} (\<lambda>(j :: [14]). (obytes @`{16384,[8],[14]} (((zext`{14,8} i0) +`{[14]} ((0x100 :: [14]) *`{[14]} (zext`{14,6} t))) +`{[14]} j))) (fromToLessThan`{0,32,[14]}))))) (list_to_seq [((0x0 :: [8],0x0 :: [6])) : (([8]) \<times> ([6])),((0x20 :: [8],0x5 :: [6])) : (([8]) \<times> ([6])),((0xe0 :: [8],0x3f :: [6])) : (([8]) \<times> ([6]))] :: [3](([8]) \<times> ([6])))))"

cryptol_definition unflat2 :: "([32768]) \<Rightarrow> ([512][64])" where
"unflat2 v \<equiv> reverse`{512,[64]} (split`{512,64,Bit} v)"

cryptol_definition decode :: "([512][64]) \<Rightarrow> ([512][64])" where
"decode fx \<equiv> 
  let
    rows = ((seq_compr`{64,[8][64],[8][64]} (\<lambda>(blk :: [8][64]). (seq_compr`{8,[64],[64]} (\<lambda>(x :: [64]). (linmap`{64} decMat x)) blk)) (split`{64,8,[64]} fx)) : ([64][8][64]));
    outByte = ((\<lambda>(q :: [12]). (
    let
      i = ((drop`{6,6,Bit} q) : ([6]));
      t = ((take`{6,6,Bit} q) : ([6]));
      k = ((take`{3,3,Bit} t) : ([3]));
      j = ((drop`{3,3,Bit} t) : ([3]));
      rr = ((rows @`{64,[8][64],[6]} i) : ([8][64]))
    in ((transpose8`{} (seq_compr`{8,[64],[8]} (\<lambda>(r :: [64]). (byteOf`{} r k)) rr)) @`{8,[8],[3]} j))) : (([12]) \<Rightarrow> ([8])))
  in (unflat2`{} (join`{4096,8,Bit} (reverse`{4096,[8]} (seq_compr`{4096,[12],[8]} (\<lambda>(q :: [12]). (outByte`{} q)) (fromToLessThan`{0,4096,[12]})))))"

cryptol_definition decode3_is_asm3 :: "([1024][64]) \<Rightarrow> Bit" where
"decode3_is_asm3 x \<equiv> (decode3`{} x) ==`{[1024][64]} (asm3`{} x)"

cryptol_definition decodeIdx3 :: "([1024][64]) \<Rightarrow> ([1024][64])" where
"decodeIdx3 fx \<equiv> 
  let
    img = ((seq_compr`{1024,[64],[64]} (\<lambda>(x :: [64]). (linmap`{64} decMat x)) fx) : ([1024][64]))
  in (unflat23`{} (reverse`{65536,Bit} (seq_compr`{65536,[16],Bit} (\<lambda>(p :: [16]). ((img @`{1024,[64],[16]} (p %`{[16]} (0x400 :: [16]))) !`{64,Bit,[16]} (p /`{[16]} (0x400 :: [16])))) (fromToLessThan`{0,65536,[16]}))))"

cryptol_definition decode3_is_decodeIdx3 :: "([1024][64]) \<Rightarrow> Bit" where
"decode3_is_decodeIdx3 x \<equiv> (decode3`{} x) ==`{[1024][64]} (decodeIdx3`{} x)"

cryptol_definition decode5_is_asm5 :: "([2048][64]) \<Rightarrow> Bit" where
"decode5_is_asm5 x \<equiv> (decode5`{} x) ==`{[2048][64]} (asm5`{} x)"

cryptol_definition decodeIdx5 :: "([2048][64]) \<Rightarrow> ([2048][64])" where
"decodeIdx5 fx \<equiv> 
  let
    img = ((seq_compr`{2048,[64],[64]} (\<lambda>(x :: [64]). (linmap`{64} decMat x)) fx) : ([2048][64]))
  in (unflat25`{} (reverse`{131072,Bit} (seq_compr`{131072,[17],Bit} (\<lambda>(p :: [17]). ((img @`{2048,[64],[17]} (p %`{[17]} (0x800 :: [17]))) !`{64,Bit,[17]} (p /`{[17]} (0x800 :: [17])))) (fromToLessThan`{0,131072,[17]}))))"

cryptol_definition decode5_is_decodeIdx5 :: "([2048][64]) \<Rightarrow> Bit" where
"decode5_is_decodeIdx5 x \<equiv> (decode5`{} x) ==`{[2048][64]} (decodeIdx5`{} x)"

cryptol_definition decodeIdx :: "([512][64]) \<Rightarrow> ([512][64])" where
"decodeIdx fx \<equiv> 
  let
    img = ((seq_compr`{512,[64],[64]} (\<lambda>(x :: [64]). (linmap`{64} decMat x)) fx) : ([512][64]))
  in (unflat2`{} (reverse`{32768,Bit} (seq_compr`{32768,[15],Bit} (\<lambda>(p :: [15]). ((img @`{512,[64],[15]} (p %`{[15]} (0x200 :: [15]))) !`{64,Bit,[15]} (p /`{[15]} (0x200 :: [15])))) (fromToLessThan`{0,32768,[15]}))))"

cryptol_definition decode_is_decodeIdx :: "([512][64]) \<Rightarrow> Bit" where
"decode_is_decodeIdx x \<equiv> (decode`{} x) ==`{[512][64]} (decodeIdx`{} x)"

cryptol_definition encMat :: "[64][64]" where
"encMat  \<equiv> list_to_seq [0x1 :: [64],0xed57ce778f0d6244 :: [64],0xb66864e6ec14b4d2 :: [64],0x9cedebc39773a213 :: [64],0x54e5bf3774b3f850 :: [64],0xaa41ec72aca4d601 :: [64],0x4943d209fdc449b8 :: [64],0x6e9a7c0e6d89dc84 :: [64],0xeb42e79f91f49f8c :: [64],0x5dc314ada2848ba2 :: [64],0x503cdedab981d32c :: [64],0x21d93ab94919cfd3 :: [64],0x4553b41bda2fbec8 :: [64],0xcb47a62d21df0b4d :: [64],0x4639691aa527dbba :: [64],0xe032e7a43c3d150f :: [64],0xb0f502e4cd60039a :: [64],0xf8287767660ad2b4 :: [64],0x1dbf8d7727fc654e :: [64],0x19b12a51dacba79e :: [64],0xe691d7c0794c614d :: [64],0x28cf418faf97a29f :: [64],0xfc5c2bca45c931c :: [64],0x4cb433e14292028e :: [64],0x189b29840c130e7f :: [64],0x315f35290c617710 :: [64],0x1f4a9de7438026b :: [64],0x6aea5df783dd08ef :: [64],0xb36ae8e530273635 :: [64],0x837b54ac6006165d :: [64],0x49216693bb420e26 :: [64],0xfd50e246ba0fe1a8 :: [64],0x57a3104fcd0e5f34 :: [64],0xbfbbcc4e6e818ce9 :: [64],0x4ff85cdbb8b5a385 :: [64],0xe5836ac7d88636ff :: [64],0xacaee33d357e7115 :: [64],0xd5591c1e1fcd94ac :: [64],0x5a80ddb4eb880892 :: [64],0x557feec300cdaab7 :: [64],0x5a3fd6353ee07e37 :: [64],0x5c467f7d2caf0e9f :: [64],0xeaac97005f61500b :: [64],0x9554e988c2331d19 :: [64],0x46fc62831b042eeb :: [64],0xe89bd07ebe5cbadc :: [64],0xe442a47d4ab744e :: [64],0x492fcd9722316b93 :: [64],0xb86431a85814f803 :: [64],0xa3c96aff342c82b8 :: [64],0x4716ccf6cbc75a1a :: [64],0x5b71bea40e882374 :: [64],0x54ac9ee9b21ebe6e :: [64],0x1aac7f922b29c823 :: [64],0x49a5f74a2ecb3e44 :: [64],0x4a5a968cc3b566d1 :: [64],0x641ddcf92a60aa5 :: [64],0xee004d8f989dba16 :: [64],0x1c2242e610c9cd6a :: [64],0x59f1654505010e32 :: [64],0xd8df39e76c0e7b7 :: [64],0x8cf8e69eb14ecfb4 :: [64],0xcb8c5396572fc44 :: [64],0x3b278b84a916e44c :: [64]] :: [64][64]"

cryptol_definition lin8 :: "([32][8]) \<Rightarrow> ([8][64])" where
"lin8 bits \<equiv> seq_compr`{8,[3],[64]} (\<lambda>(kk :: [3]). (foldl`{32,[64],[64]} (\<lblot>^`{[64]}\<rblot>) (0x0 :: [64]) (seq_compr`{32,[5],[64]} (\<lambda>(j :: [5]). (if (bits @`{32,[8],[5]} j) !`{8,Bit,[3]} kk then (encMat @`{64,[64],[5]} j) else coerce (0x0 :: [64]))) (fromToLessThan`{0,32,[5]})))) (fromToLessThan`{0,8,[3]})"

cryptol_definition encode :: "([256][64]) \<Rightarrow> ([512][64])" where
"encode fx \<equiv> join`{64,8,[64]} (seq_compr`{64,[12],[8][64]} (\<lambda>(i :: [12]). (lin8`{} (collect64`{} fx i))) (fromToLessThan`{0,64,[12]}))"

cryptol_definition encode3 :: "([512][64]) \<Rightarrow> ([1024][64])" where
"encode3 fx \<equiv> join`{128,8,[64]} (seq_compr`{128,[13],[8][64]} (\<lambda>(i :: [13]). (lin8`{} (collect128`{} fx i))) (fromToLessThan`{0,128,[13]}))"

cryptol_definition flat3 :: "([512][64]) \<Rightarrow> ([32768])" where
"flat3 fx \<equiv> join`{512,64,Bit} (reverse`{512,[64]} fx)"

cryptol_definition encodeIdx3 :: "([512][64]) \<Rightarrow> ([1024][64])" where
"encodeIdx3 fx \<equiv> 
  let
    fb = ((flat3`{} fx) : ([32768]))
  in (seq_compr`{1024,[16],[64]} (\<lambda>(e :: [16]). (linmap`{32} encMat (reverse`{32,Bit} (seq_compr`{32,[16],Bit} (\<lambda>(j :: [16]). (fb !`{32768,Bit,[16]} (((0x400 :: [16]) *`{[16]} j) +`{[16]} e))) (fromToLessThan`{0,32,[16]}))))) (fromToLessThan`{0,1024,[16]}))"

cryptol_definition encode3_is_encodeIdx3 :: "([512][64]) \<Rightarrow> Bit" where
"encode3_is_encodeIdx3 x \<equiv> (encode3`{} x) ==`{[1024][64]} (encodeIdx3`{} x)"

cryptol_definition encode5 :: "([1024][64]) \<Rightarrow> ([2048][64])" where
"encode5 fx \<equiv> join`{256,8,[64]} (seq_compr`{256,[14],[8][64]} (\<lambda>(i :: [14]). (lin8`{} (collect256`{} fx i))) (fromToLessThan`{0,256,[14]}))"

cryptol_definition flat5 :: "([1024][64]) \<Rightarrow> ([65536])" where
"flat5 fx \<equiv> join`{1024,64,Bit} (reverse`{1024,[64]} fx)"

cryptol_definition encodeIdx5 :: "([1024][64]) \<Rightarrow> ([2048][64])" where
"encodeIdx5 fx \<equiv> 
  let
    fb = ((flat5`{} fx) : ([65536]))
  in (seq_compr`{2048,[17],[64]} (\<lambda>(e :: [17]). (linmap`{32} encMat (reverse`{32,Bit} (seq_compr`{32,[17],Bit} (\<lambda>(j :: [17]). (fb !`{65536,Bit,[17]} (((0x800 :: [17]) *`{[17]} j) +`{[17]} e))) (fromToLessThan`{0,32,[17]}))))) (fromToLessThan`{0,2048,[17]}))"

cryptol_definition encode5_is_encodeIdx5 :: "([1024][64]) \<Rightarrow> Bit" where
"encode5_is_encodeIdx5 x \<equiv> (encode5`{} x) ==`{[2048][64]} (encodeIdx5`{} x)"

cryptol_definition flat :: "([256][64]) \<Rightarrow> ([16384])" where
"flat fx \<equiv> join`{256,64,Bit} (reverse`{256,[64]} fx)"

cryptol_definition encodeIdx :: "([256][64]) \<Rightarrow> ([512][64])" where
"encodeIdx fx \<equiv> 
  let
    fb = ((flat`{} fx) : ([16384]))
  in (seq_compr`{512,[14],[64]} (\<lambda>(e :: [14]). (linmap`{32} encMat (reverse`{32,Bit} (seq_compr`{32,[14],Bit} (\<lambda>(j :: [14]). (fb !`{16384,Bit,[14]} (((0x200 :: [14]) *`{[14]} j) +`{[14]} e))) (fromToLessThan`{0,32,[14]}))))) (fromToLessThan`{0,512,[14]}))"

cryptol_definition encode_is_encodeIdx :: "([256][64]) \<Rightarrow> Bit" where
"encode_is_encodeIdx x \<equiv> (encode`{} x) ==`{[512][64]} (encodeIdx`{} x)"

cryptol_definition unflat :: "([16384]) \<Rightarrow> ([256][64])" where
"unflat v \<equiv> reverse`{256,[64]} (split`{256,64,Bit} v)"

end
end
