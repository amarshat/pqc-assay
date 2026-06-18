theory "fips204_ntt_lift"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
type_synonym W = "[64]"

cryptol_definition fwdParamsRef :: "[8](([64]) \<times> ([64]) \<times> ([64]))" where
"fwdParamsRef  \<equiv> list_to_seq [((0x80 :: [64],0x1 :: [64],0x0 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x40 :: [64],0x2 :: [64],0x1 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x20 :: [64],0x4 :: [64],0x3 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x10 :: [64],0x8 :: [64],0x7 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x8 :: [64],0x10 :: [64],0xf :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x4 :: [64],0x20 :: [64],0x1f :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x2 :: [64],0x40 :: [64],0x3f :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x1 :: [64],0x80 :: [64],0x7f :: [64])) : (([64]) \<times> ([64]) \<times> ([64]))] :: [8](([64]) \<times> ([64]) \<times> ([64]))"

cryptol_definition invParamsRef :: "[8](([64]) \<times> ([64]) \<times> ([64]))" where
"invParamsRef  \<equiv> list_to_seq [((0x1 :: [64],0x80 :: [64],0x100 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x2 :: [64],0x40 :: [64],0x80 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x4 :: [64],0x20 :: [64],0x40 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x8 :: [64],0x10 :: [64],0x20 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x10 :: [64],0x8 :: [64],0x10 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x20 :: [64],0x4 :: [64],0x8 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x40 :: [64],0x2 :: [64],0x4 :: [64])) : (([64]) \<times> ([64]) \<times> ([64])),((0x80 :: [64],0x1 :: [64],0x2 :: [64])) : (([64]) \<times> ([64]) \<times> ([64]))] :: [8](([64]) \<times> ([64]) \<times> ([64]))"

cryptol_definition q :: "W" where
"q  \<equiv> 8380417 :: W"

cryptol_definition zetabrv :: "[256][32]" where
"zetabrv  \<equiv> list_to_seq [0x1 :: [32],0x495e02 :: [32],0x397567 :: [32],0x396569 :: [32],0x4f062b :: [32],0x53df73 :: [32],0x4fe033 :: [32],0x4f066b :: [32],0x76b1ae :: [32],0x360dd5 :: [32],0x28edb0 :: [32],0x207fe4 :: [32],0x397283 :: [32],0x70894a :: [32],0x88192 :: [32],0x6d3dc8 :: [32],0x4c7294 :: [32],0x41e0b4 :: [32],0x28a3d2 :: [32],0x66528a :: [32],0x4a18a7 :: [32],0x794034 :: [32],0xa52ee :: [32],0x6b7d81 :: [32],0x4e9f1d :: [32],0x1a2877 :: [32],0x2571df :: [32],0x1649ee :: [32],0x7611bd :: [32],0x492bb7 :: [32],0x2af697 :: [32],0x22d8d5 :: [32],0x36f72a :: [32],0x30911e :: [32],0x29d13f :: [32],0x492673 :: [32],0x50685f :: [32],0x2010a2 :: [32],0x3887f7 :: [32],0x11b2c3 :: [32],0x603a4 :: [32],0xe2bed :: [32],0x10b72c :: [32],0x4a5f35 :: [32],0x1f9d15 :: [32],0x428cd4 :: [32],0x3177f4 :: [32],0x20e612 :: [32],0x341c1d :: [32],0x1ad873 :: [32],0x736681 :: [32],0x49553f :: [32],0x3952f6 :: [32],0x62564a :: [32],0x65ad05 :: [32],0x439a1c :: [32],0x53aa5f :: [32],0x30b622 :: [32],0x87f38 :: [32],0x3b0e6d :: [32],0x2c83da :: [32],0x1c496e :: [32],0x330e2b :: [32],0x1c5b70 :: [32],0x2ee3f1 :: [32],0x137eb9 :: [32],0x57a930 :: [32],0x3ac6ef :: [32],0x3fd54c :: [32],0x4eb2ea :: [32],0x503ee1 :: [32],0x7bb175 :: [32],0x2648b4 :: [32],0x1ef256 :: [32],0x1d90a2 :: [32],0x45a6d4 :: [32],0x2ae59b :: [32],0x52589c :: [32],0x6ef1f5 :: [32],0x3f7288 :: [32],0x175102 :: [32],0x75d59 :: [32],0x1187ba :: [32],0x52aca9 :: [32],0x773e9e :: [32],0x296d8 :: [32],0x2592ec :: [32],0x4cff12 :: [32],0x404ce8 :: [32],0x4aa582 :: [32],0x1e54e6 :: [32],0x4f16c1 :: [32],0x1a7e79 :: [32],0x3978f :: [32],0x4e4817 :: [32],0x31b859 :: [32],0x5884cc :: [32],0x1b4827 :: [32],0x5b63d0 :: [32],0x5d787a :: [32],0x35225e :: [32],0x400c7e :: [32],0x6c09d1 :: [32],0x5bd532 :: [32],0x6bc4d3 :: [32],0x258ecb :: [32],0x2e534c :: [32],0x97a6c :: [32],0x3b8820 :: [32],0x6d285c :: [32],0x2ca4f8 :: [32],0x337caa :: [32],0x14b2a0 :: [32],0x558536 :: [32],0x28f186 :: [32],0x55795d :: [32],0x4af670 :: [32],0x234a86 :: [32],0x75e826 :: [32],0x78de66 :: [32],0x5528c :: [32],0x7adf59 :: [32],0xf6e17 :: [32],0x5bf3da :: [32],0x459b7e :: [32],0x628b34 :: [32],0x5dbecb :: [32],0x1a9e7b :: [32],0x6d9 :: [32],0x6257c5 :: [32],0x574b3c :: [32],0x69a8ef :: [32],0x289838 :: [32],0x64b5fe :: [32],0x7ef8f5 :: [32],0x2a4e78 :: [32],0x120a23 :: [32],0x154a8 :: [32],0x9b7ff :: [32],0x435e87 :: [32],0x437ff8 :: [32],0x5cd5b4 :: [32],0x4dc04e :: [32],0x4728af :: [32],0x7f735d :: [32],0xc8d0d :: [32],0xf66d5 :: [32],0x5a6d80 :: [32],0x61ab98 :: [32],0x185d96 :: [32],0x437f31 :: [32],0x468298 :: [32],0x662960 :: [32],0x4bd579 :: [32],0x28de06 :: [32],0x465d8d :: [32],0x49b0e3 :: [32],0x9b434 :: [32],0x7c0db3 :: [32],0x5a68b0 :: [32],0x409ba9 :: [32],0x64d3d5 :: [32],0x21762a :: [32],0x658591 :: [32],0x246e39 :: [32],0x48c39b :: [32],0x7bc759 :: [32],0x4f5859 :: [32],0x392db2 :: [32],0x230923 :: [32],0x12eb67 :: [32],0x454df2 :: [32],0x30c31c :: [32],0x285424 :: [32],0x13232e :: [32],0x7faf80 :: [32],0x2dbfcb :: [32],0x22a0b :: [32],0x7e832c :: [32],0x26587a :: [32],0x6b3375 :: [32],0x95b76 :: [32],0x6be1cc :: [32],0x5e061e :: [32],0x78e00d :: [32],0x628c37 :: [32],0x3da604 :: [32],0x4ae53c :: [32],0x1f1d68 :: [32],0x6330bb :: [32],0x7361b8 :: [32],0x5ea06c :: [32],0x671ac7 :: [32],0x201fc6 :: [32],0x5ba4ff :: [32],0x60d772 :: [32],0x8f201 :: [32],0x6de024 :: [32],0x80e6d :: [32],0x56038e :: [32],0x695688 :: [32],0x1e6d3e :: [32],0x2603bd :: [32],0x6a9dfa :: [32],0x7c017 :: [32],0x6dbfd4 :: [32],0x74d0bd :: [32],0x63e1e3 :: [32],0x519573 :: [32],0x7ab60d :: [32],0x2867ba :: [32],0x2decd4 :: [32],0x58018c :: [32],0x3f4cf5 :: [32],0xb7009 :: [32],0x427e23 :: [32],0x3cbd37 :: [32],0x273333 :: [32],0x673957 :: [32],0x1a4b5d :: [32],0x196926 :: [32],0x1ef206 :: [32],0x11c14e :: [32],0x4c76c8 :: [32],0x3cf42f :: [32],0x7fb19a :: [32],0x6af66c :: [32],0x2e1669 :: [32],0x3352d6 :: [32],0x34760 :: [32],0x85260 :: [32],0x741e78 :: [32],0x2f6316 :: [32],0x6f0a11 :: [32],0x7c0f1 :: [32],0x776d0b :: [32],0xd1ff0 :: [32],0x345824 :: [32],0x223d4 :: [32],0x68c559 :: [32],0x5e8885 :: [32],0x2faa32 :: [32],0x23fc65 :: [32],0x5e6942 :: [32],0x51e0ed :: [32],0x65adb3 :: [32],0x2ca5e6 :: [32],0x79e1fe :: [32],0x7b4064 :: [32],0x35e1dd :: [32],0x433aac :: [32],0x464ade :: [32],0x1cfe14 :: [32],0x73f1ce :: [32],0x10170e :: [32],0x74b6d7 :: [32]] :: [256][32]"

cryptol_definition nttLayerFwd :: "W \<Rightarrow> (W \<Rightarrow> (W \<Rightarrow> (([256][32]) \<Rightarrow> ([256][32]))))" where
"nttLayerFwd len iter m0 w \<equiv> 
  let
    wAt = ((\<lambda>(i :: W). (zext`{64,32} (w @`{256,[32],W} i))) : (W \<Rightarrow> W));
    f = ((\<lambda>(p :: W). (
    let
      blk = ((p /`{W} ((2 :: W) *`{W} len)) : W);
      off = ((p %`{W} ((2 :: W) *`{W} len)) : W);
      z = ((zext`{64,32} (zetabrv @`{256,[32],W} ((m0 +`{W} blk) +`{W} (1 :: W)))) : ([64]));
      t = (((z *`{[64]} (wAt`{} (p +`{W} len))) %`{[64]} q) : ([64]));
      tHi = (((z *`{[64]} (wAt`{} p)) %`{[64]} q) : ([64]))
    in (if blk >=`{W} iter then (w @`{256,[32],W} p) else coerce (if off <`{W} len then (drop`{32,32,Bit} (((wAt`{} p) +`{[64]} t) %`{[64]} q)) else coerce (drop`{32,32,Bit} ((((wAt`{} (p -`{W} len)) +`{[64]} q) -`{[64]} tHi) %`{[64]} q)))))) : (W \<Rightarrow> ([32])))
  in (seq_compr`{256,[8],[32]} (\<lambda>(p :: [8]). (f`{} (zext`{64,8} p))) (fromTo`{0,255,[8]}))"

cryptol_definition nttFwdAllRef :: "([256][32]) \<Rightarrow> ([256][32])" where
"nttFwdAllRef w0 \<equiv> 
  let
    step = ((\<lambda>(w :: [256][32]) (i__p0 :: (W) \<times> (W) \<times> (W)). (
    let
      m0 = ((\<lambda>(_,_,x). x) i__p0 :: W);
      iter = ((\<lambda>(_,x,_). x) i__p0 :: W);
      len = ((\<lambda>(x,_,_). x) i__p0 :: W)
    in (nttLayerFwd`{} len iter m0 w))) : (([256][32]) \<Rightarrow> (((W) \<times> (W) \<times> (W)) \<Rightarrow> ([256][32]))))
  in (foldl`{8,[256][32],(W) \<times> (W) \<times> (W)} step w0 fwdParamsRef)"

cryptol_definition nttLayerInv :: "W \<Rightarrow> (W \<Rightarrow> (W \<Rightarrow> (([256][32]) \<Rightarrow> ([256][32]))))" where
"nttLayerInv len iter m0 w \<equiv> 
  let
    wAt = ((\<lambda>(i :: W). (zext`{64,32} (w @`{256,[32],W} i))) : (W \<Rightarrow> W));
    f = ((\<lambda>(p :: W). (
    let
      blk = ((p /`{W} ((2 :: W) *`{W} len)) : W);
      off = ((p %`{W} ((2 :: W) *`{W} len)) : W);
      z = (((q -`{W} (zext`{64,32} (zetabrv @`{256,[32],W} ((m0 -`{W} (1 :: W)) -`{W} blk)))) %`{W} q) : W);
      tHi = (((((wAt`{} (p -`{W} len)) +`{W} q) -`{W} (wAt`{} p)) %`{W} q) : W)
    in (if blk >=`{W} iter then (w @`{256,[32],W} p) else coerce (if off <`{W} len then (drop`{32,32,Bit} (((wAt`{} p) +`{[64]} (wAt`{} (p +`{W} len))) %`{[64]} q)) else coerce (drop`{32,32,Bit} ((z *`{[64]} tHi) %`{[64]} q)))))) : (W \<Rightarrow> ([32])))
  in (seq_compr`{256,[8],[32]} (\<lambda>(p :: [8]). (f`{} (zext`{64,8} p))) (fromTo`{0,255,[8]}))"

cryptol_definition nttInvAllRef :: "([256][32]) \<Rightarrow> ([256][32])" where
"nttInvAllRef w0 \<equiv> 
  let
    step = ((\<lambda>(w :: [256][32]) (i__p1 :: (W) \<times> (W) \<times> (W)). (
    let
      m0 = ((\<lambda>(_,_,x). x) i__p1 :: W);
      iter = ((\<lambda>(_,x,_). x) i__p1 :: W);
      len = ((\<lambda>(x,_,_). x) i__p1 :: W)
    in (nttLayerInv`{} len iter m0 w))) : (([256][32]) \<Rightarrow> (((W) \<times> (W) \<times> (W)) \<Rightarrow> ([256][32]))))
  in (foldl`{8,[256][32],(W) \<times> (W) \<times> (W)} step w0 invParamsRef)"

end
end
