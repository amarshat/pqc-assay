theory "MLKEM_NTT"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition Q16 :: "[16]" where
"Q16  \<equiv> 0xd01 :: [16]"

cryptol_definition Q32 :: "[32]" where
"Q32  \<equiv> 0xd01 :: [32]"

cryptol_definition QINV :: "[16]" where
"QINV  \<equiv> negate`{[16]} (0xcff :: [16])"

cryptol_definition V16 :: "[16]" where
"V16  \<equiv> 0x4ebf :: [16]"

cryptol_definition q :: "Integer" where
"q  \<equiv> 3329 :: Integer"

cryptol_definition si16 :: "([16]) \<Rightarrow> Integer" where
"si16 x \<equiv> if x @`{16,Bit,Integer} (0 :: Integer) then ((toInteger`{[16]} x) -`{Integer} (65536 :: Integer)) else coerce (toInteger`{[16]} x)"

cryptol_definition sext32 :: "([16]) \<Rightarrow> ([32])" where
"sext32 x \<equiv> (if x @`{16,Bit,Integer} (0 :: Integer) then (complement`{[16]} (zero`{[16]})) else coerce (zero`{[16]})) #`{16,16,Bit} x"

cryptol_definition barrett_reduce :: "([16]) \<Rightarrow> ([16])" where
"barrett_reduce a \<equiv> 
  let
    t1 = (((((sext32`{} V16) *`{[32]} (sext32`{} a)) +`{[32]} (0x2000000 :: [32])) >>$`{32,Integer} (26 :: Integer)) : ([32]));
    t2 = (((drop`{16,16,Bit} t1) *`{[16]} Q16) : ([16]))
  in (a -`{[16]} t2)"

cryptol_definition barrett_correct :: "([16]) \<Rightarrow> Bit" where
"barrett_correct a \<equiv> 
  let
    r = ((si16`{} (barrett_reduce`{} a)) : Integer)
  in ((((r -`{Integer} (si16`{} a)) %`{Integer} q) ==`{Integer} (0 :: Integer)) \<and> ((r >=`{Integer} (negate`{Integer} (1664 :: Integer))) \<and> (r <=`{Integer} (1664 :: Integer))))"

cryptol_definition montgomery_reduce :: "([32]) \<Rightarrow> ([16])" where
"montgomery_reduce a \<equiv> 
  let
    t = (((drop`{16,16,Bit} a) *`{[16]} QINV) : ([16]))
  in (drop`{16,16,Bit} ((a -`{[32]} ((sext32`{} t) *`{[32]} Q32)) >>$`{32,Integer} (16 :: Integer)))"

cryptol_definition fqmul :: "([16]) \<Rightarrow> (([16]) \<Rightarrow> ([16]))" where
"fqmul a b \<equiv> montgomery_reduce`{} ((sext32`{} a) *`{[32]} (sext32`{} b))"

cryptol_definition invf :: "[16]" where
"invf  \<equiv> 0x5a1 :: [16]"

cryptol_definition zetas :: "[128][16]" where
"zetas  \<equiv> list_to_seq [(negate`{[16]} (0x414 :: [16])) : ([16]),(negate`{[16]} (0x2f6 :: [16])) : ([16]),(negate`{[16]} (0x167 :: [16])) : ([16]),(negate`{[16]} (0x5ed :: [16])) : ([16]),0x5d5 :: [16],0x58e :: [16],0x11f :: [16],0xca :: [16],(negate`{[16]} (0xab :: [16])) : ([16]),0x26e :: [16],0x629 :: [16],0xb6 :: [16],0x3c2 :: [16],(negate`{[16]} (0x4b2 :: [16])) : ([16]),(negate`{[16]} (0x5c2 :: [16])) : ([16]),0x5bc :: [16],0x23d :: [16],(negate`{[16]} (0x52d :: [16])) : ([16]),0x108 :: [16],0x17f :: [16],(negate`{[16]} (0x33d :: [16])) : ([16]),0x5b2 :: [16],(negate`{[16]} (0x642 :: [16])) : ([16]),(negate`{[16]} (0x82 :: [16])) : ([16]),(negate`{[16]} (0x2a9 :: [16])) : ([16]),0x3f9 :: [16],0x2dc :: [16],0x260 :: [16],(negate`{[16]} (0x606 :: [16])) : ([16]),0x19b :: [16],(negate`{[16]} (0xcd :: [16])) : ([16]),(negate`{[16]} (0x623 :: [16])) : ([16]),0x4c7 :: [16],0x28c :: [16],(negate`{[16]} (0x228 :: [16])) : ([16]),0x3f7 :: [16],(negate`{[16]} (0x50d :: [16])) : ([16]),0x5d3 :: [16],(negate`{[16]} (0x11a :: [16])) : ([16]),(negate`{[16]} (0x608 :: [16])) : ([16]),0x204 :: [16],(negate`{[16]} (0x8 :: [16])) : ([16]),(negate`{[16]} (0x140 :: [16])) : ([16]),(negate`{[16]} (0x29a :: [16])) : ([16]),(negate`{[16]} (0x652 :: [16])) : ([16]),(negate`{[16]} (0x48a :: [16])) : ([16]),0x7e :: [16],0x5bd :: [16],(negate`{[16]} (0x355 :: [16])) : ([16]),(negate`{[16]} (0x5a :: [16])) : ([16]),(negate`{[16]} (0x10f :: [16])) : ([16]),0x33e :: [16],0x6b :: [16],(negate`{[16]} (0x58d :: [16])) : ([16]),(negate`{[16]} (0xf7 :: [16])) : ([16]),(negate`{[16]} (0x3b7 :: [16])) : ([16]),(negate`{[16]} (0x18e :: [16])) : ([16]),0x3c1 :: [16],(negate`{[16]} (0x5e4 :: [16])) : ([16]),(negate`{[16]} (0x2d5 :: [16])) : ([16]),0x1c0 :: [16],(negate`{[16]} (0x429 :: [16])) : ([16]),0x2a5 :: [16],(negate`{[16]} (0x4fb :: [16])) : ([16]),(negate`{[16]} (0x44f :: [16])) : ([16]),0x1ae :: [16],0x22b :: [16],0x34b :: [16],(negate`{[16]} (0x4e3 :: [16])) : ([16]),0x367 :: [16],0x60e :: [16],0x69 :: [16],0x1a6 :: [16],0x24b :: [16],0xb1 :: [16],(negate`{[16]} (0xeb :: [16])) : ([16]),(negate`{[16]} (0x123 :: [16])) : ([16]),(negate`{[16]} (0x1cc :: [16])) : ([16]),0x626 :: [16],0x675 :: [16],(negate`{[16]} (0xf6 :: [16])) : ([16]),0x30a :: [16],0x487 :: [16],(negate`{[16]} (0x93 :: [16])) : ([16]),(negate`{[16]} (0x309 :: [16])) : ([16]),0x5cb :: [16],(negate`{[16]} (0x25a :: [16])) : ([16]),0x45f :: [16],(negate`{[16]} (0x636 :: [16])) : ([16]),0x284 :: [16],(negate`{[16]} (0x368 :: [16])) : ([16]),0x15d :: [16],0x1a2 :: [16],0x149 :: [16],(negate`{[16]} (0x9c :: [16])) : ([16]),(negate`{[16]} (0x4b :: [16])) : ([16]),0x331 :: [16],0x449 :: [16],0x25b :: [16],0x262 :: [16],0x52a :: [16],(negate`{[16]} (0x505 :: [16])) : ([16]),(negate`{[16]} (0x5b9 :: [16])) : ([16]),0x180 :: [16],(negate`{[16]} (0x4bf :: [16])) : ([16]),(negate`{[16]} (0x88 :: [16])) : ([16]),0x4c2 :: [16],(negate`{[16]} (0x537 :: [16])) : ([16]),(negate`{[16]} (0x36a :: [16])) : ([16]),0xdc :: [16],(negate`{[16]} (0x4a3 :: [16])) : ([16]),(negate`{[16]} (0x67b :: [16])) : ([16]),(negate`{[16]} (0x4a1 :: [16])) : ([16]),(negate`{[16]} (0x5fa :: [16])) : ([16]),(negate`{[16]} (0x4fe :: [16])) : ([16]),0x31a :: [16],(negate`{[16]} (0x5e6 :: [16])) : ([16]),(negate`{[16]} (0x356 :: [16])) : ([16]),(negate`{[16]} (0x366 :: [16])) : ([16]),0x1de :: [16],(negate`{[16]} (0x6c :: [16])) : ([16]),(negate`{[16]} (0x134 :: [16])) : ([16]),0x3e4 :: [16],0x3df :: [16],0x3be :: [16],(negate`{[16]} (0x5b4 :: [16])) : ([16]),0x5f2 :: [16],0x65c :: [16]] :: [128][16]"

cryptol_definition invnttLevel :: "([16]) \<Rightarrow> (([256][16]) \<Rightarrow> ([256][16]))" where
"invnttLevel ell a \<equiv> 
  let
    len = (((0x2 :: [16]) <<`{16,[16],Bit} ell) : ([16]));
    twolen = ((len <<`{16,Integer,Bit} (1 :: Integer)) : ([16]));
    base = (((0x1 :: [16]) <<`{16,[16],Bit} ((0x6 :: [16]) -`{[16]} ell)) : ([16]));
    top = ((((0x2 :: [16]) *`{[16]} base) -`{[16]} (0x1 :: [16])) : ([16]));
    bf = ((\<lambda>(m :: [16]). (if (m %`{[16]} twolen) <`{[16]} len then (barrett_reduce`{} ((a @`{256,[16],[16]} m) +`{[16]} (a @`{256,[16],[16]} (m +`{[16]} len)))) else coerce (fqmul`{} (zetas @`{128,[16],[16]} (top -`{[16]} ((m -`{[16]} len) /`{[16]} twolen))) ((a @`{256,[16],[16]} m) -`{[16]} (a @`{256,[16],[16]} (m -`{[16]} len)))))) : (([16]) \<Rightarrow> ([16])))
  in (seq_compr`{256,[16],[16]} (\<lambda>(m :: [16]). (bf`{} m)) (fromTo`{0,255,[16]}))"

cryptol_definition invntt :: "([256][16]) \<Rightarrow> ([256][16])" where
"invntt a0 \<equiv> 
  let
    step = ((\<lambda>(a :: [256][16]) (ell :: [16]). (invnttLevel`{} ell a)) : (([256][16]) \<Rightarrow> (([16]) \<Rightarrow> ([256][16]))));
    b = ((foldl`{7,[256][16],[16]} step a0 (list_to_seq [0x0 :: [16],0x1 :: [16],0x2 :: [16],0x3 :: [16],0x4 :: [16],0x5 :: [16],0x6 :: [16]] :: [7][16])) : ([256][16]))
  in (seq_compr`{256,[16],[16]} (\<lambda>(j :: [16]). (fqmul`{} (b @`{256,[16],[16]} j) invf)) (fromTo`{0,255,[16]}))"

cryptol_definition si32 :: "([32]) \<Rightarrow> Integer" where
"si32 x \<equiv> if x @`{32,Bit,Integer} (0 :: Integer) then ((toInteger`{[32]} x) -`{Integer} (4294967296 :: Integer)) else coerce (toInteger`{[32]} x)"

cryptol_definition mont_in_range :: "([32]) \<Rightarrow> Bit" where
"mont_in_range a \<equiv> 
  let
    hi = (((((0x2 :: [32]) ^^`{[32],Integer} (15 :: Integer)) *`{[32]} Q32) -`{[32]} (0x1 :: [32])) : ([32]));
    lo = ((negate`{[32]} (((0x2 :: [32]) ^^`{[32],Integer} (15 :: Integer)) *`{[32]} Q32)) : ([32]))
  in ((a >=$`{[32]} lo) &&`{Bit} (a <=$`{[32]} hi))"

cryptol_definition mont_correct :: "([32]) \<Rightarrow> Bit" where
"mont_correct a \<equiv> 
  let
    r = ((si16`{} (montgomery_reduce`{} a)) : Integer)
  in ((mont_in_range`{} a) \<longrightarrow> (((((r *`{Integer} (65536 :: Integer)) -`{Integer} (si32`{} a)) %`{Integer} q) ==`{Integer} (0 :: Integer)) \<and> ((r >`{Integer} (negate`{Integer} q)) \<and> (r <`{Integer} q))))"

cryptol_definition sext48_32 :: "([32]) \<Rightarrow> ([48])" where
"sext48_32 x \<equiv> (if x @`{32,Bit,Integer} (0 :: Integer) then (complement`{[16]} (zero`{[16]})) else coerce (zero`{[16]})) #`{16,32,Bit} x"

cryptol_definition sext48_16 :: "([16]) \<Rightarrow> ([48])" where
"sext48_16 x \<equiv> (if x @`{16,Bit,Integer} (0 :: Integer) then (complement`{[32]} (zero`{[32]})) else coerce (zero`{[32]})) #`{32,16,Bit} x"

cryptol_definition mont_correct_bv :: "([32]) \<Rightarrow> Bit" where
"mont_correct_bv a \<equiv> 
  let
    r = ((montgomery_reduce`{} a) : ([16]));
    d = ((((sext48_16`{} r) <<`{48,[48],Bit} (0x10 :: [48])) -`{[48]} (sext48_32`{} a)) : ([48]))
  in ((mont_in_range`{} a) \<longrightarrow> (((d %$`{48} (0xd01 :: [48])) ==`{[48]} (0x0 :: [48])) \<and> ((r >$`{[16]} (negate`{[16]} (0xd01 :: [16]))) \<and> (r <$`{[16]} (0xd01 :: [16])))))"

cryptol_definition nttLevel :: "([16]) \<Rightarrow> (([256][16]) \<Rightarrow> ([256][16]))" where
"nttLevel i a \<equiv> 
  let
    len = (((0x80 :: [16]) >>`{16,[16],Bit} i) : ([16]));
    twolen = (((0x100 :: [16]) >>`{16,[16],Bit} i) : ([16]));
    base = (((0x1 :: [16]) <<`{16,[16],Bit} i) : ([16]));
    bf = ((\<lambda>(m :: [16]). (if (m %`{[16]} twolen) <`{[16]} len then ((a @`{256,[16],[16]} m) +`{[16]} (fqmul`{} (zetas @`{128,[16],[16]} (base +`{[16]} (m /`{[16]} twolen))) (a @`{256,[16],[16]} (m +`{[16]} len)))) else coerce ((a @`{256,[16],[16]} (m -`{[16]} len)) -`{[16]} (fqmul`{} (zetas @`{128,[16],[16]} (base +`{[16]} ((m -`{[16]} len) /`{[16]} twolen))) (a @`{256,[16],[16]} m))))) : (([16]) \<Rightarrow> ([16])))
  in (seq_compr`{256,[16],[16]} (\<lambda>(m :: [16]). (bf`{} m)) (fromTo`{0,255,[16]}))"

cryptol_definition ntt :: "([256][16]) \<Rightarrow> ([256][16])" where
"ntt a0 \<equiv> 
  let
    step = ((\<lambda>(a :: [256][16]) (i :: [16]). (nttLevel`{} i a)) : (([256][16]) \<Rightarrow> (([16]) \<Rightarrow> ([256][16]))))
  in (foldl`{7,[256][16],[16]} step a0 (list_to_seq [0x0 :: [16],0x1 :: [16],0x2 :: [16],0x3 :: [16],0x4 :: [16],0x5 :: [16],0x6 :: [16]] :: [7][16]))"

cryptol_definition roundtrip :: "([256][16]) \<Rightarrow> Bit" where
"roundtrip x0 \<equiv> 
  let
    x = ((seq_compr`{256,[16],[16]} (\<lambda>(xi :: [16]). (barrett_reduce`{} xi)) x0) : ([256][16]));
    b = ((invntt`{} (ntt`{} x)) : ([256][16]));
    mont = ((negate`{Integer} (1044 :: Integer)) : Integer)
  in (and`{256} (seq_compr`{256,Integer,Bit} (\<lambda>(i :: Integer). ((((si16`{} (b @`{256,[16],Integer} i)) -`{Integer} (mont *`{Integer} (si16`{} (x @`{256,[16],Integer} i)))) %`{Integer} q) ==`{Integer} (0 :: Integer))) (fromTo`{0,255,Integer})))"

end
end
