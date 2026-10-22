theory "GF2X"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition clmul1 :: "([64]) \<Rightarrow> (([64]) \<Rightarrow> ([2][64]))" where
"clmul1 a b \<equiv> 
  let
    step = ((\<lambda>(acc :: [128]) (i :: [7]). (if a !`{64,Bit,[7]} i then (acc ^`{[128]} (((zero`{[64]}) #`{64,64,Bit} b) <<`{128,[7],Bit} i)) else coerce acc)) : (([128]) \<Rightarrow> (([7]) \<Rightarrow> ([128]))));
    r = ((foldl`{64,[128],[7]} step (zero`{[128]}) (fromTo`{0,63,[7]})) : ([128]))
  in (list_to_seq [(drop`{64,64,Bit} r) : ([64]),(take`{64,64,Bit} r) : ([64])] :: [2][64])"

cryptol_definition km1 :: "([1][64]) \<Rightarrow> (([1][64]) \<Rightarrow> ([2][64]))" where
"km1 a b \<equiv> clmul1`{} (a @`{1,[64],Integer} (0 :: Integer)) (b @`{1,[64],Integer} (0 :: Integer))"

cryptol_definition kstep :: "{'n0,'n1} ((fin 'n0,fin 'n1,'n1 \<ge> 'n0,'n0 \<ge> 1,(1 + 'n0) \<ge> 'n1) =?> (((['n0][64]) \<Rightarrow> ((['n0][64]) \<Rightarrow> ([2 * 'n0][64]))) \<Rightarrow> (((['n1][64]) \<Rightarrow> ((['n1][64]) \<Rightarrow> ([2 * 'n1][64]))) \<Rightarrow> ((['n0 + 'n1][64]) \<Rightarrow> ((['n0 + 'n1][64]) \<Rightarrow> ([2 * ('n0 + 'n1)][64]))))))" where
"kstep m0 m1 a b \<equiv> 
  let
    a0 = ((take`{'n0,'n1,[64]} a) : (['n0][64]));
    a1 = ((drop`{'n0,'n1,[64]} a) : (['n1][64]));
    b0 = ((take`{'n0,'n1,[64]} b) : (['n0][64]));
    b1 = ((drop`{'n0,'n1,[64]} b) : (['n1][64]));
    ta = (((a0 #`{'n0,'n1 - 'n0,[64]} (zero`{['n1 - 'n0][64]})) ^`{['n1][64]} a1) : (['n1][64]));
    tb = (((b0 #`{'n0,'n1 - 'n0,[64]} (zero`{['n1 - 'n0][64]})) ^`{['n1][64]} b1) : (['n1][64]));
    z0 = ((m0`{} a0 b0) : ([2 * 'n0][64]));
    z2 = ((m1`{} a1 b1) : ([2 * 'n1][64]));
    mid = ((((m1`{} ta tb) ^`{[2 * 'n1][64]} (z0 #`{2 * 'n0,2 * ('n1 - 'n0),[64]} (zero`{[2 * ('n1 - 'n0)][64]}))) ^`{[2 * 'n1][64]} z2) : ([2 * 'n1][64]))
  in ((z0 #`{2 * 'n0,2 * 'n1,[64]} z2) ^`{[2 * ('n0 + 'n1)][64]} ((zero`{['n0][64]}) #`{'n0,(2 * 'n1) + 'n0,[64]} (mid #`{2 * 'n1,'n0,[64]} (zero`{['n0][64]}))))"

end
end
