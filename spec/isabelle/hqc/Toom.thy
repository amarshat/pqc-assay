theory "Toom"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition pxor :: "{'n} ((fin 'n,'n \<ge> 1) =?> ((['n][64]) \<Rightarrow> (['n][64])))" where
"pxor t \<equiv> drop`{1,'n,[64]} (scanl`{'n,[64],[64]} (\<lblot>^`{[64]}\<rblot>) (zero`{[64]}) t)"

cryptol_definition tQ2 :: "{'p} ((fin 'p) =?> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> ([4 + (2 * 'p)][64]))))" where
"tQ2 p0 p2 \<equiv> (drop`{1,3 + (2 * 'p),[64]} (p2 ^`{[4 + (2 * 'p)][64]} p0)) #`{3 + (2 * 'p),1,[64]} (list_to_seq [(zero`{[64]}) : ([64])] :: [1][64])"

cryptol_definition tD2 :: "{'p} ((fin 'p,'p \<ge> 1) =?> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> ([4 + (2 * 'p)][64]))))))" where
"tD2 p0 p2 p3 p4 \<equiv> (take`{2 * 'p,4,[64]} (pxor`{4 + (2 * 'p)} (((((tQ2`{'p} p0 p2) ^`{[4 + (2 * 'p)][64]} p3) ^`{[4 + (2 * 'p)][64]} p2) ^`{[4 + (2 * 'p)][64]} p4) ^`{[4 + (2 * 'p)][64]} (take`{4 + (2 * 'p),3,[64]} ((list_to_seq [(zero`{[64]}) : ([64]),(zero`{[64]}) : ([64]),(zero`{[64]}) : ([64])] :: [3][64]) #`{3,4 + (2 * 'p),[64]} p4))))) #`{2 * 'p,4,[64]} (zero`{[4][64]})"

cryptol_definition tD3 :: "{'p} ((fin 'p,'p \<ge> 1) =?> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> ([4 + (2 * 'p)][64]))))))" where
"tD3 w1 p0 p2 p3 \<equiv> (take`{2 * 'p,4,[64]} (pxor`{4 + (2 * 'p)} ((drop`{1,3 + (2 * 'p),[64]} (((p3 ^`{[4 + (2 * 'p)][64]} p2) ^`{[4 + (2 * 'p)][64]} w1) ^`{[4 + (2 * 'p)][64]} p0)) #`{3 + (2 * 'p),1,[64]} (list_to_seq [(zero`{[64]}) : ([64])] :: [1][64])))) #`{2 * 'p,4,[64]} (zero`{[4][64]})"

cryptol_definition tE1 :: "{'p} ((fin 'p,'p \<ge> 1) =?> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> ([4 + (2 * 'p)][64])))))))" where
"tE1 w1 p0 p2 p3 p4 \<equiv> ((w1 ^`{[4 + (2 * 'p)][64]} p0) ^`{[4 + (2 * 'p)][64]} (tD2`{'p} p0 p2 p3 p4)) ^`{[4 + (2 * 'p)][64]} p4"

cryptol_definition tE2 :: "{'p} ((fin 'p,'p \<ge> 1) =?> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> ([4 + (2 * 'p)][64])))))))" where
"tE2 w1 p0 p2 p3 p4 \<equiv> (tD2`{'p} p0 p2 p3 p4) ^`{[4 + (2 * 'p)][64]} (tD3`{'p} w1 p0 p2 p3)"

cryptol_definition tR :: "{'p} ((fin 'p) =?> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> (([4 + (2 * 'p)][64]) \<Rightarrow> ([4 + (6 * 'p)][64])))))))" where
"tR w0 w1 w2 w3 w4 \<equiv> 
  let
    r0 = ((w0 #`{4 + (2 * 'p),8 + (4 * 'p),[64]} (zero`{[8 + (4 * 'p)][64]})) : ([12 + ((2 * 'p) + (4 * 'p))][64]));
    r1 = (((zero`{['p][64]}) #`{'p,12 + ((2 * 'p) + (3 * 'p)),[64]} (w1 #`{4 + (2 * 'p),8 + (3 * 'p),[64]} (zero`{[8 + (3 * 'p)][64]}))) : ([12 + (((2 * 'p) + (3 * 'p)) + 'p)][64]));
    r2 = (((zero`{[2 * 'p][64]}) #`{2 * 'p,12 + (4 * 'p),[64]} (w2 #`{4 + (2 * 'p),8 + (2 * 'p),[64]} (zero`{[8 + (2 * 'p)][64]}))) : ([12 + ((2 * 'p) + (4 * 'p))][64]));
    r3 = (((zero`{[3 * 'p][64]}) #`{3 * 'p,12 + ((2 * 'p) + 'p),[64]} (w3 #`{4 + (2 * 'p),8 + 'p,[64]} (zero`{[8 + 'p][64]}))) : ([12 + ((3 * 'p) + ((2 * 'p) + 'p))][64]));
    r4 = (((zero`{[4 * 'p][64]}) #`{4 * 'p,12 + (2 * 'p),[64]} (w4 #`{4 + (2 * 'p),8,[64]} (zero`{[8][64]}))) : ([12 + ((4 * 'p) + (2 * 'p))][64]))
  in (take`{4 + (6 * 'p),(8 + ((4 * 'p) + (2 * 'p))) - (6 * 'p),[64]} ((((r0 ^`{[12 + ((4 * 'p) + (2 * 'p))][64]} r1) ^`{[12 + ((4 * 'p) + (2 * 'p))][64]} r2) ^`{[12 + ((4 * 'p) + (2 * 'p))][64]} r3) ^`{[12 + ((4 * 'p) + (2 * 'p))][64]} r4))"

cryptol_definition tU2 :: "{'p} ((fin 'p) =?> (([3 * 'p][64]) \<Rightarrow> ([2 + 'p][64])))" where
"tU2 a \<equiv> (drop`{2 * 'p,(3 * 'p) - (2 * 'p),[64]} a) #`{(3 * 'p) - (2 * 'p),(2 + ('p + (2 * 'p))) - (3 * 'p),[64]} (zero`{[(2 + ('p + (2 * 'p))) - (3 * 'p)][64]})"

cryptol_definition tU1 :: "{'p} ((fin 'p) =?> (([3 * 'p][64]) \<Rightarrow> ([2 + 'p][64])))" where
"tU1 a \<equiv> (take`{'p,'p,[64]} (drop`{'p,2 * 'p,[64]} a)) #`{'p,2,[64]} (zero`{[2][64]})"

cryptol_definition tU0 :: "{'p} ((fin 'p) =?> (([3 * 'p][64]) \<Rightarrow> ([2 + 'p][64])))" where
"tU0 a \<equiv> (take`{'p,(3 * 'p) - 'p,[64]} a) #`{'p,2,[64]} (zero`{[2][64]})"

cryptol_definition tS :: "{'p} ((fin 'p) =?> (([3 * 'p][64]) \<Rightarrow> ([2 + 'p][64])))" where
"tS a \<equiv> ((tU0`{'p} a) ^`{[2 + 'p][64]} (tU1`{'p} a)) ^`{[2 + 'p][64]} (tU2`{'p} a)"

cryptol_definition tY :: "{'p} ((fin 'p,'p \<ge> 1) =?> (([3 * 'p][64]) \<Rightarrow> ([2 + 'p][64])))" where
"tY a \<equiv> (take`{2 + 'p,1,[64]} ((list_to_seq [(zero`{[64]}) : ([64])] :: [1][64]) #`{1,2 + 'p,[64]} (tU1`{'p} a))) ^`{[2 + 'p][64]} (take`{2 + 'p,2,[64]} ((list_to_seq [(zero`{[64]}) : ([64]),(zero`{[64]}) : ([64])] :: [2][64]) #`{2,2 + 'p,[64]} (tU2`{'p} a)))"

cryptol_definition toom3 :: "{'p} ((fin 'p,'p \<ge> 4) =?> ((([2 + 'p][64]) \<Rightarrow> (([2 + 'p][64]) \<Rightarrow> ([4 + (2 * 'p)][64]))) \<Rightarrow> (([3 * 'p][64]) \<Rightarrow> (([3 * 'p][64]) \<Rightarrow> ([4 + (6 * 'p)][64])))))" where
"toom3 m a b \<equiv> 
  let
    w1 = ((m`{} (tS`{'p} b) (tS`{'p} a)) : ([4 + (2 * 'p)][64]));
    p3 = ((m`{} ((tS`{'p} a) ^`{[2 + 'p][64]} (tY`{'p} a)) ((tS`{'p} b) ^`{[2 + 'p][64]} (tY`{'p} b))) : ([4 + (2 * 'p)][64]));
    p2 = ((m`{} ((tY`{'p} a) ^`{[2 + 'p][64]} (tU0`{'p} a)) ((tY`{'p} b) ^`{[2 + 'p][64]} (tU0`{'p} b))) : ([4 + (2 * 'p)][64]));
    p4 = ((m`{} (tU2`{'p} a) (tU2`{'p} b)) : ([4 + (2 * 'p)][64]));
    p0 = ((m`{} (tU0`{'p} a) (tU0`{'p} b)) : ([4 + (2 * 'p)][64]))
  in (tR`{'p} p0 (tE1`{'p} w1 p0 p2 p3 p4) (tE2`{'p} w1 p0 p2 p3 p4) (tD3`{'p} w1 p0 p2 p3) p4)"

end
end
