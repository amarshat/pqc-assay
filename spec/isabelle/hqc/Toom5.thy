theory "Toom5"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition pxorv :: "{'n} ((fin 'n,'n \<ge> 1) =?> (([4 * 'n][64]) \<Rightarrow> ([4 * 'n][64])))" where
"pxorv t \<equiv> join`{'n,4,[64]} (drop`{1,'n,[4][64]} (scanl`{'n,[4][64],[4][64]} (\<lblot>^`{[4][64]}\<rblot>) (zero`{[4][64]}) (split`{'n,4,[64]} t)))"

cryptol_definition vQ1 :: "([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> ([640][64]))" where
"vQ1 w1 p0 \<equiv> w1 ^`{[640][64]} ((take`{624,16,[64]} p0) #`{624,16,[64]} (zero`{[16][64]}))"

cryptol_definition vD3 :: "([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> ([640][64]))))" where
"vD3 w1 p0 p2 p3 \<equiv> pxorv`{160} ((drop`{4,636,[64]} ((p3 ^`{[640][64]} p2) ^`{[640][64]} (vQ1`{} w1 p0))) #`{636,4,[64]} (zero`{[4][64]}))"

cryptol_definition vQ2 :: "([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> ([640][64]))" where
"vQ2 p0 p2 \<equiv> (drop`{4,636,[64]} (p2 ^`{[640][64]} p0)) #`{636,4,[64]} (zero`{[4][64]})"

cryptol_definition vD2 :: "([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> ([640][64]))))" where
"vD2 p0 p2 p3 p4 \<equiv> pxorv`{160} (((((vQ2`{} p0 p2) ^`{[640][64]} p3) ^`{[640][64]} p2) ^`{[640][64]} p4) ^`{[640][64]} ((zero`{[12][64]}) #`{12,628,[64]} ((take`{624,16,[64]} p4) #`{624,4,[64]} (zero`{[4][64]}))))"

cryptol_definition vE2 :: "([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> ([640][64])))))" where
"vE2 w1 p0 p2 p3 p4 \<equiv> (vD2`{} p0 p2 p3 p4) ^`{[640][64]} (vD3`{} w1 p0 p2 p3)"

cryptol_definition vE1 :: "([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> ([640][64])))))" where
"vE1 w1 p0 p2 p3 p4 \<equiv> ((vQ1`{} w1 p0) ^`{[640][64]} (vD2`{} p0 p2 p3 p4)) ^`{[640][64]} p4"

cryptol_definition vR :: "([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> (([640][64]) \<Rightarrow> ([1872][64])))))" where
"vR w0 w1 w2 w3 w4 \<equiv> 
  let
    r0 = (((take`{624,16,[64]} w0) #`{624,1248,[64]} (zero`{[1248][64]})) : ([1872][64]));
    r1 = (((zero`{[312][64]}) #`{312,1560,[64]} ((take`{624,16,[64]} w1) #`{624,936,[64]} (zero`{[936][64]}))) : ([1872][64]));
    r2 = (((zero`{[624][64]}) #`{624,1248,[64]} (w2 #`{640,608,[64]} (zero`{[608][64]}))) : ([1872][64]));
    r3 = (((zero`{[936][64]}) #`{936,936,[64]} (w3 #`{640,296,[64]} (zero`{[296][64]}))) : ([1872][64]));
    r4 = (((zero`{[1248][64]}) #`{1248,624,[64]} (take`{624,16,[64]} w4)) : ([1872][64]))
  in ((((r0 ^`{[1872][64]} r1) ^`{[1872][64]} r2) ^`{[1872][64]} r3) ^`{[1872][64]} r4)"

cryptol_definition vU0 :: "([936][64]) \<Rightarrow> ([320][64])" where
"vU0 a \<equiv> (take`{312,624,[64]} a) #`{312,8,[64]} (zero`{[8][64]})"

cryptol_definition vU2 :: "([936][64]) \<Rightarrow> ([320][64])" where
"vU2 a \<equiv> (drop`{624,312,[64]} a) #`{312,8,[64]} (zero`{[8][64]})"

cryptol_definition vU1 :: "([936][64]) \<Rightarrow> ([320][64])" where
"vU1 a \<equiv> (take`{312,312,[64]} (drop`{312,624,[64]} a)) #`{312,8,[64]} (zero`{[8][64]})"

cryptol_definition vY :: "([936][64]) \<Rightarrow> ([320][64])" where
"vY a \<equiv> (take`{320,4,[64]} ((zero`{[4][64]}) #`{4,320,[64]} (vU1`{} a))) ^`{[320][64]} (take`{320,8,[64]} ((zero`{[8][64]}) #`{8,320,[64]} (vU2`{} a)))"

cryptol_definition vS :: "([936][64]) \<Rightarrow> ([320][64])" where
"vS a \<equiv> ((vU0`{} a) ^`{[320][64]} (vU1`{} a)) ^`{[320][64]} (vU2`{} a)"

cryptol_definition toom5 :: "(([320][64]) \<Rightarrow> (([320][64]) \<Rightarrow> ([640][64]))) \<Rightarrow> (([936][64]) \<Rightarrow> (([936][64]) \<Rightarrow> ([1872][64])))" where
"toom5 m a b \<equiv> 
  let
    w1 = ((m`{} (vS`{} b) (vS`{} a)) : ([640][64]));
    p3 = ((m`{} ((vS`{} a) ^`{[320][64]} (vY`{} a)) ((vS`{} b) ^`{[320][64]} (vY`{} b))) : ([640][64]));
    p2 = ((m`{} ((vY`{} a) ^`{[320][64]} (vU0`{} a)) ((vY`{} b) ^`{[320][64]} (vU0`{} b))) : ([640][64]));
    p4 = ((m`{} (vU2`{} a) (vU2`{} b)) : ([640][64]));
    p0 = ((m`{} (vU0`{} a) (vU0`{} b)) : ([640][64]))
  in (vR`{} p0 (vE1`{} w1 p0 p2 p3 p4) (vE2`{} w1 p0 p2 p3 p4) (vD3`{} w1 p0 p2 p3) p4)"

end
end
