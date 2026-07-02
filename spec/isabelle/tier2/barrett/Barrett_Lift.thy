theory Barrett_Lift
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition smallReduce :: "([32]) \<Rightarrow> ([32])" where
"smallReduce x \<equiv> if x >=`{[32]} (0x7fe001 :: [32]) then (x -`{[32]} (0x7fe001 :: [32])) else coerce x"

cryptol_definition q :: "[128]" where
"q  \<equiv> 0x7fe001 :: [128]"

cryptol_definition barrettMult :: "[128]" where
"barrettMult  \<equiv> 0x802007 :: [128]"

cryptol_definition barrettBV :: "([64]) \<Rightarrow> ([32])" where
"barrettBV x \<equiv> 
  let
    xll = ((zext`{128,64} x) : ([128]));
    prod = ((xll *`{[128]} barrettMult) : ([128]));
    quotient = ((prod >>`{128,Integer,Bit} (46 :: Integer)) : ([128]));
    remainder = ((xll -`{[128]} (quotient *`{[128]} q)) : ([128]))
  in (smallReduce`{} (drop`{96,32,Bit} remainder))"

cryptol_definition barrettBV_bridge :: "([64]) \<Rightarrow> Bit" where
"barrettBV_bridge x \<equiv> (x <`{[64]} ((0x1 :: [64]) <<`{64,Integer,Bit} (46 :: Integer))) \<longrightarrow> ((barrettBV`{} x) ==`{[32]} (drop`{96,32,Bit} ((zext`{128,64} x) %`{[128]} q)))"

end
end
