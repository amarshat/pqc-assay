theory "Fold"
imports "Cryptol.Cryptol"
begin

context includes cryptol_translation_syntax begin
cryptol_definition fromBits :: "{'w} ((fin 'w) =?> (([64 * 'w]) \<Rightarrow> (['w][64])))" where
"fromBits v \<equiv> reverse`{'w,[64]} (split`{'w,64,Bit} v)"

cryptol_definition toBits :: "{'w} ((fin 'w) =?> ((['w][64]) \<Rightarrow> ([64 * 'w])))" where
"toBits x \<equiv> join`{'w,64,Bit} (reverse`{'w,[64]} x)"

cryptol_definition fold :: "{'n,'w} ((fin 'n,fin 'w,(64 * 'w) \<ge> 'n,'n \<ge> 1) =?> (([2 * 'w][64]) \<Rightarrow> (['w][64])))" where
"fold p \<equiv> 
  let
    v = ((toBits`{2 * 'w} p) : ([128 * 'w]));
    lowMask = ((complement`{[64 * 'w]} ((complement`{[64 * 'w]} (zero`{[64 * 'w]})) <<`{64 * 'w,Integer,Bit} (number`{'n,Integer}))) : ([64 * 'w]))
  in (fromBits`{'w} ((drop`{64 * 'w,64 * 'w,Bit} (v ^`{[128 * 'w]} (v >>`{128 * 'w,Integer,Bit} (number`{'n,Integer})))) &&`{[64 * 'w]} lowMask))"

cryptol_definition reduced :: "{'n,'w} ((fin 'n,fin 'w,(64 * 'w) \<ge> 'n) =?> ((['w][64]) \<Rightarrow> Bit))" where
"reduced x \<equiv> ((toBits`{'w} x) >>`{64 * 'w,Integer,Bit} (number`{'n,Integer})) ==`{[64 * 'w]} (zero`{[64 * 'w]})"

end
end
