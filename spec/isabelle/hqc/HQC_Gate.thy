theory HQC_Gate
  imports HQC_P1 HQC_P3 HQC_P5
begin

text \<open>Build-time gate: the three vmul theorems depend on no oracle and no proof hole. In particular
  no \<open>by eval\<close> (code generator) and no \<open>sorry\<close> anywhere in their dependency cone.\<close>

ML \<open>
  let
    fun check nm th =
      (if Thm_Deps.has_skip_proof [th] then error ("ORACLE GATE: " ^ nm ^ " depends on a proof hole") else ();
       case Thm_Deps.all_oracles [th] of
         [] => writeln ("ORACLE GATE: " ^ nm ^ " has no oracles")
       | os => error ("ORACLE GATE: " ^ nm ^ " depends on [" ^
                      commas (map (fn ((n, _), _) => n) os) ^ "]"))
  in
    check "HQC_P1.vmul_correct" @{thm HQC_P1.vmul_correct};
    check "HQC_P3.vmul_correct" @{thm HQC_P3.vmul_correct};
    check "HQC_P5.vmul_correct" @{thm HQC_P5.vmul_correct}
  end
\<close>

end
