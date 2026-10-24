theory HQC_Gate
  imports HQC_P1 HQC_P3 HQC_P5 AVX_P1 AVX_P3 AVX_P5
begin

text \<open>Build-time gate: the vmul theorems (reference) and vmulA theorems (AVX2) depend on no oracle and no proof hole. In particular
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
    check "HQC_P5.vmul_correct" @{thm HQC_P5.vmul_correct};
    check "AVX_P1.vmulA_correct" @{thm AVX_P1.vmulA_correct};
    check "AVX_P3.vmulA_correct" @{thm AVX_P3.vmulA_correct};
    check "AVX_P5.km320_correct" @{thm AVX_P5.km320_correct}
  end
\<close>

end
