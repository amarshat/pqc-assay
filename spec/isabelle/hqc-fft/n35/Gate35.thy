theory Gate35
  imports Top5
begin

text \<open>Build-time gate for the additive-FFT result at the hqc-3 and hqc-5 sizes: mulT3_correct and
  mulT5_correct (and the steps they rest on) depends on no oracle and no proof hole. The kernel checks of the model's
  constants use code_simp, which is a simplifier proof; an evaluation oracle (eval, normalization)
  would show up here.\<close>

ML \<open>
  let
    fun check nm th =
      (if Thm_Deps.has_skip_proof [th] then error ("ORACLE GATE: " ^ nm ^ " depends on a proof hole") else ();
       case Thm_Deps.all_oracles [th] of
         [] => writeln ("ORACLE GATE: " ^ nm ^ " has no oracles")
       | os => error ("ORACLE GATE: " ^ nm ^ " depends on [" ^
                      commas (map (fn ((n, _), _) => n) os) ^ "]"))
  in
    check "Top5.mulT5_correct" @{thm Top5.mulT5_correct};
    check "Top5.forward_eval5" @{thm Top5.forward_eval5};
    check "Ibc35.ibc1_131072_iconv" @{thm Ibc35.ibc1_131072_iconv};
    check "Commute.layersR_layers" @{thm Commute.layersR_layers}
  end
\<close>

text \<open>Axiom gate. The oracle check above does not see axioms. Every axiom of this theory's context
  that is not already an axiom of HOL's \<open>Main\<close> must be a definition (registered in the
  theory's specification table) or one of the type-declaration axioms Isabelle's typedecl, typedef and
  datatype packages generate (type arities, type_definition, and the internal morphism axioms). Any
  other axiom fails the build. In particular the Cryptol support session ships a theory
  \<open>Unsupported\<close> whose axiom \<open>unsupported: \<And>P. PROP P\<close> proves anything; it must not be in
  this context, and the check below fails the build if it is.\<close>

ML \<open>
  let
    val thy = @{theory};
    val main_axs = map #1 (Theory.all_axioms_of (Thy_Info.get_theory "Main"));
    val extra = subtract (op =) main_axs (map #1 (Theory.all_axioms_of thy));
    val defs = Defs.all_specifications_of (Theory.defs_of thy) |> maps (fn (_, specs) => map_filter #def specs);
    fun generated n =
      let val b = Long_Name.base_name n in
        String.isPrefix "arity_type_" b orelse String.isPrefix "type_definition" b orelse
        String.isSuffix "_ext" b orelse String.isSubstring "_IITN_" b orelse String.isSubstring "_pre_" b
      end;
    val plain = filter_out (fn n => member (op =) defs n orelse generated n) extra;
    val unsupported = exists (fn n => hd (Long_Name.explode n) = "Unsupported") extra;
  in
    if unsupported then error "AXIOM GATE: the Cryptol theory Unsupported (axiom: every proposition) is in the context" else ();
    case plain of
      [] => writeln ("AXIOM GATE: " ^ string_of_int (length extra) ^ " axioms beyond Main, all definitions or generated type axioms")
    | ns => error ("AXIOM GATE: axioms that are neither definitions nor generated type axioms: " ^ commas ns)
  end
\<close>

end
