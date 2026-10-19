theory Reduce_AC2 imports AutoCorres2.AutoCorres Assay.Assay_Equivalence begin

text \<open>PQClean's reduce.c relies on arithmetic right shift of negative values (caddq), which C
  leaves implementation-defined; clang implements it arithmetically. AutoCorres2 guards it as
  undefined unless told otherwise.\<close>
declare [[arithmetic_right_shift]]

install_C_file "pp_reduce.c"

text \<open>montgomery_reduce narrows an unsigned 64-bit product to int32. AutoCorres2's default signed
  word abstraction turns that into a guarded signed multiply that fails for almost every input,
  although C has no undefined behaviour there; without signed word abstraction the guards are
  exactly C's int64 overflow conditions.\<close>
autocorres [no_signed_word_abs = PQCLEAN_MLDSA44_CLEAN_montgomery_reduce] "pp_reduce.c"

end
