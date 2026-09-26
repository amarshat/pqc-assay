(* v4 O8, first step: what poly_pointwise_montgomery means mod q.

   SAW proves the C equals the Cryptol `pointwise` bit for bit, on the -fwrapv module, for ALL
   inputs. That is an equality of 32-bit words and says nothing on its own about arithmetic mod q.
   The mod-q reading needs montgomery_reduce's contract, whose precondition is mont_input_ok, and
   an arbitrary int32 product reaches 2^62, far outside the +/-2^31*q window. So the bridge below
   carries a bound hypothesis that the SAW leg does not.

   That asymmetry is the point of this file: "verified in SAW" and "computes the product mod q" are
   different statements here, and only the second is what the convolution theorem needs. The bound
   that makes them meet is the natural one, coefficients centered below q, and it holds with room:
   q^2 = 70231389093889 against 2^31*q = 17996808470921216. *)
theory Pointwise_Bridge
  imports Mont_Bridge
begin

text \<open>The precondition, discharged from the bound the transforms actually deliver. \<open>|a|,|b| < q\<close>
gives \<open>|a*b| < q^2\<close>, and \<open>q^2 < 2^31*q\<close> because \<open>q < 2^31\<close>. Stated outside the Cryptol syntax
context, where \<open>^\<close> is ordinary HOL exponentiation.\<close>

lemma mont_input_ok_of_abs_lt_q:
  assumes a: "\<bar>a\<bar> < 8380417" and b: "\<bar>b\<bar> < 8380417"
  shows "mont_input_ok (a * b)"
proof -
  have "\<bar>a * b\<bar> = \<bar>a\<bar> * \<bar>b\<bar>" by (simp add: abs_mult)
  also have "\<dots> < 8380417 * 8380417"
    using a b by (intro mult_strict_mono) auto
  finally have lt: "\<bar>a * b\<bar> < 8380417 * 8380417" .
  have pw: "(2::int)^31 * 8380417 = 17996808470921216" by simp
  have "(8380417::int) * 8380417 < 17996808470921216" by simp
  with lt have "\<bar>a * b\<bar> < (2::int)^31 * 8380417" by (simp add: pw)
  thus ?thesis unfolding mont_input_ok_def MLDSA_NTT_Spec.q_def by linarith
qed

context includes cryptol_translation_syntax begin

text \<open>Coefficientwise unfolding of the lifted definition: \<open>pointwise\<close> is a map over a zip, so its
\<open>k\<close>-th entry is \<open>montgomery_reduce\<close> of the sign-extended product.\<close>

lemma nth_seq_pointwise:
  assumes k: "k < 256"
  shows "nth_seq (pointwise x y) k
           = montgomery_reduce (sext64 (nth_seq x k) * sext64 (nth_seq y k))"
  using k by (simp add: pointwise_def)

text \<open>The mod-q meaning of the pointwise multiply. The Montgomery factor \<open>2^32\<close> it leaves behind is
exactly what \<open>invntt_tomont\<close>'s \<open>f = mont^2/256\<close> tail is there to cancel, which is the next
obligation.\<close>

theorem pointwise_bridge:
  assumes k: "k < 256"
    and ok: "mont_input_ok (sint_seq (nth_seq x k) * sint_seq (nth_seq y k))"
  shows "(4294967296 * sint_seq (nth_seq (pointwise x y) k)) mod 8380417
           = (sint_seq (nth_seq x k) * sint_seq (nth_seq y k)) mod 8380417"
proof -
  have ok2: "mont_input_ok (sint_seq (sext64 (nth_seq x k) * sext64 (nth_seq y k)))"
    using ok by (simp add: sint_sext64_mult)
  show ?thesis
    using mont_mod_q[OF ok2] by (simp add: nth_seq_pointwise[OF k] sint_sext64_mult)
qed

text \<open>The form a caller gets: under the centered bound the transforms deliver, the C model's
pointwise product is the coefficient product divided by the Montgomery factor, mod q.\<close>

corollary pointwise_bridge_bounded:
  assumes k: "k < 256"
    and bx: "\<bar>sint_seq (nth_seq x k)\<bar> < 8380417"
    and by': "\<bar>sint_seq (nth_seq y k)\<bar> < 8380417"
  shows "(4294967296 * sint_seq (nth_seq (pointwise x y) k)) mod 8380417
           = (sint_seq (nth_seq x k) * sint_seq (nth_seq y k)) mod 8380417"
  by (rule pointwise_bridge[OF k mont_input_ok_of_abs_lt_q[OF bx by']])

end

end
