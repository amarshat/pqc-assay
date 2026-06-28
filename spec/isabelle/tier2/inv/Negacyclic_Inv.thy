(* Tier-2, inverse leg, sub-step 1: the negacyclic transform is invertible mod q.

   Bounded and self-contained: reuses the AFP cyclic round-trip theorems
   (ntt_correct: INTT o NTT = n.id, inv_ntt_correct: NTT o INTT = n.id) and the
   negacyclic<->cyclic twist already proven in Negacyclic_NTT. The inverse
   negacyclic map is AFP INTT post-composed with the untwist (multiply coord j
   by (psi*mu)^j). psi is a unit because psi^2 = omega and mu*omega = 1, so
   psi*(psi*mu) = 1 -- no field `inverse` and no extra locale assumption needed.

   Result: INNTT o NNTT = NNTT o INNTT = n.id (n a unit mod q), i.e. NNTT is a
   bijection on length-n vectors with inverse (n^-1).INNTT. This is the algebra
   the montgomery inverse-butterfly bridge (sub-step 2) composes against. *)
theory Negacyclic_Inv
  imports "Tier2_Base.Negacyclic_NTT"
begin

context negacyclic
begin

section \<open>untwist: the pointwise inverse of twist\<close>

definition untwist :: "'a mod_ring list \<Rightarrow> 'a mod_ring list" where
  "untwist xs = map (\<lambda>j. (\<psi>*\<mu>)^j * (xs ! j)) [0..<n]"

lemma length_untwist [simp]: "length (untwist xs) = n"
  by (simp add: untwist_def)

lemma untwist_nth [simp]: "j < n \<Longrightarrow> untwist xs ! j = (\<psi>*\<mu>)^j * (xs ! j)"
  by (simp add: untwist_def)

text \<open>\<open>\<psi>\<close> is a unit: \<open>(\<psi>\<mu>)\<cdot>\<psi> = \<psi>^2\<mu> = \<omega>\<mu> = 1\<close>, hence the exponentwise cancellation.\<close>
lemma psiinv_cancel: "(\<psi>*\<mu>) * \<psi> = 1"
  by (metis mult.assoc mult.commute mu_properties psi_sq)

lemma psiinv_pow_cancel: "((\<psi>*\<mu>)^j) * (\<psi>^j) = 1"
proof -
  have "((\<psi>*\<mu>)^j) * (\<psi>^j) = ((\<psi>*\<mu>) * \<psi>)^j"
    by (simp add: power_mult_distrib)
  also have "\<dots> = 1" by (simp add: psiinv_cancel)
  finally show ?thesis .
qed

lemma untwist_twist [simp]:
  assumes "length xs = n"
  shows "untwist (twist xs) = xs"
proof (rule nth_equalityI)
  show "length (untwist (twist xs)) = length xs" using assms by simp
next
  fix i assume "i < length (untwist (twist xs))"
  hence i: "i < n" by simp
  have "untwist (twist xs) ! i = ((\<psi>*\<mu>)^i * \<psi>^i) * (xs ! i)"
    using i by (simp add: mult.assoc mult.left_commute)
  also have "\<dots> = xs ! i" by (simp add: psiinv_pow_cancel)
  finally show "untwist (twist xs) ! i = xs ! i" .
qed

lemma twist_untwist:
  assumes "length xs = n"
  shows "twist (untwist xs) = xs"
proof (rule nth_equalityI)
  show "length (twist (untwist xs)) = length xs" using assms by simp
next
  fix i assume "i < length (twist (untwist xs))"
  hence i: "i < n" by simp
  have "twist (untwist xs) ! i = (\<psi>^i * (\<psi>*\<mu>)^i) * (xs ! i)"
    using i by (simp add: mult.assoc mult.left_commute)
  also have "\<dots> = xs ! i"
    by (metis psiinv_pow_cancel mult.assoc mult.commute mult.left_neutral)
  finally show "twist (untwist xs) ! i = xs ! i" .
qed

section \<open>The inverse negacyclic transform and its round-trip with NNTT\<close>

definition INNTT :: "'a mod_ring list \<Rightarrow> 'a mod_ring list" where
  "INNTT ys = untwist (INTT ys)"

text \<open>\<open>INNTT \<circ> NNTT = n\<cdot>id\<close>: AFP @{thm [source] ntt_correct} on the twist, then untwist.\<close>
theorem INNTT_NNTT:
  assumes len: "length xs = n"
  shows "INNTT (NNTT xs) = map (\<lambda>x. of_int_mod_ring (int n) * x) xs"
proof -
  let ?c = "of_int_mod_ring (int n) :: 'a mod_ring"
  have step: "INTT (NTT (twist xs)) = map (\<lambda>x. ?c * x) (twist xs)"
    using ntt_correct[OF length_twist] by simp
  show ?thesis
  proof (rule nth_equalityI)
    show "length (INNTT (NNTT xs)) = length (map (\<lambda>x. ?c * x) xs)"
      using len by (simp add: INNTT_def)
  next
    fix i assume "i < length (INNTT (NNTT xs))"
    hence i: "i < n" by (simp add: INNTT_def)
    have "INNTT (NNTT xs) ! i = (\<psi>*\<mu>)^i * (?c * (\<psi>^i * (xs ! i)))"
      using i step by (simp add: INNTT_def NNTT_eq_NTT_twist)
    also have "\<dots> = ?c * (((\<psi>*\<mu>)^i * \<psi>^i) * (xs ! i))"
      by (simp add: mult.assoc mult.left_commute)
    also have "\<dots> = ?c * (xs ! i)"
      by (metis psiinv_pow_cancel mult.left_neutral)
    also have "\<dots> = map (\<lambda>x. ?c * x) xs ! i" using i len by simp
    finally show "INNTT (NNTT xs) ! i = map (\<lambda>x. ?c * x) xs ! i" .
  qed
qed

text \<open>The converse \<open>NNTT \<circ> INNTT = n\<cdot>id\<close> from AFP @{thm [source] inv_ntt_correct}.\<close>
theorem NNTT_INNTT:
  assumes len: "length ys = n"
  shows "NNTT (INNTT ys) = map (\<lambda>x. of_int_mod_ring (int n) * x) ys"
proof -
  have "NNTT (INNTT ys) = NTT (twist (untwist (INTT ys)))"
    by (simp add: INNTT_def NNTT_eq_NTT_twist)
  also have "twist (untwist (INTT ys)) = INTT ys"
    by (rule twist_untwist[OF length_INTT[OF len]])
  also have "NTT (INTT ys) = map (\<lambda>x. of_int_mod_ring (int n) * x) ys"
    using inv_ntt_correct[OF len] by simp
  finally show ?thesis .
qed

end

end
