(* Tier-2: the composed forward NTT computes the negacyclic transform.
   Reuses AFP Number_Theoretic_Transform (cyclic NTT + Cooley-Tukey FNTT_correct).
   Lives in the separate Tier2 session (not the Assay session); proof-hole-free. *)
theory Negacyclic_NTT
  imports "Number_Theoretic_Transform.Butterfly"
begin

section \<open>Bridge 1 — negacyclic transform = cyclic transform of the twisted input\<close>

text \<open>
  ML-DSA's NTT works in \<open>Z_q[x]/(x^n+1)\<close> (negacyclic), evaluating at the ODD
  powers \<open>\<psi>^(2k+1)\<close> of a primitive \<open>2n\<close>-th root \<open>\<psi>\<close>, whereas the AFP
  transform is cyclic (\<open>x^n-1\<close>, even powers \<open>\<omega>^k\<close>). The standard reduction:
  with \<open>\<psi>^2 = \<omega>\<close>, the negacyclic transform of \<open>x\<close> equals the cyclic transform
  of the twisted vector \<open>x[j] \<mapsto> \<psi>^j \<cdot> x[j]\<close>. This is pure root-of-unity
  algebra and needs only \<open>\<psi>^2 = \<omega>\<close> (primitivity is used later, for the inverse).
\<close>

locale negacyclic = ntt +
  fixes \<psi> :: "'a mod_ring"
  assumes psi_sq: "\<psi> * \<psi> = \<omega>"
begin

definition twist :: "'a mod_ring list \<Rightarrow> 'a mod_ring list" where
  "twist xs = map (\<lambda>j. \<psi>^j * (xs ! j)) [0..<n]"

definition nntt :: "'a mod_ring list \<Rightarrow> nat \<Rightarrow> 'a mod_ring" where
  "nntt xs kk = (\<Sum>j=0..<n. (xs ! j) * \<psi>^((2*kk+1)*j))"

definition "NNTT xs = map (nntt xs) [0..<n]"

lemma length_twist [simp]: "length (twist xs) = n"
  by (simp add: twist_def)

lemma twist_nth [simp]: "j < n \<Longrightarrow> twist xs ! j = \<psi>^j * (xs ! j)"
  by (simp add: twist_def)

text \<open>\<open>\<psi>^2 = \<omega>\<close> lifted to arbitrary even exponents.\<close>
lemma psi_pow_omega: "\<psi>^(2*m) = \<omega>^m"
  by (metis power_mult power2_eq_square psi_sq)

text \<open>The key identity: a negacyclic coefficient is a cyclic coefficient of the twist.\<close>
theorem nntt_eq_ntt_twist:
  shows "nntt xs kk = ntt (twist xs) kk"
proof -
  have "ntt (twist xs) kk = (\<Sum>j=0..<n. (twist xs ! j) * \<omega>^(kk*j))"
    by (simp add: ntt_def)
  also have "\<dots> = (\<Sum>j=0..<n. (xs ! j) * \<psi>^((2*kk+1)*j))"
  proof (rule sum.cong[OF refl])
    fix j assume "j \<in> {0..<n}"
    hence j: "j < n" by simp
    have "(twist xs ! j) * \<omega>^(kk*j) = (xs ! j) * (\<psi>^j * \<omega>^(kk*j))"
      using j by (simp add: mult.assoc mult.left_commute)
    also have "\<psi>^j * \<omega>^(kk*j) = \<psi>^j * \<psi>^(2*(kk*j))"
      by (simp add: psi_pow_omega)
    also have "\<dots> = \<psi>^(j + 2*(kk*j))"
      by (simp add: power_add)
    also have "j + 2*(kk*j) = (2*kk+1)*j" by (simp add: algebra_simps)
    finally show "(twist xs ! j) * \<omega>^(kk*j) = (xs ! j) * \<psi>^((2*kk+1)*j)"
      by simp
  qed
  also have "\<dots> = nntt xs kk" by (simp add: nntt_def)
  finally show ?thesis by simp
qed

corollary NNTT_eq_NTT_twist:
  "NNTT xs = NTT (twist xs)"
  by (simp add: NNTT_def NTT_def nntt_eq_ntt_twist)

end

section \<open>Bridge 1 + AFP Cooley-Tukey: negacyclic transform via the recursive FNTT\<close>

text \<open>
  Composing Bridge 1 with the AFP butterfly-correctness theorem @{thm [source]
  butterfly.FNTT_correct}: in the power-of-two setting the negacyclic transform is
  computed by the recursive Cooley-Tukey transform applied to the twisted input.
  The twist always has length \<open>n\<close>, so the length hypothesis of @{thm [source]
  butterfly.FNTT_correct} is discharged unconditionally.
\<close>

locale negacyclic_butterfly = negacyclic + butterfly
begin

theorem NNTT_eq_FNTT_twist:
  "NNTT xs = FNTT (twist xs)"
  using FNTT_correct[of "twist xs"] length_twist
  by (simp add: NNTT_eq_NTT_twist)

end

end
