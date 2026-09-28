(* Offered as a patch to AFP CRYSTALS-Kyber (Katharina Kreuzer).

   kyber_ntt's psi_properties assumes BOTH "psi^2 = omega" and "psi^n = -1" (NTT_Scheme.thy:28).
   The second is redundant: it follows from the first together with omega_properties and
   n = 2^n', n' > 0.

   Stated as a standalone lemma over an arbitrary field, deliberately NOT inside kyber_ntt. Proving
   it in that locale would prove nothing, because the locale assumes the conclusion, and a
   derivation that may silently use the fact it claims to derive is not a derivation. The corollary
   at the end then instantiates it at the locale's own parameters. *)
theory Kyber_Psi_Derived
  imports "CRYSTALS-Kyber.NTT_Scheme"
begin

section \<open>The derivation, with no locale assumption in scope\<close>

lemma psi_pow_n_from_omega:
  fixes \<psi> \<omega> :: "'a :: field"
  assumes sq:      "\<psi>^2 = \<omega>"
      and om_one:  "\<omega>^m = 1"
      and minimal: "\<And>k. \<omega>^k = 1 \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> k \<ge> m"
      and m_even:  "even m"
      and m_pos:   "m > 1"
    shows "\<psi>^m = -1"
proof -
  have "\<psi>^(2*m) = (\<psi>^2)^m" by (simp add: power_mult)
  also have "\<dots> = \<omega>^m" by (simp add: sq)
  finally have two_m: "\<psi>^(2*m) = 1" using om_one by simp
  have sqr: "(\<psi>^m)^2 = 1"
    using two_m by (simp add: power_mult[symmetric] mult.commute)
  have "(\<psi>^m - 1) * (\<psi>^m + 1) = (\<psi>^m)^2 - 1"
    by (simp add: algebra_simps power2_eq_square)
  also have "\<dots> = 0" using sqr by simp
  finally have disj: "\<psi>^m = 1 \<or> \<psi>^m = -1"
    by (auto simp add: eq_neg_iff_add_eq_0)
  moreover have "\<psi>^m \<noteq> 1"
  proof
    assume a: "\<psi>^m = 1"
    have half: "2 * (m div 2) = m" using m_even by simp
    have "\<omega>^(m div 2) = (\<psi>^2)^(m div 2)" by (simp add: sq)
    also have "\<dots> = \<psi>^(2 * (m div 2))" by (simp add: power_mult)
    also have "\<dots> = \<psi>^m" by (simp only: half)
    finally have one: "\<omega>^(m div 2) = 1" using a by simp
    have nz: "m div 2 \<noteq> 0" using m_pos by simp
    from minimal[OF one nz] have "m div 2 \<ge> m" .
    thus False using m_pos by simp
  qed
  ultimately show ?thesis by blast
qed

section \<open>Instantiated at the entry's own parameters\<close>

text \<open>With the lemma above available, \<open>psi_properties\<close>'s second conjunct can be dropped from
\<open>kyber_ntt\<close> and recovered here. The hypotheses are exactly \<open>psi_properties(1)\<close>,
\<open>omega_properties(1)\<close>, \<open>omega_properties(3)\<close>, and evenness of \<open>n\<close> from \<open>n_powr_2\<close> with
\<open>n'_gr_0\<close>.\<close>

context kyber_ntt
begin

lemma n_even_nat': "even (nat n)"
  using n_powr_2 n'_gr_0 by (simp add: nat_power_eq)

corollary psi_pow_n_recovered: "\<psi>^(nat n) = -1"
proof (rule psi_pow_n_from_omega[where \<omega> = \<omega>])
  show "\<psi>^2 = \<omega>" by (rule psi_properties(1))
  show "\<omega>^(nat n) = 1" using omega_properties(1) by simp
  show "\<And>k. \<omega>^k = 1 \<Longrightarrow> k \<noteq> 0 \<Longrightarrow> k \<ge> nat n" using omega_properties(3) by simp
  show "even (nat n)" by (rule n_even_nat')
  show "nat n > 1" using n_gt_1 by simp
qed

end

end
