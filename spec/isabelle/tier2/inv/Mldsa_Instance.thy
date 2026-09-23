(* v4 O9: a model of negacyclic_butterfly at the ML-DSA parameters.

   Everything in Negacyclic_Conv is proven inside the locale. A theorem proven in a locale with no
   model is vacuous, and nothing in this development or in the AFP NTT entry it builds on exhibits
   one. This file builds the ingredients at q = 8380417, n = 256, omega = 3073009, psi = 1753.

   The AFP CRYSTALS-Kyber entry establishes its root of unity by checking all 255 lower powers with
   `by eval`, the Code_Runtime oracle. Two facts suffice instead: the order divides 256 because
   omega^256 = 1, and does not divide 128 because omega^128 = -1, so it is exactly 256. Both come
   from an eight-step squaring chain with explicit constants, so nothing here is an oracle, and the
   primality goes through Pratt rather than `by eval` for the same reason.

   STATUS: the type, its instances and the squaring chain are proven. The order-minimality lemma
   and the interpretation itself are not done yet, so O9 is NOT closed and Negacyclic_Conv's
   results remain conditional. See docs/ROADMAP.md v4. *)
theory Mldsa_Instance
  imports Negacyclic_Conv "Pratt_Certificate.Pratt_Certificate"
begin


typedef fin8380417 = "{0..<8380417::int}"
  morphisms fin8380417_rep fin8380417_abs
  by (rule_tac x = 0 in exI, simp)
setup_lifting type_definition_fin8380417

lemma CARD_fin8380417 [simp]: "CARD (fin8380417) = 8380417"
  unfolding type_definition.card [OF type_definition_fin8380417] by simp

instantiation fin8380417 :: finite begin
instance proof
  show "finite (UNIV :: fin8380417 set)"
    unfolding type_definition.univ [OF type_definition_fin8380417] by auto
qed
end

instantiation fin8380417 :: nontriv begin
instance by (standard, simp)
end

lemma prime_8380417: "prime (8380417::nat)" by (pratt (silent))

text \<open>Discharged by \<open>blast\<close> against the Pratt result, not by \<open>simp\<close>: handed
\<open>prime (8380417::nat)\<close> as a simp goal the simplifier tries to decide it by trial division and does
not come back.\<close>
instantiation fin8380417 :: prime_card begin
instance proof
  show "prime CARD(fin8380417)" unfolding CARD_fin8380417 using prime_8380417 by blast
qed
end

abbreviation Q :: int where "Q \<equiv> 8380417"

text \<open>Both go through \<open>transfer\<close> to the representative, where they are \<open>mod_mult_eq\<close> and
\<open>mod_mod_trivial\<close>. Neither uses metis: applied to the numeral-carrying goals further down, metis
ran for 57 minutes without closing.\<close>

lemma omr_mult: "(of_int_mod_ring (a*b) :: 'b :: finite mod_ring)
                   = of_int_mod_ring a * of_int_mod_ring b"
  by (transfer, simp add: mod_mult_eq)

lemma omr_mod: "(of_int_mod_ring a :: 'b :: finite mod_ring) = of_int_mod_ring (a mod CARD('b))"
  by (transfer, simp)

lemma sq: "(of_int_mod_ring a :: fin8380417 mod_ring)^2 = of_int_mod_ring ((a*a) mod Q)"
proof -
  have "(of_int_mod_ring a :: fin8380417 mod_ring)^2 = of_int_mod_ring a * of_int_mod_ring a"
    by (simp add: power2_eq_square)
  also have "\<dots> = of_int_mod_ring (a*a)" by (rule omr_mult[symmetric])
  also have "\<dots> = of_int_mod_ring ((a*a) mod Q)" using omr_mod[where 'b=fin8380417] by simp
  finally show ?thesis .
qed

text \<open>One squaring step. The only thing left for the caller is integer arithmetic on a product of
two seven-digit numbers, which simp does directly.\<close>
lemma sq_step:
  assumes p: "(x::fin8380417 mod_ring)^e = of_int_mod_ring a" and v: "(a*a) mod Q = b"
  shows "x^(2*e) = of_int_mod_ring b"
proof -
  have "x^(2*e) = (x^e)^2" by (simp add: power_mult mult.commute)
  also have "\<dots> = (of_int_mod_ring a :: fin8380417 mod_ring)^2" by (simp add: p)
  also have "\<dots> = of_int_mod_ring ((a*a) mod Q)" by (rule sq)
  finally show ?thesis by (simp add: v)
qed

definition w :: "fin8380417 mod_ring" where "w = of_int_mod_ring 3073009"

lemma w_pow_1: "w^1 = of_int_mod_ring 3073009" by (simp add: w_def)
lemma w_pow_2:   "w^2   = of_int_mod_ring 3602218" using sq_step[OF w_pow_1] by simp
lemma w_pow_4:   "w^4   = of_int_mod_ring 5010068" using sq_step[OF w_pow_2] by simp
lemma w_pow_8:   "w^8   = of_int_mod_ring 7778734" using sq_step[OF w_pow_4] by simp
lemma w_pow_16:  "w^16  = of_int_mod_ring 5178923" using sq_step[OF w_pow_8] by simp
lemma w_pow_32:  "w^32  = of_int_mod_ring 3765607" using sq_step[OF w_pow_16] by simp
lemma w_pow_64:  "w^64  = of_int_mod_ring 4808194" using sq_step[OF w_pow_32] by simp
lemma w_pow_128: "w^128 = of_int_mod_ring 8380416" using sq_step[OF w_pow_64] by simp
lemma w_pow_256: "w^256 = of_int_mod_ring 1"       using sq_step[OF w_pow_128] by simp

section \<open>The remaining constants\<close>

text \<open>\<open>omr_mod\<close> cannot be handed to simp as a rewrite: \<open>a \<longrightarrow> a mod Q \<longrightarrow> (a mod Q) mod Q\<close> loops.
It is applied as a rule, with the arithmetic done separately.\<close>

lemma omr_modQ: "(of_int_mod_ring a :: fin8380417 mod_ring) = of_int_mod_ring (a mod Q)"
proof -
  have "(of_int_mod_ring a :: fin8380417 mod_ring)
          = of_int_mod_ring (a mod int CARD(fin8380417))" by (rule omr_mod)
  thus ?thesis by simp
qed

lemma omr_one: "(of_int_mod_ring 1 :: fin8380417 mod_ring) = 1"
  by (transfer, simp)

definition mu :: "fin8380417 mod_ring" where "mu = of_int_mod_ring 6635910"
definition ps :: "fin8380417 mod_ring" where "ps = of_int_mod_ring 1753"

text \<open>\<open>mu * omega = 1\<close>: 6635910 * 3073009 reduces to 1 mod q.\<close>
lemma mu_w: "mu * w = 1"
proof -
  have arith: "((6635910::int) * 3073009) mod Q = 1" by simp
  have "mu * w = of_int_mod_ring ((6635910::int) * 3073009)"
    unfolding mu_def w_def by (rule omr_mult[symmetric])
  also have "\<dots> = of_int_mod_ring (((6635910::int) * 3073009) mod Q)" by (rule omr_modQ)
  also have "\<dots> = (of_int_mod_ring 1 :: fin8380417 mod_ring)" by (simp only: arith)
  also have "\<dots> = 1" by (rule omr_one)
  finally show ?thesis .
qed

text \<open>\<open>psi^2 = omega\<close>. 1753 * 1753 is exactly 3073009, so no reduction is involved.\<close>
lemma ps_sq: "ps * ps = w"
proof -
  have "ps * ps = of_int_mod_ring ((1753::int) * 1753)"
    unfolding ps_def by (rule omr_mult[symmetric])
  also have "((1753::int) * 1753) = 3073009" by simp
  finally show ?thesis by (simp add: w_def)
qed

text \<open>\<open>omega \<noteq> 1\<close>, which the locale needs alongside \<open>omega^256 = 1\<close>.\<close>
lemma to_int_omr: "to_int_mod_ring (of_int_mod_ring a :: fin8380417 mod_ring) = a mod Q"
  by (simp add: of_int_mod_ring.rep_eq to_int_mod_ring.rep_eq)

lemma w_neq_one: "w \<noteq> 1"
proof
  assume eq: "w = 1"
  have "to_int_mod_ring (w :: fin8380417 mod_ring) = 3073009"
    unfolding w_def by (simp add: to_int_omr)
  moreover have "to_int_mod_ring (1 :: fin8380417 mod_ring) = 1"
    using omr_one to_int_omr[of 1] by simp
  ultimately show False using eq by simp
qed

end
