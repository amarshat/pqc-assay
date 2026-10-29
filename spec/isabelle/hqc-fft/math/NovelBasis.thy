theory NovelBasis
  imports LCH "HOL-Computational_Algebra.Polynomial"
begin

text \<open>The subspace polynomials and the novel basis as polynomials. \<open>sp i\<close> is \<open>s\<^sub>i\<close>
  (\<open>poly (sp i) = sv i\<close>), they compose (\<open>s\<^sub>i\<^sub>+\<^sub>j = s\<^sub>i \<circ> s\<^sub>j\<close>), and \<open>s\<^sub>2\<^sup>j\<close> has two terms,
  \<open>x\<^sup>2\<^sup>^\<^sup>2\<^sup>^\<^sup>j + x\<close>; with Frobenius its \<open>2\<^sup>t\<close>-th power is \<open>x\<^sup>2\<^sup>^\<^sup>(\<^sup>2\<^sup>^\<^sup>j\<^sup>+\<^sup>t\<^sup>) + x\<^sup>2\<^sup>^\<^sup>t\<close>. These are
  the divisors of the basis-conversion layers. \<open>XP k\<close> is the novel basis polynomial \<open>X\<^sub>k\<close>, and
  \<open>X\<^sub>a\<^sub>+\<^sub>2\<^sub>^\<^sub>m\<^sub>b = X\<^sub>a \<cdot> (X\<^sub>b \<circ> s\<^sub>m)\<close> for \<open>a < 2\<^sup>m\<close>, the identity behind the recursive conversion.\<close>

instantiation poly :: (char2) char2
begin
instance proof
  show "1 + 1 = (0 :: 'a poly)" by (simp only: one_pCons add_pCons one_plus_one add_0_left pCons_0_0)
qed
end

lemma frob: "(x + y :: 'a :: char2) ^ (2 ^ t) = x ^ (2 ^ t) + y ^ (2 ^ t)"
proof (induction t)
  case 0 then show ?case by simp
next
  case (Suc t)
  have "(x + y) ^ (2 ^ Suc t) = ((x + y) ^ (2 ^ t)) * ((x + y) ^ (2 ^ t))"
    by (simp add: power_mult[symmetric] power2_eq_square[symmetric] mult.commute)
  also have "\<dots> = x ^ (2 ^ t) * x ^ (2 ^ t) + y ^ (2 ^ t) * y ^ (2 ^ t)" by (simp only: Suc sq_add)
  also have "\<dots> = x ^ (2 ^ Suc t) + y ^ (2 ^ Suc t)"
    by (simp add: power_mult[symmetric] power2_eq_square[symmetric] mult.commute)
  finally show ?case .
qed

fun sp :: "nat \<Rightarrow> 'a :: char2 poly" where
  "sp 0 = [:0, 1:]"
| "sp (Suc i) = sp i * sp i + sp i"

lemma poly_sp: "poly (sp i) x = sv i x"
  by (induction i) simp_all

lemma sp_compose: "sp (i + j) = pcompose (sp i) (sp j)"
  by (induction i) (simp_all add: pcompose_add pcompose_mult pcompose_pCons)

lemma pcompose_one [simp]: "pcompose 1 q = 1"
  by (simp add: one_pCons pcompose_pCons)

lemma X_pow: "[:0, 1 :: 'a :: comm_ring_1:] ^ n = monom 1 n"
  by (simp add: monom_altdef)

lemma pcompose_monom1: "pcompose (monom 1 n) q = (q :: 'a :: comm_ring_1 poly) ^ n"
proof -
  have "pcompose ([:0, 1:] ^ n) q = q ^ n"
    by (induction n) (simp_all add: pcompose_mult pcompose_pCons)
  then show ?thesis by (simp only: X_pow)
qed

lemma monom_pow: "(monom (1 :: 'a :: comm_ring_1) n) ^ k = monom 1 (n * k)"
  by (induction k) (simp_all add: mult_monom algebra_simps)

theorem sp_two_term: "sp (2 ^ j) = (monom 1 (2 ^ 2 ^ j) + [:0, 1:] :: 'a :: char2 poly)"
proof (induction j)
  case 0 then show ?case by (simp add: monom_altdef power2_eq_square)
next
  case (Suc j)
  define N :: nat where "N = 2 ^ 2 ^ j"
  have "sp (2 ^ Suc j) = pcompose (sp (2 ^ j)) (sp (2 ^ j) :: 'a poly)"
    by (simp add: sp_compose[symmetric] mult_2)
  also have "\<dots> = (monom 1 N + [:0, 1:]) ^ N + (monom 1 N + [:0, 1:])"
    by (simp add: Suc N_def pcompose_add pcompose_monom1 pcompose_pCons)
  also have "(monom 1 N + [:0, 1 :: 'a:]) ^ N = monom 1 (N * N) + monom 1 N"
    by (simp add: N_def frob monom_pow X_pow)
  also have "N * N = 2 ^ 2 ^ Suc j" by (simp add: N_def power_add[symmetric] mult_2)
  finally show ?case by simp
qed

theorem sp_two_term_pow:
  "sp (2 ^ j) ^ (2 ^ t) = (monom 1 (2 ^ (2 ^ j + t)) + monom 1 (2 ^ t) :: 'a :: char2 poly)"
  by (simp add: sp_two_term frob monom_pow X_pow power_add)

fun XPf :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: char2 poly" where
  "XPf i k = (if k = 0 then 1 else (if odd k then sp i else 1) * XPf (Suc i) (k div 2))"

declare XPf.simps [simp del]

lemma XPf_0 [simp]: "XPf i 0 = 1"
  by (simp add: XPf.simps)

lemma XPf_unfold: "XPf i k = (if odd k then sp i else 1) * XPf (Suc i) (k div 2)"
  by (cases "k = 0") (simp_all add: XPf.simps[of i k])

lemma poly_XPf: "poly (XPf i k) x = Xf i k x"
proof (induction k arbitrary: i rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k = 0")
    case True then show ?thesis by simp
  next
    case False
    then have "k div 2 < k" by simp
    then show ?thesis
      by (simp add: XPf_unfold[of i k] Xf_unfold[of i k] less.IH poly_sp)
  qed
qed

lemma XPf_shift: "XPf (i + m) b = pcompose (XPf i b) (sp m :: 'a :: char2 poly)"
proof (induction b arbitrary: i rule: less_induct)
  case (less b)
  show ?case
  proof (cases "b = 0")
    case True then show ?thesis by simp
  next
    case False
    then have lt: "b div 2 < b" by simp
    have "XPf (i + m) b = (if odd b then sp (i + m) else 1) * (XPf (Suc i + m) (b div 2) :: 'a poly)"
      by (simp add: XPf_unfold[of "i + m" b])
    also have "\<dots> = pcompose ((if odd b then sp i else 1) * XPf (Suc i) (b div 2)) (sp m)"
    proof -
      have h: "XPf (Suc (i + m)) (b div 2) = pcompose (XPf (Suc i) (b div 2)) (sp m :: 'a poly)"
        using less.IH[OF lt, of "Suc i"] by simp
      show ?thesis by (simp add: h pcompose_mult sp_compose)
    qed
    also have "\<dots> = pcompose (XPf i b) (sp m)" by (simp add: XPf_unfold[of i b])
    finally show ?thesis .
  qed
qed

lemma XPf_split:
  "a < 2 ^ m \<Longrightarrow> XPf i (a + 2 ^ m * b) = XPf i a * (XPf (i + m) b :: 'a :: char2 poly)"
proof (induction m arbitrary: i a)
  case 0 then show ?case by simp
next
  case (Suc m)
  have lt: "a div 2 < 2 ^ m" using Suc.prems by simp
  have d: "(a + 2 ^ Suc m * b) div 2 = a div 2 + 2 ^ m * b" by simp
  have o: "odd (a + 2 ^ Suc m * b) = odd a" by simp
  have "XPf i (a + 2 ^ Suc m * b) = (if odd a then sp i else 1) * (XPf (Suc i) (a div 2 + 2 ^ m * b) :: 'a poly)"
    by (subst XPf_unfold) (simp only: d o)
  also have "\<dots> = (if odd a then sp i else 1) * (XPf (Suc i) (a div 2) * XPf (Suc i + m) b)"
  proof -
    have h: "XPf (Suc i) (a div 2 + 2 ^ m * b) = XPf (Suc i) (a div 2) * (XPf (Suc (i + m)) b :: 'a poly)"
      using Suc.IH[OF lt, of "Suc i"] by simp
    show ?thesis by (simp add: h)
  qed
  also have "\<dots> = XPf i a * XPf (i + Suc m) b"
    by (subst (2) XPf_unfold) (simp add: ac_simps)
  finally show ?case .
qed

definition XP :: "nat \<Rightarrow> 'a :: char2 poly" where "XP k = XPf 0 k"

theorem XP_factor:
  "a < 2 ^ m \<Longrightarrow> XP (a + 2 ^ m * b) = XP a * pcompose (XP b) (sp m)"
  by (simp add: XP_def XPf_split XPf_shift[of 0 m b, simplified])

lemma poly_XP: "poly (XP k) x = X k x"
  by (simp add: XP_def X_def poly_XPf)

end
