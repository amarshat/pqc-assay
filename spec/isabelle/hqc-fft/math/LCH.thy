theory LCH
  imports Cantor
begin

text \<open>The additive FFT of Lin, Chung and Han in the novel polynomial basis built from the Cantor
  subspace polynomials. \<open>X k = \<Prod> s\<^sub>i\<^sup>k\<^sup>\<^sub>i\<close> over the bits \<open>k\<^sub>i\<close> of \<open>k\<close>; \<open>evalN m f x\<close> is
  \<open>\<Sum>\<^sub>k\<^sub><\<^sub>2\<^sub>\<^sup>m f\<^sub>k X\<^sub>k(x)\<close>. \<open>fft m base f\<close> is the butterfly recursion: one layer
  (lo += c hi; hi += lo, with \<open>c = cantor (base div 2\<^sup>m)\<close>) and the two halves on the cosets at
  \<open>base\<close> and \<open>base + 2\<^sup>m\<close>. The theorem: output \<open>u\<close> is \<open>f\<close> evaluated at \<open>cantor (base + u)\<close>.\<close>

fun Xf :: "nat \<Rightarrow> nat \<Rightarrow> 'a :: char2 \<Rightarrow> 'a" where
  "Xf i k x = (if k = 0 then 1 else (if odd k then sv i x else 1) * Xf (Suc i) (k div 2) x)"

declare Xf.simps [simp del]

lemma Xf_0 [simp]: "Xf i 0 x = 1"
  by (simp add: Xf.simps)

lemma Xf_unfold: "Xf i k x = (if odd k then sv i x else 1) * Xf (Suc i) (k div 2) x"
  by (cases "k = 0") (simp_all add: Xf.simps[of i k])

lemma Xf_top:
  "k < 2 ^ m \<Longrightarrow> Xf i (k + 2 ^ m) x = sv (i + m) x * Xf i k x"
proof (induction m arbitrary: i k)
  case 0
  then have "k = 0" by simp
  then show ?case by (simp add: Xf_unfold[of i "Suc 0"])
next
  case (Suc m)
  have d: "(k + 2 ^ Suc m) div 2 = k div 2 + 2 ^ m" by simp
  have o: "odd (k + 2 ^ Suc m) = odd k" by simp
  have lt: "k div 2 < 2 ^ m" using Suc.prems by simp
  have "Xf i (k + 2 ^ Suc m) x = (if odd k then sv i x else 1) * Xf (Suc i) (k div 2 + 2 ^ m) x"
    by (subst Xf_unfold) (simp only: d o)
  also have "\<dots> = (if odd k then sv i x else 1) * (sv (Suc i + m) x * Xf (Suc i) (k div 2) x)"
    by (simp only: Suc.IH[OF lt])
  also have "\<dots> = sv (i + Suc m) x * Xf i k x"
    by (subst (2) Xf_unfold) (simp add: ac_simps)
  finally show ?case .
qed

definition X :: "nat \<Rightarrow> 'a :: char2 \<Rightarrow> 'a" where "X k = Xf 0 k"

definition evalN :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: char2) \<Rightarrow> 'a \<Rightarrow> 'a" where
  "evalN m f x = (\<Sum>k<2 ^ m. f k * X k x)"

lemma sum_lessThan_add:
  fixes a b :: nat
  shows "(\<Sum>k<a + b. h k) = (\<Sum>k<a. h k) + (\<Sum>k<b. h (k + a))"
  by (induction b) (simp_all add: add.commute add.left_commute)

lemma sum_double:
  "(\<Sum>k<(2::nat) ^ Suc m. h k) = (\<Sum>k<2 ^ m. h k) + (\<Sum>k<2 ^ m. h (k + 2 ^ m))"
  using sum_lessThan_add[of h "2 ^ m" "2 ^ m"] by (simp add: mult_2)

lemma evalN_split:
  "evalN (Suc m) f x = evalN m f x + sv m x * evalN m (\<lambda>k. f (k + 2 ^ m)) x"
proof -
  have "evalN (Suc m) f x = evalN m f x + (\<Sum>k<2 ^ m. f (k + 2 ^ m) * X (k + 2 ^ m) x)"
    by (simp only: evalN_def sum_double)
  also have "(\<Sum>k<2 ^ m. f (k + 2 ^ m) * X (k + 2 ^ m) x) = (\<Sum>k<2 ^ m. sv m x * (f (k + 2 ^ m) * X k x))"
    by (rule sum.cong) (simp_all add: X_def Xf_top ac_simps)
  finally show ?thesis by (simp add: evalN_def sum_distrib_left)
qed

lemma evalN_lin:
  "evalN m (\<lambda>k. f k + c * g k) x = evalN m f x + c * evalN m g x"
proof -
  have "(\<Sum>k<2 ^ m. (f k + c * g k) * X k x) = (\<Sum>k<2 ^ m. f k * X k x + c * (g k * X k x))"
    by (rule sum.cong) (simp_all add: algebra_simps)
  then show ?thesis by (simp only: evalN_def sum.distrib sum_distrib_left)
qed

fun fft :: "(nat \<Rightarrow> 'a :: char2) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "fft \<beta> 0 base f = (\<lambda>u. f 0)"
| "fft \<beta> (Suc m) base f =
     (let c = cantor \<beta> (base div 2 ^ m);
          g0 = (\<lambda>k. f k + c * f (k + 2 ^ m));
          g1 = (\<lambda>k. g0 k + f (k + 2 ^ m))
      in (\<lambda>u. if u < 2 ^ m then fft \<beta> m base g0 u else fft \<beta> m (base + 2 ^ m) g1 (u - 2 ^ m)))"

lemma cantor_odd: "cantor \<beta> (Suc (2 * t)) = \<beta> 0 + cantor \<beta> (2 * t)"
proof -
  have a: "cantor \<beta> (Suc (2 * t)) = \<beta> 0 + cantor_from \<beta> (Suc 0) t"
    by (simp add: cantor_def cantor_from.simps[of \<beta> 0 "Suc (2 * t)"])
  show ?thesis
  proof (cases "t = 0")
    case True then show ?thesis by (simp add: a cantor_def cantor_from.simps)
  next
    case False
    then have "cantor \<beta> (2 * t) = cantor_from \<beta> (Suc 0) t"
      by (simp add: cantor_def cantor_from.simps[of \<beta> 0 "2 * t"])
    then show ?thesis by (simp add: a)
  qed
qed

theorem fft_eval:
  assumes cb: "cantor_basis n \<beta>" and al: "base mod 2 ^ m = 0" and u: "u < 2 ^ m"
    and top: "base + 2 ^ m \<le> 2 ^ n"
  shows "fft \<beta> m base f u = evalN m f (cantor \<beta> (base + u))"
  using al u top
proof (induction m arbitrary: base f u)
  case 0 then show ?case by (simp add: evalN_def X_def Xf.simps)
next
  case (Suc m)
  define c where "c = cantor \<beta> (base div 2 ^ m)"
  define hi where "hi = (\<lambda>k. f (k + 2 ^ m))"
  define g0 where "g0 = (\<lambda>k. f k + c * hi k)"
  define g1 where "g1 = (\<lambda>k. g0 k + hi k)"
  obtain q where bq: "base = 2 ^ Suc m * q" using Suc.prems(1) by (auto simp: mod_eq_0_iff_dvd elim: dvdE)
  have al0: "base mod 2 ^ m = 0" by (simp add: bq)
  have ev: "base div 2 ^ m = 2 * (base div 2 ^ Suc m)" by (simp add: bq)
  show ?case
  proof (cases "u < 2 ^ m")
    case True
    have s: "sv m (cantor \<beta> (base + u)) = c"
      using True al0 Suc.prems(3) by (simp add: sv_cantor[OF cb] c_def div_add1_eq)
    have "fft \<beta> (Suc m) base f u = fft \<beta> m base g0 u"
      using True by (simp add: Let_def c_def g0_def hi_def)
    also have "\<dots> = evalN m g0 (cantor \<beta> (base + u))" by (rule Suc.IH[OF al0 True]) (use Suc.prems(3) in simp)
    also have "\<dots> = evalN (Suc m) f (cantor \<beta> (base + u))"
      by (simp add: evalN_split s g0_def evalN_lin hi_def)
    finally show ?thesis .
  next
    case False
    define u' where "u' = u - 2 ^ m"
    have u': "u' < 2 ^ m" using False Suc.prems(2) by (simp add: u'_def)
    have alb: "(base + 2 ^ m) mod 2 ^ m = 0" using al0 by simp
    have bu: "base + u = (base + 2 ^ m) + u'" using False by (simp add: u'_def)
    have q: "(base + u) div 2 ^ m = 2 * (base div 2 ^ Suc m) + 1"
      using al0 u' ev by (simp add: bu div_add1_eq)
    have s: "sv m (cantor \<beta> (base + u)) = 1 + c"
      using cb Suc.prems(2,3) by (simp add: sv_cantor[OF cb] q cantor_odd c_def ev cantor_basis_def)
    have "fft \<beta> (Suc m) base f u = fft \<beta> m (base + 2 ^ m) g1 u'"
      using False by (simp add: Let_def c_def g0_def g1_def hi_def u'_def)
    also have "\<dots> = evalN m g1 (cantor \<beta> (base + u))"
      using Suc.IH[OF alb u'] Suc.prems(3) by (simp add: bu)
    also have "\<dots> = evalN (Suc m) f (cantor \<beta> (base + u))"
    proof -
      have "g1 = (\<lambda>k. f k + (1 + c) * hi k)" by (simp add: g1_def g0_def fun_eq_iff algebra_simps)
      then show ?thesis by (simp add: evalN_split s evalN_lin hi_def)
    qed
    finally show ?thesis .
  qed
qed

end
