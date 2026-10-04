(* v4: negconv IS multiplication in R_q = Z_q[X]/(X^n+1).

   Negacyclic_Conv proves the transform carries negconv to pointwise multiplication, but negconv
   there is a coefficient formula. This theory proves the lemma that makes it a product:

     Poly (negconv xs ys) = (Poly xs * Poly ys) mod (monom 1 n + 1)

   The proof is conv_row's rearrangement run at X instead of at a root of X^n + 1. At a root the
   wrap-around terms pick up z^n = -1; at X they pick up X^n = (X^n + 1) - 1, and the (X^n + 1)
   parts are collected into an explicit quotient H. So the product is negconv plus a multiple of
   X^n + 1, and negconv has degree below n, which pins it as the remainder. *)
theory Negacyclic_Poly
  imports Negacyclic_Conv
begin

lemma monom_sum: "monom (\<Sum>x\<in>A. f x) m = (\<Sum>x\<in>A. monom (f x) m)"
  by (induct A rule: infinite_finite_induct) (auto simp: add_monom[symmetric])

context negacyclic_butterfly
begin

abbreviation (input) Dn :: "'a mod_ring poly" where "Dn \<equiv> monom 1 n + 1"

lemma Dn_monom: "Dn * monom c a = monom c (a + n) + monom c a"
  by (simp add: distrib_right mult_monom add.commute)

text \<open>One row of the rearrangement, at \<open>X\<close>. The left sum is row \<open>i\<close>'s contribution to
\<open>Poly (negconv xs ys)\<close>; the second term collects what \<open>X^n = -1\<close> would have discarded.\<close>

lemma poly_row:
  assumes i: "i < n"
  shows "(\<Sum>m<n. monom (if i \<le> m then (xs!i) * (ys!(m-i)) else - ((xs!i) * (ys!(m+n-i)))) m)
         + Dn * (\<Sum>j\<in>{n-i..<n}. monom ((xs!i) * (ys!j)) (j - (n-i)))
       = monom (xs!i) i * (\<Sum>j<n. monom (ys!j) j)"
proof -
  let ?F = "\<lambda>m. monom (if i \<le> m then (xs!i) * (ys!(m-i)) else - ((xs!i) * (ys!(m+n-i)))) m"
  let ?G = "\<lambda>j. monom ((xs!i) * (ys!j)) (i+j)"
  let ?H = "\<lambda>j. monom ((xs!i) * (ys!j)) (j - (n-i))"

  have hi: "(\<Sum>m\<in>{i..<n}. ?F m) = (\<Sum>j\<in>{0..<n-i}. ?G j)"
  proof (rule sum.reindex_bij_witness[of _ "\<lambda>j. i+j" "\<lambda>m. m-i"])
    show "\<And>a. a \<in> {i..<n} \<Longrightarrow> i + (a - i) = a" by auto
    show "\<And>a. a \<in> {i..<n} \<Longrightarrow> a - i \<in> {0..<n-i}" by auto
    show "\<And>b. b \<in> {0..<n-i} \<Longrightarrow> (i + b) - i = b" by auto
    show "\<And>b. b \<in> {0..<n-i} \<Longrightarrow> i + b \<in> {i..<n}" using i by auto
    show "\<And>a. a \<in> {i..<n} \<Longrightarrow> ?G (a - i) = ?F a" by auto
  qed

  have lo0: "(\<Sum>m\<in>{0..<i}. ?F m) = (\<Sum>j\<in>{n-i..<n}. ?F (j - (n-i)))"
  proof (rule sum.reindex_bij_witness[of _ "\<lambda>j. j-(n-i)" "\<lambda>m. m+n-i"])
    show "\<And>a. a \<in> {0..<i} \<Longrightarrow> (a + n - i) - (n - i) = a" using i by auto
    show "\<And>a. a \<in> {0..<i} \<Longrightarrow> a + n - i \<in> {n-i..<n}" using i by auto
    show "\<And>b. b \<in> {n-i..<n} \<Longrightarrow> (b - (n-i)) + n - i = b" using i by auto
    show "\<And>b. b \<in> {n-i..<n} \<Longrightarrow> b - (n-i) \<in> {0..<i}" using i by auto
    show "\<And>a. a \<in> {0..<i} \<Longrightarrow> ?F ((a + n - i) - (n - i)) = ?F a" using i by auto
  qed

  have lo_term: "?F (j - (n-i)) + Dn * ?H j = ?G j" if j: "j \<in> {n-i..<n}" for j
  proof -
    let ?a = "j - (n-i)"
    have lt: "?a < i" and idx: "?a + n - i = j" and ex: "?a + n = i + j" using i j by auto
    have "?F ?a = monom (- ((xs!i) * (ys!(?a + n - i)))) ?a" using lt by simp
    also have "\<dots> = - monom ((xs!i) * (ys!j)) ?a" by (simp only: idx minus_monom)
    finally have Fa: "?F ?a = - monom ((xs!i) * (ys!j)) ?a" .
    have Dh: "Dn * ?H j = monom ((xs!i) * (ys!j)) (?a + n) + monom ((xs!i) * (ys!j)) ?a"
      by (rule Dn_monom)
    show ?thesis using Fa Dh by (simp add: ex)
  qed

  have lo: "(\<Sum>m\<in>{0..<i}. ?F m) + Dn * (\<Sum>j\<in>{n-i..<n}. ?H j) = (\<Sum>j\<in>{n-i..<n}. ?G j)"
  proof -
    have "(\<Sum>m\<in>{0..<i}. ?F m) + Dn * (\<Sum>j\<in>{n-i..<n}. ?H j)
            = (\<Sum>j\<in>{n-i..<n}. ?F (j - (n-i))) + (\<Sum>j\<in>{n-i..<n}. Dn * ?H j)"
      by (simp only: lo0 sum_distrib_left)
    also have "\<dots> = (\<Sum>j\<in>{n-i..<n}. ?F (j - (n-i)) + Dn * ?H j)"
      by (simp only: sum.distrib)
    also have "\<dots> = (\<Sum>j\<in>{n-i..<n}. ?G j)"
      by (rule sum.cong[OF refl]) (rule lo_term)
    finally show ?thesis .
  qed

  have c1: "(\<Sum>m\<in>{0..<i}. ?F m) + (\<Sum>m\<in>{i..<n}. ?F m) = (\<Sum>m\<in>{0..<n}. ?F m)"
    using i by (intro sum.atLeastLessThan_concat) auto
  have c2: "(\<Sum>j\<in>{0..<n-i}. ?G j) + (\<Sum>j\<in>{n-i..<n}. ?G j) = (\<Sum>j\<in>{0..<n}. ?G j)"
    using i by (intro sum.atLeastLessThan_concat) auto

  have "(\<Sum>m<n. ?F m) + Dn * (\<Sum>j\<in>{n-i..<n}. ?H j)
          = (\<Sum>m\<in>{i..<n}. ?F m) + ((\<Sum>m\<in>{0..<i}. ?F m) + Dn * (\<Sum>j\<in>{n-i..<n}. ?H j))"
    using c1 by (simp add: atLeast0LessThan[symmetric] add_ac)
  also have "\<dots> = (\<Sum>j\<in>{0..<n-i}. ?G j) + (\<Sum>j\<in>{n-i..<n}. ?G j)"
    by (simp only: hi lo)
  also have "\<dots> = (\<Sum>j<n. ?G j)" using c2 by (simp add: atLeast0LessThan)
  also have "\<dots> = monom (xs!i) i * (\<Sum>j<n. monom (ys!j) j)"
    by (simp add: sum_distrib_left mult_monom)
  finally show ?thesis .
qed

lemma Poly_as_sum:
  assumes len: "length xs = n"
  shows "Poly xs = (\<Sum>j<n. monom (xs!j) j)"
proof (rule poly_eqI)
  fix k
  show "coeff (Poly xs) k = coeff (\<Sum>j<n. monom (xs!j) j) k"
    using len by (simp add: coeff_Poly nth_default_def coeff_sum coeff_monom)
qed

lemma degree_Poly_lt:
  assumes len: "length xs = n"
  shows "degree (Poly xs) < n"
proof -
  have "degree (Poly xs) \<le> n - 1"
    by (rule degree_le) (use len in \<open>auto simp: coeff_Poly nth_default_def\<close>)
  moreover have "0 < n" using N_pos n_lst2 by linarith
  ultimately show ?thesis by linarith
qed

lemma degree_Dn: "degree Dn = n"
proof -
  have "0 < n" using N_pos n_lst2 by linarith
  thus ?thesis by (simp add: degree_add_eq_left degree_monom_eq)
qed

theorem negconv_poly_identity:
  assumes lx: "length xs = n" and ly: "length ys = n"
  shows "Poly xs * Poly ys
           = Poly (negconv xs ys)
             + Dn * (\<Sum>i<n. \<Sum>j\<in>{n-i..<n}. monom ((xs!i) * (ys!j)) (j - (n-i)))"
proof -
  let ?row = "\<lambda>i m. monom (if i \<le> m then (xs!i) * (ys!(m-i)) else - ((xs!i) * (ys!(m+n-i)))) m"
  have "Poly (negconv xs ys) = (\<Sum>m<n. monom (negconv xs ys ! m) m)"
    by (rule Poly_as_sum) simp
  also have "\<dots> = (\<Sum>m<n. \<Sum>i<n. ?row i m)"
    by (rule sum.cong[OF refl]) (simp add: monom_sum)
  also have "\<dots> = (\<Sum>i<n. \<Sum>m<n. ?row i m)" by (rule sum.swap)
  finally have pn: "Poly (negconv xs ys) = (\<Sum>i<n. \<Sum>m<n. ?row i m)" .
  have "Poly (negconv xs ys)
          + Dn * (\<Sum>i<n. \<Sum>j\<in>{n-i..<n}. monom ((xs!i) * (ys!j)) (j - (n-i)))
          = (\<Sum>i<n. (\<Sum>m<n. ?row i m)
                     + Dn * (\<Sum>j\<in>{n-i..<n}. monom ((xs!i) * (ys!j)) (j - (n-i))))"
    by (simp add: pn sum.distrib sum_distrib_left)
  also have "\<dots> = (\<Sum>i<n. monom (xs!i) i * (\<Sum>j<n. monom (ys!j) j))"
    by (rule sum.cong[OF refl], rule poly_row, simp)
  also have "\<dots> = Poly xs * Poly ys"
    by (simp add: Poly_as_sum[OF lx] Poly_as_sum[OF ly] sum_distrib_right)
  finally show ?thesis by simp
qed

theorem negconv_is_mult:
  assumes lx: "length xs = n" and ly: "length ys = n"
  shows "Poly (negconv xs ys) = (Poly xs * Poly ys) mod (monom 1 n + 1)"
proof -
  let ?H = "\<Sum>i<n. \<Sum>j\<in>{n-i..<n}. monom ((xs!i) * (ys!j)) (j - (n-i))"
  have "(Poly xs * Poly ys) mod Dn = (Poly (negconv xs ys) + Dn * ?H) mod Dn"
    by (simp only: negconv_poly_identity[OF lx ly])
  also have "\<dots> = Poly (negconv xs ys) mod Dn" by (rule mod_mult_self2)
  also have "\<dots> = Poly (negconv xs ys)"
    by (rule mod_poly_less) (simp add: degree_Dn degree_Poly_lt)
  finally show ?thesis by simp
qed

end

end
