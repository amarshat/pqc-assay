(* Tier-2, v4: the negacyclic NTT diagonalises multiplication in R_q = Z_q[X]/(X^n+1).

   Everything proven before this file says the transform IS the transform and that it inverts.
   None of it says it MULTIPLIES, which is the only reason the NTT is in ML-DSA at all. This file
   states and proves that missing theorem at the mod_ring level:

     NNTT (negconv xs ys) = pointwise (NNTT xs) (NNTT ys)            (NNTT_negconv)
     INNTT (pointwise (NNTT xs) (NNTT ys)) = n .* negconv xs ys      (negconv_via_NNTT)

   The reading that makes it work: nntt xs k = (SUM j<n. xs!j * psi^((2k+1)*j)) is evaluation of
   the coefficient list at psi^(2k+1), so NNTT is the CRT map onto the n roots of X^n+1 and the
   theorem is that evaluation is a ring homomorphism. The one fact that has to be established
   first is psi^n = -1, i.e. that the evaluation points really are roots of X^n+1. It needs n
   even, so this lives in negacyclic_butterfly rather than plain negacyclic.

   See docs/ROADMAP.md, v4. The AFP Number_Theoretic_Transform entry this development depends on
   proves the transform and its inverse and has no convolution theorem. *)
theory Negacyclic_Conv
  imports Negacyclic_Inv
begin

context negacyclic_butterfly
begin

section \<open>n is even\<close>

lemma N_pos: "N > 0"
proof (rule ccontr)
  assume "\<not> N > 0"
  then have "n = 1" using n_two_pot by simp
  with n_lst2 show False by simp
qed

lemma n_even: "even n"
  using N_pos n_two_pot by simp

lemma n_half: "2 * (n div 2) = n"
  using n_even by simp

section \<open>The evaluation points are the roots of \<open>X^n + 1\<close>\<close>

text \<open>\<open>psi^2 = omega\<close> and \<open>omega^n = 1\<close> give \<open>(psi^n)^2 = 1\<close>, so \<open>psi^n\<close> is \<open>1\<close> or \<open>-1\<close> over a
field. It cannot be \<open>1\<close>: that would make \<open>omega^(n div 2) = 1\<close> with \<open>0 < n div 2 < n\<close>, against the
minimality in \<open>omega_properties\<close>. So no extra locale assumption is needed for this.\<close>

lemma psi_sq': "\<psi>^2 = \<omega>"
  using psi_sq by (simp add: power2_eq_square)

lemma psi_pow_2n: "\<psi>^(2*n) = 1"
proof -
  have "\<psi>^(2*n) = (\<psi>^2)^n" by (simp add: power_mult)
  also have "\<dots> = \<omega>^n" by (simp add: psi_sq')
  finally show ?thesis using omega_properties(1) by simp
qed

theorem psi_pow_n: "\<psi>^n = -1"
proof -
  have sq: "(\<psi>^n)^2 = 1"
    using psi_pow_2n by (simp add: power_mult[symmetric] mult.commute)
  have "(\<psi>^n - 1) * (\<psi>^n + 1) = (\<psi>^n)^2 - 1"
    by (simp add: algebra_simps power2_eq_square)
  also have "\<dots> = 0" using sq by simp
  finally have disj: "\<psi>^n = 1 \<or> \<psi>^n = -1"
    by (auto simp add: eq_neg_iff_add_eq_0)
  moreover have "\<psi>^n \<noteq> 1"
  proof
    assume a: "\<psi>^n = 1"
    have "\<omega>^(n div 2) = (\<psi>^2)^(n div 2)" by (simp add: psi_sq')
    also have "\<dots> = \<psi>^(2 * (n div 2))" by (simp add: power_mult)
    also have "\<dots> = \<psi>^n" by (simp add: n_half)
    finally have one: "\<omega>^(n div 2) = 1" using a by simp
    have "n div 2 \<noteq> 0" using n_lst2 by simp
    with one have "n div 2 \<ge> n" using omega_properties(3) by blast
    thus False using n_lst2 by simp
  qed
  ultimately show ?thesis by blast
qed

definition zpt :: "nat \<Rightarrow> 'a mod_ring" where
  "zpt kk = \<psi>^(2*kk+1)"

lemma zpt_pow_n: "(zpt kk)^n = -1"
proof -
  have "(zpt kk)^n = (\<psi>^(2*kk+1))^n" unfolding zpt_def ..
  also have "\<dots> = \<psi>^((2*kk+1)*n)" by (rule power_mult[symmetric])
  also have "\<dots> = \<psi>^(n*(2*kk+1))" by (simp add: mult.commute)
  also have "\<dots> = (\<psi>^n)^(2*kk+1)" by (rule power_mult)
  also have "\<dots> = (-1::'a mod_ring)^(2*kk+1)" by (simp add: psi_pow_n)
  also have "\<dots> = -1" by (simp add: power_add power_mult)
  finally show ?thesis .
qed

text \<open>The wrap-around identity: past degree \<open>n\<close> an evaluation picks up a sign.\<close>
lemma zpt_shift: "(zpt kk)^(i+j) = - ((zpt kk)^(i+j-n))" if "i+j \<ge> n"
proof -
  have "(zpt kk)^(i+j) = (zpt kk)^((i+j-n) + n)" using that by simp
  also have "\<dots> = (zpt kk)^(i+j-n) * (zpt kk)^n" by (simp add: power_add)
  finally show ?thesis by (simp add: zpt_pow_n)
qed

lemma zpt_pow: "(zpt kk)^j = \<psi>^((2*kk+1)*j)"
  unfolding zpt_def by (rule power_mult[symmetric])

lemma nntt_eval: "nntt xs kk = (\<Sum>j<n. (xs ! j) * (zpt kk)^j)"
  unfolding nntt_def by (simp add: zpt_pow atLeast0LessThan)

section \<open>Negacyclic convolution\<close>

text \<open>Coefficient \<open>kk\<close> of \<open>f*g\<close> reduced mod \<open>X^n + 1\<close>: the ordinary convolution term, minus the
wrap-around term, the sign coming from \<open>X^n = -1\<close>.\<close>

definition negconv :: "'a mod_ring list \<Rightarrow> 'a mod_ring list \<Rightarrow> 'a mod_ring list" where
  "negconv xs ys =
     map (\<lambda>kk. \<Sum>i<n. if i \<le> kk then (xs!i) * (ys!(kk-i)) else - ((xs!i) * (ys!(kk+n-i)))) [0..<n]"

lemma length_negconv [simp]: "length (negconv xs ys) = n"
  by (simp add: negconv_def)

lemma negconv_nth [simp]:
  assumes m: "m < n"
  shows "negconv xs ys ! m
     = (\<Sum>i<n. if i \<le> m then (xs!i) * (ys!(m-i)) else - ((xs!i) * (ys!(m+n-i))))"
proof -
  have len: "m < length [0..<n]" using m by simp
  have idx: "[0..<n] ! m = m" using m by (simp add: nth_upt)
  show ?thesis unfolding negconv_def by (simp only: nth_map[OF len] idx)
qed

section \<open>Evaluation is a ring homomorphism\<close>

text \<open>The single row of the rearrangement. For a fixed \<open>i\<close>, summing the \<open>negconv\<close> contribution over
all output positions \<open>m\<close> reproduces \<open>xs!i * z^i\<close> times the whole evaluation of \<open>ys\<close>. The two halves
of the split reindex to the two halves of \<open>j < n\<close>: \<open>m \<ge> i\<close> maps to \<open>j = m - i\<close> below \<open>n - i\<close>, and
\<open>m < i\<close> maps to \<open>j = m + n - i\<close> at or above \<open>n - i\<close>, where the minus sign in \<open>negconv\<close> is exactly
cancelled by the sign \<open>zpt_shift\<close> introduces.\<close>

lemma conv_row:
  assumes i: "i < n"
  shows "(\<Sum>m<n. (if i \<le> m then (xs!i) * (ys!(m-i)) else - ((xs!i) * (ys!(m+n-i)))) * (zpt kk)^m)
       = (xs!i) * (zpt kk)^i * (\<Sum>j<n. (ys!j) * (zpt kk)^j)"
proof -
  let ?z = "zpt kk"
  let ?F = "\<lambda>m. (if i \<le> m then (xs!i) * (ys!(m-i)) else - ((xs!i) * (ys!(m+n-i)))) * ?z^m"
  let ?G = "\<lambda>j. (xs!i) * (ys!j) * ?z^(i+j)"

  text \<open>Output positions at or above \<open>i\<close> carry the ordinary convolution term and reindex to
  \<open>j = m - i\<close> below \<open>n - i\<close>.\<close>
  have hi: "(\<Sum>m\<in>{i..<n}. ?F m) = (\<Sum>j\<in>{0..<n-i}. ?G j)"
  proof (rule sum.reindex_bij_witness[of _ "\<lambda>j. i+j" "\<lambda>m. m-i"])
    show "\<And>a. a \<in> {i..<n} \<Longrightarrow> i + (a - i) = a" by auto
    show "\<And>a. a \<in> {i..<n} \<Longrightarrow> a - i \<in> {0..<n-i}" by auto
    show "\<And>b. b \<in> {0..<n-i} \<Longrightarrow> (i + b) - i = b" by auto
    show "\<And>b. b \<in> {0..<n-i} \<Longrightarrow> i + b \<in> {i..<n}" using i by auto
    show "\<And>a. a \<in> {i..<n} \<Longrightarrow> ?G (a - i) = ?F a" by auto
  qed

  text \<open>Positions below \<open>i\<close> carry the wrap-around term and reindex to \<open>j = m + n - i\<close> at or above
  \<open>n - i\<close>. The minus sign in \<open>negconv\<close> is exactly the sign \<open>zpt_shift\<close> produces, so the two cancel
  and both halves end up with the same summand \<open>?G\<close>.\<close>
  have lo: "(\<Sum>m\<in>{0..<i}. ?F m) = (\<Sum>j\<in>{n-i..<n}. ?G j)"
  proof (rule sum.reindex_bij_witness[of _ "\<lambda>j. j-(n-i)" "\<lambda>m. m+n-i"])
    show "\<And>a. a \<in> {0..<i} \<Longrightarrow> (a + n - i) - (n - i) = a" using i by auto
    show "\<And>a. a \<in> {0..<i} \<Longrightarrow> a + n - i \<in> {n-i..<n}" using i by auto
    show "\<And>b. b \<in> {n-i..<n} \<Longrightarrow> (b - (n-i)) + n - i = b" using i by auto
    show "\<And>b. b \<in> {n-i..<n} \<Longrightarrow> b - (n-i) \<in> {0..<i}" using i by auto
    fix a assume a: "a \<in> {0..<i}"
    then have lt: "a < i" by simp
    have ge: "i + (a + n - i) \<ge> n" using i lt by auto
    have sum_eq: "i + (a + n - i) = a + n" using i lt by auto
    have "?G (a + n - i) = (xs!i) * (ys!(a+n-i)) * ?z^(a+n)" by (simp add: sum_eq)
    also have "?z^(a+n) = ?z^a * ?z^n" by (simp add: power_add)
    also have "\<dots> = - (?z^a)" by (simp add: zpt_pow_n)
    finally have "?G (a + n - i) = - ((xs!i) * (ys!(a+n-i)) * ?z^a)" by simp
    thus "?G (a + n - i) = ?F a" using lt by simp
  qed

  have c1: "(\<Sum>m\<in>{0..<i}. ?F m) + (\<Sum>m\<in>{i..<n}. ?F m) = (\<Sum>m\<in>{0..<n}. ?F m)"
    using i by (intro sum.atLeastLessThan_concat) auto
  have c2: "(\<Sum>j\<in>{0..<n-i}. ?G j) + (\<Sum>j\<in>{n-i..<n}. ?G j) = (\<Sum>j\<in>{0..<n}. ?G j)"
    using i by (intro sum.atLeastLessThan_concat) auto

  have "(\<Sum>m<n. ?F m) = (\<Sum>m\<in>{0..<n}. ?F m)" by (simp add: atLeast0LessThan)
  also have "\<dots> = (\<Sum>m\<in>{0..<i}. ?F m) + (\<Sum>m\<in>{i..<n}. ?F m)" using c1 by simp
  also have "\<dots> = (\<Sum>j\<in>{n-i..<n}. ?G j) + (\<Sum>j\<in>{0..<n-i}. ?G j)" by (simp only: hi lo)
  also have "\<dots> = (\<Sum>j\<in>{0..<n}. ?G j)" using c2 by (simp add: add.commute)
  also have "\<dots> = (\<Sum>j<n. ((xs!i) * ?z^i) * ((ys!j) * ?z^j))"
    by (simp add: atLeast0LessThan power_add mult.assoc mult.left_commute)
  also have "\<dots> = (xs!i) * ?z^i * (\<Sum>j<n. (ys!j) * ?z^j)"
    by (simp add: sum_distrib_left)
  finally show ?thesis .
qed

theorem nntt_negconv: "nntt (negconv xs ys) kk = nntt xs kk * nntt ys kk"
proof -
  let ?z = "zpt kk"
  have "nntt (negconv xs ys) kk = (\<Sum>m<n. (negconv xs ys ! m) * ?z^m)"
    by (rule nntt_eval)
  also have "\<dots> = (\<Sum>m<n. (\<Sum>i<n. (if i \<le> m then (xs!i) * (ys!(m-i))
                                    else - ((xs!i) * (ys!(m+n-i)))) * ?z^m))"
    by (simp add: sum_distrib_right)
  also have "\<dots> = (\<Sum>i<n. (\<Sum>m<n. (if i \<le> m then (xs!i) * (ys!(m-i))
                                    else - ((xs!i) * (ys!(m+n-i)))) * ?z^m))"
    by (rule sum.swap)
  also have "\<dots> = (\<Sum>i<n. (xs!i) * ?z^i * (\<Sum>j<n. (ys!j) * ?z^j))"
    by (rule sum.cong[OF refl]) (simp add: conv_row)
  also have "\<dots> = (\<Sum>i<n. (xs!i) * ?z^i) * (\<Sum>j<n. (ys!j) * ?z^j)"
    by (simp add: sum_distrib_right)
  finally show ?thesis by (simp add: nntt_eval)
qed

section \<open>The convolution theorem\<close>

definition pointwise :: "'a mod_ring list \<Rightarrow> 'a mod_ring list \<Rightarrow> 'a mod_ring list" where
  "pointwise us vs = map (\<lambda>kk. (us!kk) * (vs!kk)) [0..<n]"

lemma length_pointwise [simp]: "length (pointwise us vs) = n"
  by (simp add: pointwise_def)

theorem NNTT_negconv: "NNTT (negconv xs ys) = pointwise (NNTT xs) (NNTT ys)"
  by (simp add: NNTT_def pointwise_def nntt_negconv)

text \<open>And the form an implementation uses: transform, multiply pointwise, transform back, and you
have the product in \<open>R_q\<close>, up to the factor \<open>n\<close> that the unnormalised inverse leaves behind.\<close>

text \<open>\<^bold>\<open>Non-vacuity, stated because it is not yet discharged.\<close> Everything above is proven inside
\<open>negacyclic_butterfly\<close>, and nothing in this development, or in the AFP entry it builds on,
exhibits a model of that locale: there is no \<open>interpretation\<close> of \<open>ntt\<close>, \<open>butterfly\<close>, \<open>negacyclic\<close>
or \<open>negacyclic_butterfly\<close> at concrete parameters anywhere. A theorem proven in a locale with no
model is vacuous, so until an interpretation exists these results are conditional on the locale
being inhabited.

The parameters that should inhabit it for ML-DSA are \<open>CARD('a) = 8380417\<close>, \<open>n = 256\<close>, \<open>N = 8\<close>,
\<open>k = 32736\<close> (so \<open>p = k*n + 1\<close>), \<open>omega = 3073009\<close>, \<open>psi = 1753\<close>, \<open>mu = omega^-1\<close>. Those satisfy the
assumptions by ordinary arithmetic: 8380417 is prime, 1753 has order exactly 512 and 3073009 order
exactly 256. Discharging it in Isabelle needs a numeral type of cardinality 8380417, which is why it
is a separate obligation rather than a line here. See \<^file>\<open>../../../../docs/ROADMAP.md\<close>, v4 O9.\<close>

theorem negconv_via_NNTT:
  "INNTT (pointwise (NNTT xs) (NNTT ys))
     = map (\<lambda>c. of_int_mod_ring (int n) * c) (negconv xs ys)"
proof -
  have "INNTT (pointwise (NNTT xs) (NNTT ys)) = INNTT (NNTT (negconv xs ys))"
    by (simp add: NNTT_negconv)
  also have "\<dots> = map (\<lambda>c. of_int_mod_ring (int n) * c) (negconv xs ys)"
    by (rule INNTT_NNTT) simp
  finally show ?thesis .
qed

end

end
