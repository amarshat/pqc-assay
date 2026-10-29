theory Encode
  imports IConv
begin

text \<open>Why \<open>encode_64\<close> is partial evaluation. On the coset \<open>cantor (base + u)\<close>, \<open>u < 2\<^sup>m\<close>,
  \<open>base\<close> a multiple of \<open>2\<^sup>m\<close>, the factor \<open>s\<^sub>m\<close> is the constant \<open>\<gamma> = cantor (base div 2\<^sup>m)\<close>.
  Since \<open>X\<^sub>a\<^sub>+\<^sub>2\<^sub>^\<^sub>m\<^sub>b(x) = X\<^sub>a(x) X\<^sub>b(s\<^sub>m x)\<close>, a polynomial with \<open>2\<^sup>m N\<close> novel-basis
  coordinates \<open>c\<close> agrees there with the one with \<open>2\<^sup>m\<close> coordinates
  \<open>g\<^sub>a = \<Sum>\<^sub>b c\<^sub>a\<^sub>+\<^sub>2\<^sub>^\<^sub>m\<^sub>b X\<^sub>b(\<gamma>)\<close>, which the butterfly network then evaluates.
  In the hqc-1 model \<open>m = 9\<close>, \<open>base = 2\<^sup>4\<^sup>1\<close>, \<open>\<gamma> = \<beta>\<^sub>3\<^sub>2\<close>, and \<open>X\<^sub>b(\<beta>\<^sub>3\<^sub>2)\<close> is row \<open>b\<close>
  of \<open>_enc_mat\<close>.\<close>

lemma X_split: "a < 2 ^ m \<Longrightarrow> X (a + 2 ^ m * b) x = X a x * X b (sv m x)"
  by (simp add: poly_XP[symmetric] XP_factor poly_pcompose poly_sp)

lemma sv_coset:
  assumes cb: "cantor_basis \<beta>" and al: "base mod 2 ^ m = 0" and u: "u < 2 ^ m"
  shows "sv m (cantor \<beta> (base + u)) = cantor \<beta> (base div 2 ^ m)"
  using al u by (simp add: sv_cantor[OF cb] div_add1_eq)

theorem eval_partial:
  assumes cb: "cantor_basis \<beta>" and al: "base mod 2 ^ m = 0" and u: "u < 2 ^ m"
  shows "(\<Sum>d<2 ^ m * N. c d * X d (cantor \<beta> (base + u)))
       = evalN m (\<lambda>a. \<Sum>b<N. c (a + 2 ^ m * b) * X b (cantor \<beta> (base div 2 ^ m))) (cantor \<beta> (base + u))"
proof -
  define x where "x = cantor \<beta> (base + u)"
  define \<gamma> where "\<gamma> = cantor \<beta> (base div 2 ^ m)"
  have "(\<Sum>d<2 ^ m * N. c d * X d x) = (\<Sum>b<N. \<Sum>a<2 ^ m. c (a + 2 ^ m * b) * X (a + 2 ^ m * b) x)"
    by (rule sum_lt_mult)
  also have "\<dots> = (\<Sum>b<N. \<Sum>a<2 ^ m. c (a + 2 ^ m * b) * X b \<gamma> * X a x)"
  proof (intro sum.cong refl)
    fix b a :: nat assume "a \<in> {..<2 ^ m}"
    then have "a < 2 ^ m" by simp
    then have "X (a + 2 ^ m * b) x = X a x * X b \<gamma>"
      using X_split[of a m b x] sv_coset[OF cb al u] by (simp add: x_def \<gamma>_def)
    then show "c (a + 2 ^ m * b) * X (a + 2 ^ m * b) x = c (a + 2 ^ m * b) * X b \<gamma> * X a x"
      by (simp add: ac_simps)
  qed
  also have "\<dots> = (\<Sum>a<2 ^ m. (\<Sum>b<N. c (a + 2 ^ m * b) * X b \<gamma>) * X a x)"
    by (simp only: sum.swap[of _ "{..<N}"] sum_distrib_right)
  also have "\<dots> = evalN m (\<lambda>a. \<Sum>b<N. c (a + 2 ^ m * b) * X b \<gamma>) x"
    by (simp add: evalN_def)
  finally show ?thesis by (simp add: x_def \<gamma>_def)
qed

corollary fft_encode:
  assumes cb: "cantor_basis \<beta>" and al: "base mod 2 ^ m = 0" and u: "u < 2 ^ m"
  shows "fft \<beta> m base (\<lambda>a. \<Sum>b<N. c (a + 2 ^ m * b) * X b (cantor \<beta> (base div 2 ^ m))) u
       = (\<Sum>d<2 ^ m * N. c d * X d (cantor \<beta> (base + u)))"
  by (simp add: fft_eval[OF cb al u] eval_partial[OF cb al u])

text \<open>The value of a polynomial from its novel-basis coordinates.\<close>

lemma poly_novel: "poly (\<Sum>d<n. smult (c d) (XP d)) x = (\<Sum>d<n. c d * X d x)"
  by (simp add: poly_sum poly_XP)

end
