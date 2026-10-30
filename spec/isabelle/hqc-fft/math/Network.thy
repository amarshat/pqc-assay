theory Network
  imports LCH
begin

text \<open>The butterfly network as the reference C runs it: stage \<open>si\<close> (half-unit \<open>2\<^sup>s\<^sup>i\<close>) applied for
  \<open>si = M - 1\<close> down to 0 over the whole vector, unit \<open>mm\<close> with the twiddle
  \<open>cantor ((base + mm 2\<^sup>s\<^sup>i\<^sup>+\<^sup>1) div 2\<^sup>s\<^sup>i)\<close>. \<open>net_fft\<close>: this is the recursive \<open>fft\<close>, so
  by \<open>fft_eval\<close> it evaluates on the coset.\<close>

definition stagef :: "nat \<Rightarrow> (nat \<Rightarrow> 'a :: char2) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "stagef h tw f t = (let r = t mod (2 * h); c = tw (t div (2 * h))
     in if r < h then f t + f (t + h) * c else f t + (f (t - h) + f t * c))"

definition twf :: "(nat \<Rightarrow> 'a :: char2) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "twf \<beta> base si mm = cantor \<beta> ((base + mm * 2 ^ Suc si) div 2 ^ si)"

fun chain :: "(nat \<Rightarrow> 'a :: char2) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a" where
  "chain \<beta> base 0 f = f"
| "chain \<beta> base (Suc M) f = chain \<beta> base M (stagef (2 ^ M) (twf \<beta> base M) f)"

lemma mod_pow_Suc: "x mod 2 ^ Suc M = 0 \<Longrightarrow> x mod (2::nat) ^ M = 0"
proof -
  assume "x mod 2 ^ Suc M = 0"
  then have "2 ^ Suc M dvd x" by (simp add: mod_eq_0_iff_dvd)
  moreover have "(2::nat) ^ M dvd 2 ^ Suc M" by simp
  ultimately have "2 ^ M dvd x" by (rule dvd_trans[rotated])
  then show ?thesis by (simp add: mod_eq_0_iff_dvd)
qed

lemma div_blk: "r < (W::nat) \<Longrightarrow> (q * W + r) div W = q"
proof -
  assume r: "r < W"
  then have W: "W \<noteq> 0" by auto
  have "(r + q * W) div W = r div W + q" using W by simp
  then show ?thesis using r by (simp add: add.commute)
qed

lemma stagef_shift:
  assumes "S mod 2 ^ Suc si = 0"
  shows "stagef (2 ^ si) (twf \<beta> base si) g (t + S) = stagef (2 ^ si) (twf \<beta> (base + S) si) (\<lambda>j. g (j + S)) t"
proof -
  obtain q where S: "S = 2 ^ Suc si * q" using assms by (auto elim: dvdE simp: mod_eq_0_iff_dvd)
  have r: "(t + S) mod (2 * 2 ^ si) = t mod (2 * 2 ^ si)" by (simp add: S)
  have d: "(t + S) div (2 * 2 ^ si) = t div (2 * 2 ^ si) + q" by (simp add: S)
  have tw: "twf \<beta> base si (t div (2 * 2 ^ si) + q) = twf \<beta> (base + S) si (t div (2 * 2 ^ si))"
    by (simp add: twf_def S algebra_simps)
  have m: "t + S - 2 ^ si = t - 2 ^ si + S" if "\<not> t mod (2 * 2 ^ si) < 2 ^ si"
  proof -
    have "2 ^ si \<le> t mod (2 * 2 ^ si)" using that by simp
    also have "\<dots> \<le> t" by simp
    finally show ?thesis by simp
  qed
  show ?thesis
  proof (cases "t mod (2 * 2 ^ si) < 2 ^ si")
    case True
    have e: "t + S + 2 ^ si = t + 2 ^ si + S" by (simp add: ac_simps)
    show ?thesis unfolding stagef_def Let_def r d tw using True by (simp only: if_True e)
  next
    case False
    show ?thesis unfolding stagef_def Let_def r d tw using False by (simp only: if_False m[OF False])
  qed
qed

lemma chain_shift:
  "S mod 2 ^ M = 0 \<Longrightarrow> chain \<beta> base M g (t + S) = chain \<beta> (base + S) M (\<lambda>j. g (j + S)) t"
proof (induction M arbitrary: g t)
  case 0 then show ?case by simp
next
  case (Suc M)
  have SM: "S mod 2 ^ M = 0" using Suc.prems by (rule mod_pow_Suc)
  have "chain \<beta> base (Suc M) g (t + S) = chain \<beta> (base + S) M (\<lambda>j. stagef (2 ^ M) (twf \<beta> base M) g (j + S)) t"
    by (simp add: Suc.IH[OF SM])
  also have "(\<lambda>j. stagef (2 ^ M) (twf \<beta> base M) g (j + S)) = stagef (2 ^ M) (twf \<beta> (base + S) M) (\<lambda>j. g (j + S))"
    by (rule ext) (rule stagef_shift[OF Suc.prems])
  finally show ?case by simp
qed

lemma chain_local:
  "(\<And>j. j div 2 ^ M = t div 2 ^ M \<Longrightarrow> g j = g' j) \<Longrightarrow> chain \<beta> base M g t = chain \<beta> base M g' t"
proof (induction M arbitrary: g g' t)
  case 0 then show ?case by simp
next
  case (Suc M)
  show ?case
  proof (simp only: chain.simps, rule Suc.IH)
    fix j assume j: "j div 2 ^ M = t div 2 ^ M"
    have dd: "x div 2 ^ Suc M = x div 2 ^ M div 2" for x :: nat by (simp only: power_Suc2 div_mult2_eq)
    have jb: "j div 2 ^ Suc M = t div 2 ^ Suc M" by (simp only: dd j)
    have same: "i div 2 ^ Suc M = t div 2 ^ Suc M \<Longrightarrow> g i = g' i" for i using Suc.prems by simp
    have up: "(j + 2 ^ M) div 2 ^ Suc M = j div 2 ^ Suc M" if "j mod (2 * 2 ^ M) < 2 ^ M"
    proof -
      have "j = j div (2 * 2 ^ M) * (2 * 2 ^ M) + j mod (2 * 2 ^ M)" by (rule div_mult_mod_eq[symmetric])
      then have e: "j + 2 ^ M = j div (2 * 2 ^ M) * (2 * 2 ^ M) + (j mod (2 * 2 ^ M) + 2 ^ M)" by linarith
      have b: "j mod (2 * 2 ^ M) + 2 ^ M < 2 * 2 ^ M" using that by simp
      have "(j + 2 ^ M) div (2 * 2 ^ M) = j div (2 * 2 ^ M)" by (simp only: e div_blk[OF b])
      then show ?thesis by (simp only: power_Suc)
    qed
    have dn: "(j - 2 ^ M) div 2 ^ Suc M = j div 2 ^ Suc M" if "\<not> j mod (2 * 2 ^ M) < 2 ^ M"
    proof -
      have le: "2 ^ M \<le> j mod (2 * 2 ^ M)" using that by simp
      have "j = j div (2 * 2 ^ M) * (2 * 2 ^ M) + j mod (2 * 2 ^ M)" by (rule div_mult_mod_eq[symmetric])
      then have "j - 2 ^ M = j div (2 * 2 ^ M) * (2 * 2 ^ M) + (j mod (2 * 2 ^ M) - 2 ^ M)" using le by linarith
      moreover have b: "j mod (2 * 2 ^ M) - 2 ^ M < 2 * 2 ^ M" by (simp add: less_imp_diff_less)
      ultimately have "(j - 2 ^ M) div (2 * 2 ^ M) = j div (2 * 2 ^ M)" by (simp only: div_blk)
      then show ?thesis by (simp only: power_Suc)
    qed
    have e0: "g j = g' j" by (rule same[OF jb])
    show "stagef (2 ^ M) (twf \<beta> base M) g j = stagef (2 ^ M) (twf \<beta> base M) g' j"
    proof (cases "j mod (2 * 2 ^ M) < 2 ^ M")
      case True
      have "g (j + 2 ^ M) = g' (j + 2 ^ M)" by (rule same) (simp only: up[OF True] jb)
      then show ?thesis unfolding stagef_def Let_def using True e0 by (simp only: if_True)
    next
      case False
      have "g (j - 2 ^ M) = g' (j - 2 ^ M)" by (rule same) (simp only: dn[OF False] jb)
      then show ?thesis unfolding stagef_def Let_def using False e0 by (simp only: if_False)
    qed
  qed
qed

theorem net_fft:
  "base mod 2 ^ M = 0 \<Longrightarrow> t < 2 ^ M \<Longrightarrow> chain \<beta> base M f t = fft \<beta> M base f t"
proof (induction M arbitrary: base f t)
  case 0 then show ?case by simp
next
  case (Suc M)
  define c where "c = cantor \<beta> (base div 2 ^ M)"
  define G where "G = stagef (2 ^ M) (twf \<beta> base M) f"
  define g0 where "g0 = (\<lambda>k. f k + c * f (k + 2 ^ M))"
  define g1 where "g1 = (\<lambda>k. g0 k + f (k + 2 ^ M))"
  have al: "base mod 2 ^ M = 0" using Suc.prems(1) by (rule mod_pow_Suc)
  have tw0: "twf \<beta> base M 0 = c" by (simp add: twf_def c_def)
  have Glo: "G j = g0 j" if "j < 2 ^ M" for j
    using that by (simp add: G_def g0_def stagef_def Let_def tw0 mult.commute)
  have Ghi: "G (j + 2 ^ M) = g1 j" if "j < 2 ^ M" for j
  proof -
    have "(j + 2 ^ M) mod (2 * 2 ^ M) = j + 2 ^ M" "(j + 2 ^ M) div (2 * 2 ^ M) = 0" using that by simp_all
    then show ?thesis by (simp add: G_def g1_def g0_def stagef_def Let_def tw0 algebra_simps)
  qed
  have "chain \<beta> base (Suc M) f t = chain \<beta> base M G t" by (simp add: G_def)
  also have "\<dots> = fft \<beta> (Suc M) base f t"
  proof (cases "t < 2 ^ M")
    case True
    have "chain \<beta> base M G t = chain \<beta> base M g0 t"
      by (rule chain_local) (use True in \<open>auto simp: Glo div_eq_0_iff\<close>)
    also have "\<dots> = fft \<beta> M base g0 t" by (rule Suc.IH[OF al True])
    finally show ?thesis using True by (simp add: Let_def c_def g0_def)
  next
    case False
    define t' where "t' = t - 2 ^ M"
    have t': "t' < 2 ^ M" "t = t' + 2 ^ M" using False Suc.prems(2) by (simp_all add: t'_def)
    have alb: "(base + 2 ^ M) mod 2 ^ M = 0" using al by simp
    have "chain \<beta> base M G t = chain \<beta> (base + 2 ^ M) M (\<lambda>j. G (j + 2 ^ M)) t'"
      unfolding t'(2) by (rule chain_shift) simp
    also have "\<dots> = chain \<beta> (base + 2 ^ M) M g1 t'"
      by (rule chain_local) (use t' in \<open>auto simp: Ghi div_eq_0_iff\<close>)
    also have "\<dots> = fft \<beta> M (base + 2 ^ M) g1 t'" by (rule Suc.IH[OF alb t'(1)])
    finally show ?thesis using False by (simp add: Let_def c_def g0_def g1_def t'_def)
  qed
  finally show ?case .
qed

end
