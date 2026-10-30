theory Hom
  imports DivBridge
begin

text \<open>GF(2) embeds in GF(2^64); the embedding is a ring homomorphism, so a polynomial over GF(2)
  with novel-basis coordinates c has, as a polynomial over GF(2^64), the same coordinates.\<close>

definition emb :: "bit \<Rightarrow> gf64" where "emb b = (if b = 1 then 1 else 0)"

lemma bit_cases': "(b :: bit) = 0 \<or> b = 1"
  by (cases b) auto

interpretation emb: comm_ring_hom emb
proof
  fix x y :: bit
  show "emb (x + y) = emb x + emb y"
    using bit_cases'[of x] bit_cases'[of y] by (auto simp: emb_def)
  show "emb (x * y) = emb x * emb y"
    using bit_cases'[of x] bit_cases'[of y] by (auto simp: emb_def)
  show "emb 1 = 1" by (simp add: emb_def)
  show "emb 0 = 0" by (simp add: emb_def)
qed

interpretation emb_poly: map_poly_comm_ring_hom emb ..

lemma emb_sp: "map_poly emb (sp i) = sp i"
  by (induction i) (simp_all add: emb_poly.hom_add emb_poly.hom_mult)

lemma emb_XPf: "map_poly emb (XPf i k) = XPf i k"
proof (induction k arbitrary: i rule: less_induct)
  case (less k)
  show ?case
  proof (cases "k = 0")
    case True then show ?thesis by simp
  next
    case False
    then have "k div 2 < k" by simp
    then show ?thesis
      by (subst (1 2) XPf_unfold) (simp add: emb_poly.hom_mult less.IH emb_sp)
  qed
qed

lemma emb_XP: "map_poly emb (XP k) = XP k"
  by (simp add: XP_def emb_XPf)

theorem eval_novel_emb:
  fixes p :: "bit poly" and c :: "nat \<Rightarrow> bit"
  assumes "p = (\<Sum>d<n. smult (c d) (XP d))"
  shows "poly (map_poly emb p) x = (\<Sum>d<n. emb (c d) * X d x)"
proof -
  have "map_poly emb p = (\<Sum>d<n. smult (emb (c d)) (XP d))"
    by (simp add: assms emb_poly.hom_sum emb.map_poly_hom_smult emb_XP)
  then show ?thesis by (simp add: poly_novel)
qed

end
