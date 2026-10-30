theory IStageBridge
  imports EncBridge
begin

text \<open>The inverse butterfly and inverse stage of the lifted model as istagef.\<close>

definition ibfl :: "nat \<Rightarrow> gf64 \<Rightarrow> gf64 list \<Rightarrow> gf64 list" where
  "ibfl h c xs = map (\<lambda>(x, y, x'). x + (y + x') * c) (zip (take h xs) (zip (drop h xs) (take h xs)))
               @ map (\<lambda>(y, x). y + x) (zip (drop h xs) (take h xs))"

lemma ibutterfly_gf:
  fixes u :: "(2 \<times> 'h::len, w64) seq" and a :: w64
  shows "gv (seq_to_list (FFTRef.ibutterfly TY('h) a u)) = ibfl LENGTH('h) (gfw (seq_to_word a)) (gv (seq_to_list u))"
  by (simp add: FFTRef.ibutterfly_def Let_def seq_to_list gv_def ibfl_def s2w_xor2 s2w_xor3 gfw_xor gf264_gf
      zip_map1 zip_map2 take_map drop_map case_prod_beta)

lemma ibfl_nth:
  assumes "length xs = 2 * h" "r < 2 * h"
  shows "ibfl h c xs ! r = (if r < h then xs ! r + (xs ! (r + h) + xs ! r) * c else xs ! r + xs ! (r - h))"
  using assms by (auto simp: ibfl_def nth_append min_def add.commute)

lemma length_ibfl [simp]: "length xs = 2 * h \<Longrightarrow> length (ibfl h c xs) = 2 * h"
  by (simp add: ibfl_def)

lemma istage_gf:
  fixes p :: "('k::len \<times> 2 \<times> 'h::len, w64) seq" and s :: w64
  assumes "LEN('k) \<le> 2 ^ 32" "t < LENGTH('k) * (2 * LENGTH('h))"
  shows "gv (seq_to_list (FFTRef.istage TY('h) TY('k) s p)) ! t
       = istagef LENGTH('h) (\<lambda>mm. Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)))
                  (\<lambda>i. gv (seq_to_list p) ! i) t"
proof -
  have g: "PRED('k \<le> 2 ^ 32)" using assms(1) by simp
  define xs where "xs = seq_to_list p"
  define H where "H = LENGTH('h)"
  define K where "K = LENGTH('k)"
  have lx: "length xs = K * (2 * H)" by (simp add: xs_def K_def H_def)
  define blocks where "blocks = group_list K (2 * H) xs"
  have lb: "\<And>b. b \<in> set blocks \<Longrightarrow> length b = 2 * H"
    using group_list_grouped[OF lx] by (simp add: blocks_def)
  have "seq_to_list (FFTRef.istage TY('h) TY('k) s p)
      = concat (map (seq_to_list \<circ> (\<lambda>(u, m). FFTRef.ibutterfly TY('h)
              (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * m) s))) u))
           (zip (map list_to_seq blocks) (map from_nat [0..<K])))"
    by (simp add: FFTRef.istage_def seq_to_list unguard_unfold_context[OF g] blocks_def xs_def K_def H_def)
  then have st: "gv (seq_to_list (FFTRef.istage TY('h) TY('k) s p))
      = concat (map (\<lambda>(b, m). ibfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b))
           (zip blocks [0..<K]))"
  proof -
    have tw: "gfw (seq_to_word (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * from_nat m) s))))
            = Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))" for m :: nat
      by (simp add: cantor_gf s2w_xor2 word_seq_convs seq_to_word.from_nat from_nat_word)
    have "gv (seq_to_list (FFTRef.istage TY('h) TY('k) s p))
        = concat (map (\<lambda>(b, m). gv (seq_to_list (FFTRef.ibutterfly TY('h)
              (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * from_nat m) s))) (list_to_seq b))))
           (zip blocks [0..<K]))"
      by (simp add: \<open>seq_to_list _ = _\<close> gv_def map_concat zip_map_map comp_def prod.case_eq_if)
         (rule arg_cong[where f=concat], rule map_cong, simp_all add: split_beta)
    also have "\<dots> = concat (map (\<lambda>(b, m). ibfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b))
           (zip blocks [0..<K]))"
    proof (intro arg_cong[where f=concat] map_cong refl)
      fix bm assume "bm \<in> set (zip blocks [0..<K])"
      then have "fst bm \<in> set blocks" by (metis prod.collapse set_zip_leftD)
      then have "length (fst bm) = 2 * H" by (rule lb)
      then show "(\<lambda>(b, m). gv (seq_to_list (FFTRef.ibutterfly TY('h)
              (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * from_nat m) s))) (list_to_seq b)))) bm
          = (\<lambda>(b, m). ibfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b)) bm"
        by (cases bm) (simp add: ibutterfly_gf tw H_def)
    qed
    finally show ?thesis .
  qed
  have lgb: "\<forall>x\<in>set (map (\<lambda>(b, m). ibfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b))
                (zip blocks [0..<K])). length x = 2 * H"
    using lb by (auto simp: gv_def dest!: set_zip_leftD)
  have tK: "t < length (zip blocks [0..<K]) * (2 * H)" using assms(2) by (simp add: blocks_def K_def H_def)
  have tdiv: "t div (2 * H) < K" using assms(2) by (simp add: K_def H_def less_mult_imp_div_less)
  have H0: "0 < H" using assms(2) by (cases H) (auto simp: H_def)
  have "gv (seq_to_list (FFTRef.istage TY('h) TY('k) s p)) ! t
      = ibfl H (Cantor.cantor beta (unat ((2 * word_of_nat (t div (2 * H))) XOR seq_to_word s)))
             (gv (blocks ! (t div (2 * H)))) ! (t mod (2 * H))"
  proof -
    have lbk: "length blocks = K" by (simp add: blocks_def)
    show ?thesis using nth_concat_eq_len[OF lgb] tK tdiv by (simp add: st lbk nth_zip)
  qed
  also have "\<dots> = istagef H (\<lambda>mm. Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)))
                  (\<lambda>i. gv xs ! i) t"
  proof -
    have lgv: "length (gv (blocks ! (t div (2 * H)))) = 2 * H"
      using lb tdiv by (simp add: gv_def blocks_def)
    have nth_blk: "gv (blocks ! (t div (2 * H))) ! r = gv xs ! (t div (2 * H) * (2 * H) + r)" if "r < 2 * H" for r
    proof -
      have "Suc (t div (2 * H)) * (2 * H) \<le> K * (2 * H)" using tdiv by (intro mult_le_mono1) simp
      then have "t div (2 * H) * (2 * H) + r < length xs" using that lx by simp
      then show ?thesis using that tdiv lx by (simp add: gv_def blocks_def group_list_elem)
    qed
    have tt: "t div (2 * H) * (2 * H) + t mod (2 * H) = t" by (rule div_mult_mod_eq)
    define q where "q = t div (2 * H)"
    define r where "r = t mod (2 * H)"
    have r2: "r < 2 * H" using H0 by (simp add: r_def)
    have qr: "q * (2 * H) + r = t" using tt by (simp add: q_def r_def)
    have lgvq: "length (gv (blocks ! q)) = 2 * H" using lgv by (simp add: q_def)
    show ?thesis
    proof (cases "r < H")
      case True
      have a: "gv (blocks ! q) ! r = gv xs ! t" using nth_blk[OF r2] qr by (simp add: q_def)
      have b: "gv (blocks ! q) ! (r + H) = gv xs ! (t + H)"
        using nth_blk[of "r + H"] True qr by (simp add: q_def add.assoc[symmetric])
      show ?thesis using True r2 by (simp add: ibfl_nth[OF lgvq r2] istagef_def Let_def a b q_def[symmetric] r_def[symmetric])
    next
      case False
      have a: "gv (blocks ! q) ! r = gv xs ! t" using nth_blk[OF r2] qr by (simp add: q_def)
      have b: "gv (blocks ! q) ! (r - H) = gv xs ! (t - H)"
        using nth_blk[of "r - H"] False r2 qr by (simp add: q_def)
      show ?thesis using False r2 by (simp add: ibfl_nth[OF lgvq r2] istagef_def Let_def a b q_def[symmetric] r_def[symmetric])
    qed
  qed
  finally show ?thesis by (simp add: xs_def H_def)
qed


lemma istage_step:
  fixes p :: "('k::len \<times> 2 \<times> 'h::len, w64) seq" and s :: w64
  assumes "LEN('k) \<le> 2 ^ 32" and e: "EqOn (LENGTH('k) * (2 * LENGTH('h))) (FV p) G"
    and tw: "\<And>mm. mm < LENGTH('k) \<Longrightarrow> Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)) = tw mm"
  shows "EqOn (LENGTH('k) * (2 * LENGTH('h))) (FV (FFTRef.istage TY('h) TY('k) s p)) (istagef LENGTH('h) tw G)"
  unfolding EqOn_def
proof (intro allI impI)
  fix t assume t: "t < LENGTH('k) * (2 * LENGTH('h))"
  have "FV (FFTRef.istage TY('h) TY('k) s p) t
      = istagef LENGTH('h) (\<lambda>mm. Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s))) (FV p) t"
    using istage_gf[OF assms(1) t] by (simp add: FV_eq)
  also have "\<dots> = istagef LENGTH('h) tw G t"
  proof -
    have h0: "t mod (2 * LENGTH('h)) < 2 * LENGTH('h)" using t by (cases "LENGTH('h)") auto
    have tq: "t div (2 * LENGTH('h)) < LENGTH('k)" using t by (simp add: less_mult_imp_div_less)
    have a: "t div (2 * LENGTH('h)) * (2 * LENGTH('h)) + 2 * LENGTH('h) \<le> LENGTH('k) * (2 * LENGTH('h))"
      using tq by (metis add.commute mult_Suc mult_le_mono1 Suc_leI)
    have b: "t = t div (2 * LENGTH('h)) * (2 * LENGTH('h)) + t mod (2 * LENGTH('h))" by (rule div_mult_mod_eq[symmetric])
    have up: "t + LENGTH('h) < LENGTH('k) * (2 * LENGTH('h))" if "t mod (2 * LENGTH('h)) < LENGTH('h)"
      using a b that by linarith
    show ?thesis
      using e t tq up by (auto simp: istagef_def Let_def EqOn_def tw)
  qed
  finally show "FV (FFTRef.istage TY('h) TY('k) s p) t = istagef LENGTH('h) tw G t" .
qed

lemma istage_step_num:
  fixes p :: "('k::len \<times> 2 \<times> 'h::len, w64) seq" and s :: w64
  assumes "LENGTH('h) = h" "LENGTH('k) = k" "k * (2 * h) = N" "k \<le> 2 ^ 32"
    and "EqOn N (FV p) G"
    and "\<And>mm. mm < k \<Longrightarrow> Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)) = tw mm"
  shows "EqOn N (FV (FFTRef.istage TY('h) TY('k) s p)) (istagef h tw G)"
  using istage_step[of p G s tw] assms by simp

theorem ibtfy9_ichain:
  fixes sc :: w64 and p :: "(512, w64) seq"
  assumes sc: "seq_to_word sc = 2 ^ 41" and e: "EqOn 512 (FV p) f"
  shows "EqOn 512 (FV (FFTRef.ibtfy9 sc p)) (ichain beta (2 ^ 41) 9 f)"
proof -
  have tw0: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word sc)) = twf beta (2 ^ 41) 0 mm" if "mm < 256" for mm
  proof -
    have "seq_to_word sc = drop_bit 0 (2 ^ 41)" by (simp only: sc) simp
    then show ?thesis using tw_level[of 41 0 9 mm] that by simp
  qed
  have tw1: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc 1))) = twf beta (2 ^ 41) 1 mm" if "mm < 128" for mm
  proof -
    have "seq_to_word (right_shift sc 1) = drop_bit 1 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 1 9 mm] that by simp
  qed
  have tw2: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (2::int)))) = twf beta (2 ^ 41) 2 mm" if "mm < 64" for mm
  proof -
    have "seq_to_word (right_shift sc (2::int)) = drop_bit 2 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 2 9 mm] that by simp
  qed
  have tw3: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (3::int)))) = twf beta (2 ^ 41) 3 mm" if "mm < 32" for mm
  proof -
    have "seq_to_word (right_shift sc (3::int)) = drop_bit 3 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 3 9 mm] that by simp
  qed
  have tw4: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (4::int)))) = twf beta (2 ^ 41) 4 mm" if "mm < 16" for mm
  proof -
    have "seq_to_word (right_shift sc (4::int)) = drop_bit 4 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 4 9 mm] that by simp
  qed
  have tw5: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (5::int)))) = twf beta (2 ^ 41) 5 mm" if "mm < 8" for mm
  proof -
    have "seq_to_word (right_shift sc (5::int)) = drop_bit 5 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 5 9 mm] that by simp
  qed
  have tw6: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (6::int)))) = twf beta (2 ^ 41) 6 mm" if "mm < 4" for mm
  proof -
    have "seq_to_word (right_shift sc (6::int)) = drop_bit 6 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 6 9 mm] that by simp
  qed
  have tw7: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (7::int)))) = twf beta (2 ^ 41) 7 mm" if "mm < 2" for mm
  proof -
    have "seq_to_word (right_shift sc (7::int)) = drop_bit 7 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 7 9 mm] that by simp
  qed
  have tw8: "Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word (right_shift sc (8::int)))) = twf beta (2 ^ 41) 8 mm" if "mm < 1" for mm
  proof -
    have "seq_to_word (right_shift sc (8::int)) = drop_bit 8 (2 ^ 41)" by (simp only: s2w_rshift sc) simp
    then show ?thesis using tw_level[of 41 8 9 mm] that by simp
  qed
  have chb: "ichain beta b 9 f = istagef 256 (twf beta b 8) (istagef 128 (twf beta b 7) (istagef 64 (twf beta b 6) (istagef 32 (twf beta b 5) (istagef 16 (twf beta b 4) (istagef 8 (twf beta b 3) (istagef 4 (twf beta b 2) (istagef 2 (twf beta b 1) (istagef 1 (twf beta b 0) (f)))))))))" for b
  proof -
    have n: "(9::nat) = Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (0)))))))))" by simp
    show ?thesis by (simp only: n ichain.simps) (simp add: numeral_eq_Suc)
  qed
  have ch: "ichain beta (2 ^ 41) 9 f = istagef 256 (twf beta (2 ^ 41) 8) (istagef 128 (twf beta (2 ^ 41) 7) (istagef 64 (twf beta (2 ^ 41) 6) (istagef 32 (twf beta (2 ^ 41) 5) (istagef 16 (twf beta (2 ^ 41) 4) (istagef 8 (twf beta (2 ^ 41) 3) (istagef 4 (twf beta (2 ^ 41) 2) (istagef 2 (twf beta (2 ^ 41) 1) (istagef 1 (twf beta (2 ^ 41) 0) (f)))))))))"
    by (rule chb)
  have nf: "FFTRef.ibtfy9 sc p = (coerce_seq_len (FFTRef.istage TY(256) TY(1) (right_shift sc (8::int)) (coerce_seq_len (FFTRef.istage TY(128) TY(2) (right_shift sc (7::int)) (coerce_seq_len (FFTRef.istage TY(64) TY(4) (right_shift sc (6::int)) (coerce_seq_len (FFTRef.istage TY(32) TY(8) (right_shift sc (5::int)) (coerce_seq_len (FFTRef.istage TY(16) TY(16) (right_shift sc (4::int)) (coerce_seq_len (FFTRef.istage TY(8) TY(32) (right_shift sc (3::int)) (coerce_seq_len (FFTRef.istage TY(4) TY(64) (right_shift sc (2::int)) (coerce_seq_len (FFTRef.istage TY(2) TY(128) (right_shift sc 1) (coerce_seq_len (FFTRef.istage TY(1) TY(256) sc (coerce_seq_len p)))))))))))))))))) :: (512, w64) seq)"
    by (simp add: FFTRef.ibtfy9_def)
  show ?thesis
    unfolding nf ch
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw8, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw7, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw6, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw5, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw4, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw3, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw2, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw1, simp)
    apply (subst FV_coerce, simp)
    apply (rule istage_step_num, simp, simp, simp, simp)
     prefer 2 apply (rule tw0, simp)
    apply (subst FV_coerce, simp)
    by (rule e)
qed

end
