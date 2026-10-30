theory StageBridge
  imports CantorBridge "HQC_FFT_Math.Network"
begin

lemma s2w_xor3:
  fixes a b c :: "('n::len, bool) seq"
  shows "seq_to_word (map_seq (\<lambda>x. fst x = (fst (snd x) = snd (snd x))) (zip_seq a (zip_seq b c)))
       = seq_to_word a XOR seq_to_word b XOR seq_to_word c"
  by (rule bit_eqI) (auto simp: bit_s2w map_seq_code zip_seq.rep_eq bit_xor_iff nth_zip)

lemma from_nat_word: "(from_nat m :: 'a::len word) = word_of_nat m"
  by (simp add: from_nat_def)

definition gv :: "w64 list \<Rightarrow> gf64 list" where
  "gv xs = map (gfw \<circ> seq_to_word) xs"

text \<open>One butterfly on a list of 2h field elements, in the shape the lifted model computes it:
  lo' = lo + hi c, hi' = hi + lo'.\<close>

definition bfl :: "nat \<Rightarrow> gf64 \<Rightarrow> gf64 list \<Rightarrow> gf64 list" where
  "bfl h c xs = map (\<lambda>(x, y). x + y * c) (zip (take h xs) (drop h xs))
               @ map (\<lambda>(y, x, y'). y + (x + y' * c)) (zip (drop h xs) (zip (take h xs) (drop h xs)))"

lemma butterfly_gf:
  fixes u :: "(2 \<times> 'h::len, w64) seq" and a :: w64
  shows "gv (seq_to_list (FFTRef.butterfly TY('h) a u)) = bfl LENGTH('h) (gfw (seq_to_word a)) (gv (seq_to_list u))"
  by (simp add: FFTRef.butterfly_def Let_def seq_to_list gv_def bfl_def s2w_xor2 s2w_xor3 gfw_xor gf264_gf
      zip_map1 zip_map2 take_map drop_map case_prod_beta)

lemma bfl_nth:
  assumes "length xs = 2 * h" "r < 2 * h"
  shows "bfl h c xs ! r = (if r < h then xs ! r + xs ! (r + h) * c else xs ! r + (xs ! (r - h) + xs ! r * c))"
  using assms by (auto simp: bfl_def nth_append min_def add.commute)

lemma length_bfl [simp]: "length xs = 2 * h \<Longrightarrow> length (bfl h c xs) = 2 * h"
  by (simp add: bfl_def)

lemma nth_concat_eq_len:
  "(\<forall>x\<in>set xss. length x = n) \<Longrightarrow> t < length xss * n \<Longrightarrow> concat xss ! t = xss ! (t div n) ! (t mod n)"
proof (induction xss arbitrary: t)
  case Nil then show ?case by simp
next
  case (Cons x xss)
  show ?case
  proof (cases "t < n")
    case True then show ?thesis using Cons.prems by (simp add: nth_append)
  next
    case False
    then have n0: "0 < n" using Cons.prems by (cases n) auto
    have "t - n < length xss * n" using Cons.prems False by auto
    then have "concat xss ! (t - n) = xss ! ((t - n) div n) ! ((t - n) mod n)" using Cons by simp
    moreover have "t div n = Suc ((t - n) div n)" "t mod n = (t - n) mod n"
      using False n0 by (simp_all add: le_div_geq le_mod_geq not_less)
    ultimately show ?thesis using False Cons.prems by (simp add: nth_append)
  qed
qed

text \<open>One stage as a function of the index: unit mm = t div 2h gets the twiddle tw mm.\<close>

definition stage_fn :: "nat \<Rightarrow> (nat \<Rightarrow> gf64) \<Rightarrow> (nat \<Rightarrow> gf64) \<Rightarrow> nat \<Rightarrow> gf64" where
  "stage_fn h tw f t = (let r = t mod (2 * h); c = tw (t div (2 * h))
     in if r < h then f t + f (t + h) * c else f t + (f (t - h) + f t * c))"

lemma stage_gf:
  fixes p :: "('k::len \<times> 2 \<times> 'h::len, w64) seq" and s :: w64
  assumes "LEN('k) \<le> 2 ^ 32" "t < LENGTH('k) * (2 * LENGTH('h))"
  shows "gv (seq_to_list (FFTRef.stage TY('h) TY('k) s p)) ! t
       = stage_fn LENGTH('h) (\<lambda>mm. Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)))
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
  have "seq_to_list (FFTRef.stage TY('h) TY('k) s p)
      = concat (map (seq_to_list \<circ> (\<lambda>(u, m). FFTRef.butterfly TY('h)
              (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * m) s))) u))
           (zip (map list_to_seq blocks) (map from_nat [0..<K])))"
    by (simp add: FFTRef.stage_def seq_to_list unguard_unfold_context[OF g] blocks_def xs_def K_def H_def)
  then have st: "gv (seq_to_list (FFTRef.stage TY('h) TY('k) s p))
      = concat (map (\<lambda>(b, m). bfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b))
           (zip blocks [0..<K]))"
  proof -
    have tw: "gfw (seq_to_word (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * from_nat m) s))))
            = Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))" for m :: nat
      by (simp add: cantor_gf s2w_xor2 word_seq_convs seq_to_word.from_nat from_nat_word)
    have "gv (seq_to_list (FFTRef.stage TY('h) TY('k) s p))
        = concat (map (\<lambda>(b, m). gv (seq_to_list (FFTRef.butterfly TY('h)
              (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * from_nat m) s))) (list_to_seq b))))
           (zip blocks [0..<K]))"
      by (simp add: \<open>seq_to_list _ = _\<close> gv_def map_concat zip_map_map comp_def prod.case_eq_if)
         (rule arg_cong[where f=concat], rule map_cong, simp_all add: split_beta)
    also have "\<dots> = concat (map (\<lambda>(b, m). bfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b))
           (zip blocks [0..<K]))"
    proof (intro arg_cong[where f=concat] map_cong refl)
      fix bm assume "bm \<in> set (zip blocks [0..<K])"
      then have "fst bm \<in> set blocks" by (metis prod.collapse set_zip_leftD)
      then have "length (fst bm) = 2 * H" by (rule lb)
      then show "(\<lambda>(b, m). gv (seq_to_list (FFTRef.butterfly TY('h)
              (FFTRef.cantor (map_seq (\<lambda>(a', b'). a' = (\<not> b')) (zip_seq (2 * from_nat m) s))) (list_to_seq b)))) bm
          = (\<lambda>(b, m). bfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b)) bm"
        by (cases bm) (simp add: butterfly_gf tw H_def)
    qed
    finally show ?thesis .
  qed
  have lgb: "\<forall>x\<in>set (map (\<lambda>(b, m). bfl H (Cantor.cantor beta (unat ((2 * word_of_nat m) XOR seq_to_word s))) (gv b))
                (zip blocks [0..<K])). length x = 2 * H"
    using lb by (auto simp: gv_def dest!: set_zip_leftD)
  have tK: "t < length (zip blocks [0..<K]) * (2 * H)" using assms(2) by (simp add: blocks_def K_def H_def)
  have tdiv: "t div (2 * H) < K" using assms(2) by (simp add: K_def H_def less_mult_imp_div_less)
  have H0: "0 < H" using assms(2) by (cases H) (auto simp: H_def)
  have "gv (seq_to_list (FFTRef.stage TY('h) TY('k) s p)) ! t
      = bfl H (Cantor.cantor beta (unat ((2 * word_of_nat (t div (2 * H))) XOR seq_to_word s)))
             (gv (blocks ! (t div (2 * H)))) ! (t mod (2 * H))"
  proof -
    have lbk: "length blocks = K" by (simp add: blocks_def)
    show ?thesis using nth_concat_eq_len[OF lgb] tK tdiv by (simp add: st lbk nth_zip)
  qed
  also have "\<dots> = stage_fn H (\<lambda>mm. Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)))
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
      show ?thesis using True r2 by (simp add: bfl_nth[OF lgvq r2] stage_fn_def Let_def a b q_def[symmetric] r_def[symmetric])
    next
      case False
      have a: "gv (blocks ! q) ! r = gv xs ! t" using nth_blk[OF r2] qr by (simp add: q_def)
      have b: "gv (blocks ! q) ! (r - H) = gv xs ! (t - H)"
        using nth_blk[of "r - H"] False r2 qr by (simp add: q_def)
      show ?thesis using False r2 by (simp add: bfl_nth[OF lgvq r2] stage_fn_def Let_def a b q_def[symmetric] r_def[symmetric])
    qed
  qed
  finally show ?thesis by (simp add: xs_def H_def)
qed

lemma stage_fn_is_stagef: "stage_fn = stagef"
  by (intro ext) (simp add: stage_fn_def stagef_def)

definition FV :: "('n, w64) seq \<Rightarrow> nat \<Rightarrow> gf64" where
  "FV p i = gv (seq_to_list p) ! i"

lemma FV_eq: "FV p = (!) (gv (seq_to_list p))"
  by (rule ext) (simp add: FV_def)

definition EqOn :: "nat \<Rightarrow> (nat \<Rightarrow> gf64) \<Rightarrow> (nat \<Rightarrow> gf64) \<Rightarrow> bool" where
  "EqOn N g g' \<longleftrightarrow> (\<forall>i<N. g i = g' i)"

lemma stagef_cong:
  assumes N: "N = K * (2 * h)" and t: "t < N" and g: "EqOn N g g'" and tw: "tw (t div (2 * h)) = tw' (t div (2 * h))"
  shows "stagef h tw g t = stagef h tw' g' t"
proof (cases "t mod (2 * h) < h")
  case True
  have "t div (2 * h) < K" using t N by (simp add: less_mult_imp_div_less)
  then have a: "Suc (t div (2 * h)) * (2 * h) \<le> K * (2 * h)" by (intro mult_le_mono1) simp
  have b: "t = t div (2 * h) * (2 * h) + t mod (2 * h)" by (rule div_mult_mod_eq[symmetric])
  have c: "Suc (t div (2 * h)) * (2 * h) = t div (2 * h) * (2 * h) + 2 * h" by simp
  have "t + h < N" using a b c True N by linarith
  then show ?thesis using True t g tw by (simp add: stagef_def Let_def EqOn_def)
next
  case False
  then show ?thesis using t g tw by (simp add: stagef_def Let_def EqOn_def)
qed

lemma stage_step:
  fixes p :: "('k::len \<times> 2 \<times> 'h::len, w64) seq" and s :: w64
  assumes "LEN('k) \<le> 2 ^ 32" and e: "EqOn (LENGTH('k) * (2 * LENGTH('h))) (FV p) G"
    and tw: "\<And>mm. mm < LENGTH('k) \<Longrightarrow> Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s)) = tw mm"
  shows "EqOn (LENGTH('k) * (2 * LENGTH('h))) (FV (FFTRef.stage TY('h) TY('k) s p)) (stagef LENGTH('h) tw G)"
  unfolding EqOn_def
proof (intro allI impI)
  fix t assume t: "t < LENGTH('k) * (2 * LENGTH('h))"
  have "FV (FFTRef.stage TY('h) TY('k) s p) t
      = stagef LENGTH('h) (\<lambda>mm. Cantor.cantor beta (unat ((2 * word_of_nat mm) XOR seq_to_word s))) (FV p) t"
    using stage_gf[OF assms(1) t] by (simp add: FV_eq stage_fn_is_stagef)
  also have "\<dots> = stagef LENGTH('h) tw G t"
    by (rule stagef_cong[OF refl t e]) (use t in \<open>simp add: tw less_mult_imp_div_less\<close>)
  finally show "FV (FFTRef.stage TY('h) TY('k) s p) t = stagef LENGTH('h) tw G t" .
qed

end
