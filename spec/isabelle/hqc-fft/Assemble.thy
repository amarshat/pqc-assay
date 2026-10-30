theory Assemble
  imports Backward
begin

lemma pl_Pl:
  fixes v :: "('n::len, w64) seq"
  assumes "LENGTH('o::len0) + LENGTH('n) \<le> 560"
  shows "Pl (L (FFTTop.pl TY('o) TY('n) v)) = monom 1 (64 * LENGTH('o)) * Pl (L v)"
  using assms by (simp add: FFTTop.pl_def L_append L_zero L_coerce Pl_append)

lemma seg_L:
  fixes v :: "(('o::len0 + 'n::len) + 'r::len0, w64) seq"
  shows "L (FFTTop.seg TY('o) TY('n) TY('r) v) = take LENGTH('n) (drop LENGTH('o) (L v))"
  by (simp add: FFTTop.seg_def L_take L_drop L_coerce)

lemma Pl_map2_xor: "length xs = length ys \<Longrightarrow> Pl (map2 (XOR) xs ys) = Pl xs + Pl ys"
  by (rule Pl_xor)

lemma Pl_split_seg:
  assumes "off + n + m \<le> length ys"
  shows "Pl (take (n + m) (drop off ys)) = Pl (take n (drop off ys)) + monom 1 (64 * n) * Pl (take m (drop (off + n) ys))"
proof -
  have "Pl (take (n + m) (drop off ys)) = Pl (take n (take (n + m) (drop off ys))) + monom 1 (64 * n) * Pl (drop n (take (n + m) (drop off ys)))"
    using assms by (intro Pl_take_drop) simp
  also have "take n (take (n + m) (drop off ys)) = take n (drop off ys)" by simp
  also have "drop n (take (n + m) (drop off ys)) = take m (drop (off + n) ys)" by (simp add: drop_take add.commute)
  finally show ?thesis .
qed

lemma monom_mm: "monom (1 :: 'a :: comm_ring_1) a * (monom 1 b * p) = monom 1 (a + b) * p"
  by (simp add: mult.assoc[symmetric] mult_monom)

lemma low_split:
  assumes "length xs = 280"
  shows "Pl (take 256 xs) = Pl (take 24 xs) + monom 1 1536 * Pl (take 24 (drop 24 xs)) + monom 1 3072 * Pl (take 24 (drop 48 xs)) + monom 1 4608 * Pl (take 24 (drop 72 xs)) + monom 1 6144 * Pl (take 24 (drop 96 xs)) + monom 1 7680 * Pl (take 24 (drop 120 xs)) + monom 1 9216 * Pl (take 24 (drop 144 xs)) + monom 1 10752 * Pl (take 24 (drop 168 xs)) + monom 1 12288 * Pl (take 24 (drop 192 xs)) + monom 1 13824 * Pl (take 24 (drop 216 xs)) + monom 1 15360 * (Pl (take 8 (drop 240 xs)) + monom 1 512 * Pl (take 8 (drop 248 xs)))"
proof -
  have t: "Pl (take (n + m) (drop off xs)) = Pl (take n (drop off xs)) + monom 1 (64 * n) * Pl (take m (drop (off + n) xs))"
    if "off + n + m \<le> 280" for off n m using Pl_split_seg[of off n m xs] that assms by simp
  show "Pl (take 256 xs) = Pl (take 24 xs) + monom 1 1536 * Pl (take 24 (drop 24 xs)) + monom 1 3072 * Pl (take 24 (drop 48 xs)) + monom 1 4608 * Pl (take 24 (drop 72 xs)) + monom 1 6144 * Pl (take 24 (drop 96 xs)) + monom 1 7680 * Pl (take 24 (drop 120 xs)) + monom 1 9216 * Pl (take 24 (drop 144 xs)) + monom 1 10752 * Pl (take 24 (drop 168 xs)) + monom 1 12288 * Pl (take 24 (drop 192 xs)) + monom 1 13824 * Pl (take 24 (drop 216 xs)) + monom 1 15360 * (Pl (take 8 (drop 240 xs)) + monom 1 512 * Pl (take 8 (drop 248 xs)))"
    by (simp only: t[of 0 24 232, simplified] t[of 24 24 208, simplified] t[of 48 24 184, simplified]
        t[of 72 24 160, simplified] t[of 96 24 136, simplified] t[of 120 24 112, simplified]
        t[of 144 24 88, simplified] t[of 168 24 64, simplified] t[of 192 24 40, simplified]
        t[of 216 24 16, simplified] t[of 240 8 8, simplified])
       (simp add: distrib_left monom_mm add.assoc)
qed

lemma length_L280: "length (L (a :: (280, w64) seq)) = 280"
  by (simp add: L_def)

lemma ypow: "monom (1::gf2) (512 * k) = monom 1 512 ^ k"
  by (simp add: monom_pow mult.commute)

theorem mulT_correct:
  fixes a b :: "(280, w64) seq"
  assumes enc: "\<And>fx. FFTEnc.encode fx = FFTEnc.encodeIdx fx"
    and dec: "\<And>fx. FFTEnc.decode fx = FFTEnc.decodeIdx fx"
  shows "Pl (L (FFTTop.mulT a b (FFTTop.inputT a) (FFTTop.inputT b))) = Pl (L a) * Pl (L b)"
proof -
  define xs where "xs = L a"
  define ys where "ys = L b"
  have lx: "length xs = 280" and ly: "length ys = 280" by (simp_all add: xs_def ys_def length_L280)
  have whole: "Pl zs = Pl (take 256 zs) + monom 1 16384 * Pl (drop 256 zs)" if "length zs = 280" for zs :: "64 word list"
    using Pl_take_drop[of 256 zs] that by simp
  have high: "Pl (drop 256 zs) = Pl (take 16 (drop 256 zs)) + monom 1 1024 * Pl (drop 272 zs)" if "length zs = 280" for zs :: "64 word list"
    using Pl_take_drop[of 16 "drop 256 zs"] that by simp
  have t16: "Pl (take 16 (drop 240 zs)) = Pl (take 8 (drop 240 zs)) + monom 1 512 * Pl (take 8 (drop 248 zs))"
    if "length zs = 280" for zs :: "64 word list"
    using Pl_split_seg[of 240 8 8 zs] that by simp
  have "Pl (L (FFTTop.mulT a b (FFTTop.inputT a) (FFTTop.inputT b)))
      = Pl (take 256 xs) * Pl (take 256 ys) +
     (monom 1 32768 * (Pl (drop 256 xs) * Pl (drop 256 ys)) +
      monom 1 16384 * (Pl (take 24 xs) * Pl (drop 256 ys) + Pl (take 24 ys) * Pl (drop 256 xs)) +
      monom 1 17920 * (Pl (take 24 (drop 24 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 24 ys)) * Pl (drop 256 xs)) +
      monom 1 19456 * (Pl (take 24 (drop 48 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 48 ys)) * Pl (drop 256 xs)) +
      monom 1 20992 * (Pl (take 24 (drop 72 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 72 ys)) * Pl (drop 256 xs)) +
      monom 1 22528 * (Pl (take 24 (drop 96 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 96 ys)) * Pl (drop 256 xs)) +
      monom 1 24064 * (Pl (take 24 (drop 120 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 120 ys)) * Pl (drop 256 xs)) +
      monom 1 25600 * (Pl (take 24 (drop 144 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 144 ys)) * Pl (drop 256 xs)) +
      monom 1 27136 * (Pl (take 24 (drop 168 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 168 ys)) * Pl (drop 256 xs)) +
      monom 1 28672 * (Pl (take 24 (drop 192 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 192 ys)) * Pl (drop 256 xs)) +
      monom 1 30208 * (Pl (take 24 (drop 216 xs)) * Pl (drop 256 ys) + Pl (take 24 (drop 216 ys)) * Pl (drop 256 xs)) +
      monom 1 31744 * (Pl (take 16 (drop 240 xs)) * Pl (take 16 (drop 256 ys)) + Pl (take 16 (drop 240 ys)) * Pl (take 16 (drop 256 xs))) +
      monom 1 32768 * (Pl (take 8 (drop 240 xs)) * Pl (drop 272 ys) + Pl (take 8 (drop 240 ys)) * Pl (drop 272 xs)) +
      monom 1 33280 * (Pl (take 8 (drop 248 xs)) * Pl (drop 272 ys) + Pl (take 8 (drop 248 ys)) * Pl (drop 272 xs)))"
    apply (simp only: FFTTop.mulT_def Let_def)
    apply (simp del: xor_logic_seq add: L_xor L_append L_zero L_coerce Pl_xor Pl_append pl_Pl seg_L L_drop L_take
       fkm24_correct fkm16_correct fkm8_correct fftpart_correct[OF enc dec] xs_def ys_def)
    done
  also have "\<dots> = Pl xs * Pl ys"
  proof -
    define Y where "Y = monom (1::gf2) 512"
    have ys: "monom (1::gf2) 512 = Y ^ 1" "monom (1::gf2) 1024 = Y ^ 2" "monom (1::gf2) 1536 = Y ^ 3" "monom (1::gf2) 3072 = Y ^ 6" "monom (1::gf2) 4608 = Y ^ 9" "monom (1::gf2) 6144 = Y ^ 12" "monom (1::gf2) 7680 = Y ^ 15" "monom (1::gf2) 9216 = Y ^ 18" "monom (1::gf2) 10752 = Y ^ 21" "monom (1::gf2) 12288 = Y ^ 24" "monom (1::gf2) 13824 = Y ^ 27" "monom (1::gf2) 15360 = Y ^ 30" "monom (1::gf2) 16384 = Y ^ 32" "monom (1::gf2) 17920 = Y ^ 35" "monom (1::gf2) 19456 = Y ^ 38" "monom (1::gf2) 20992 = Y ^ 41" "monom (1::gf2) 22528 = Y ^ 44" "monom (1::gf2) 24064 = Y ^ 47" "monom (1::gf2) 25600 = Y ^ 50" "monom (1::gf2) 27136 = Y ^ 53" "monom (1::gf2) 28672 = Y ^ 56" "monom (1::gf2) 30208 = Y ^ 59" "monom (1::gf2) 31744 = Y ^ 62" "monom (1::gf2) 32768 = Y ^ 64" "monom (1::gf2) 33280 = Y ^ 65"
      by (simp_all add: Y_def ypow[symmetric])
    have ex: "Y ^ 32 = Y ^ 30 * Y ^ 2" "Y ^ 35 = Y ^ 30 * (Y ^ 2 * Y ^ 3)" "Y ^ 38 = Y ^ 30 * (Y ^ 2 * Y ^ 6)" "Y ^ 41 = Y ^ 30 * (Y ^ 2 * Y ^ 9)" "Y ^ 44 = Y ^ 30 * (Y ^ 2 * Y ^ 12)" "Y ^ 47 = Y ^ 30 * (Y ^ 2 * Y ^ 15)" "Y ^ 50 = Y ^ 30 * (Y ^ 2 * Y ^ 18)" "Y ^ 53 = Y ^ 30 * (Y ^ 2 * Y ^ 21)" "Y ^ 56 = Y ^ 30 * (Y ^ 2 * Y ^ 24)" "Y ^ 59 = Y ^ 30 * (Y ^ 2 * Y ^ 27)" "Y ^ 62 = Y ^ 30 * (Y ^ 2 * Y ^ 30)" "Y ^ 64 = Y ^ 30 * (Y ^ 2 * (Y ^ 30 * Y ^ 2))" "Y ^ 65 = Y ^ 30 * (Y ^ 2 * (Y ^ 30 * (Y ^ 2 * Y ^ 1)))"
      by (simp_all only: power_add[symmetric]) simp_all
    show ?thesis
      apply (simp only: whole[OF lx] whole[OF ly] high[OF lx] high[OF ly] low_split[OF lx] low_split[OF ly] t16[OF lx] t16[OF ly])
      apply (simp only: ys)
      apply (simp only: ex)
      apply (simp only: algebra_simps)
      done
  qed
  finally show ?thesis by (simp add: xs_def ys_def)
qed

end
