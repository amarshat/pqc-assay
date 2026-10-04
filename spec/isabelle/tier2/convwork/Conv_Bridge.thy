(* v4 O8: transform, multiply pointwise, transform back, and the result is the negacyclic product.

   Composes four results that were proven separately:
     ntt_signed_correct     (Signed_Bridge)      the forward model is the FIPS-204 transform mod q
     pointwise_bridge       (Pointwise_Bridge)   the pointwise model multiplies with a 2^-32 factor
     invntt_signed_correct  (Inv_Signed_Bridge)  the inverse model is the inverse transform, scaled
     conv_int               (Conv_Ring)          the convolution theorem at q = 8380417
   and does the Montgomery bookkeeping between them. pointwise leaves 2^-32, invntt leaves
   2^-32 * invf with invf = 41978, and the unnormalised inverse leaves a factor 256. Since
   invf * 256 == 2^64 (mod q), the three cancel exactly and the theorem has no residual factor.

   All three models are the SAW-checked Cryptol, lifted. The hypothesis is the centered input
   window |coeff| < q on both operands; the intermediate bounds (forward output within 9q, pointwise
   input within the montgomery precondition, pointwise output within q) are derived here. *)
theory Conv_Bridge
  imports "Tier2_Signed.Signed_Bridge" "Tier2_InvSigned.Inv_Signed_Bridge"
          "Tier2.Pointwise_Bridge" "Tier2_Inv.Conv_Ring"
begin

context includes cryptol_syntax begin

declare [[coercion_enabled = false]]

subsection \<open>Bounds between the stages\<close>

lemma ntt_out_bounded:
  assumes nb0: "ntt_bounded 8380416 a"
  shows "ntt_bounded 75423752 (ntt a)"
proof -
  have nb1: "ntt_bounded 16760833 (nttLevel 0 a)" using nttLevel_bounded[OF nb0] by simp
  have nb2: "ntt_bounded 25141250 (nttLevel 1 (nttLevel 0 a))" using nttLevel_bounded[OF nb1] by simp
  have nb3: "ntt_bounded 33521667 (nttLevel 2 (nttLevel 1 (nttLevel 0 a)))"
    using nttLevel_bounded[OF nb2] by simp
  have nb4: "ntt_bounded 41902084 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 a))))"
    using nttLevel_bounded[OF nb3] by simp
  have nb5: "ntt_bounded 50282501 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 a)))))"
    using nttLevel_bounded[OF nb4] by simp
  have nb6: "ntt_bounded 58662918
               (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 a))))))"
    using nttLevel_bounded[OF nb5] by simp
  have nb7: "ntt_bounded 67043335
               (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3 (nttLevel 2 (nttLevel 1 (nttLevel 0 a)))))))"
    using nttLevel_bounded[OF nb6] by simp
  have nb8: "ntt_bounded 75423752
               (nttLevel 7 (nttLevel 6 (nttLevel 5 (nttLevel 4 (nttLevel 3
                  (nttLevel 2 (nttLevel 1 (nttLevel 0 a))))))))"
    using nttLevel_bounded[OF nb7] by simp
  show ?thesis unfolding ntt_unfold by (rule nb8)
qed

text \<open>The forward outputs are not reduced, so the pointwise inputs can reach \<open>9q\<close>. The product is
still inside the montgomery window: \<open>75423752^2 = 5688742365757504 < 2^31 q = 17996808470921216\<close>.\<close>

lemma mont_input_ok_of_9q:
  fixes x y :: int
  assumes x: "- 75423752 \<le> x" "x \<le> 75423752" and y: "- 75423752 \<le> y" "y \<le> 75423752"
  shows "mont_input_ok (x * y)"
proof -
  have ax: "\<bar>x\<bar> \<le> 75423752" using x by (simp add: abs_le_iff)
  have ay: "\<bar>y\<bar> \<le> 75423752" using y by (simp add: abs_le_iff)
  have "\<bar>x * y\<bar> \<le> 75423752 * 75423752" unfolding abs_mult using ax ay by (intro mult_mono) auto
  hence "\<bar>x * y\<bar> \<le> 5688742365757504" by simp
  thus ?thesis unfolding mont_input_ok_def MLDSA_NTT_Spec.q_def by (simp add: abs_le_iff)
qed

lemma pointwise_ok:
  assumes bx: "ntt_bounded 75423752 x" and by': "ntt_bounded 75423752 y"
  shows "mont_input_ok (sint_seq (nth_seq x k) * sint_seq (nth_seq y k))"
  using bx by' unfolding ntt_bounded_def by (intro mont_input_ok_of_9q) auto

lemma pointwise_out_bounded:
  assumes bx: "ntt_bounded 75423752 x" and by': "ntt_bounded 75423752 y"
  shows "ntt_bounded 8380416 (pointwise x y)"
proof -
  have out: "- 8380416 \<le> sint_seq (nth_seq (pointwise x y) k)
           \<and> sint_seq (nth_seq (pointwise x y) k) \<le> 8380416" if k: "k < 256" for k
  proof -
    have "- 8380417 < sint_seq (nth_seq (pointwise x y) k)
          \<and> sint_seq (nth_seq (pointwise x y) k) < 8380417"
      using mont_butterfly_bound[OF pointwise_ok[OF bx by', of k]]
      by (simp add: nth_seq_pointwise[OF k])
    thus ?thesis by linarith
  qed
  show ?thesis
    unfolding ntt_bounded_def
  proof (intro allI)
    fix n
    show "- 8380416 \<le> sint_seq (nth_seq (pointwise x y) n)
          \<and> sint_seq (nth_seq (pointwise x y) n) \<le> 8380416"
    proof (cases "n < 256")
      case True thus ?thesis using out by blast
    next
      case False hence ge: "256 \<le> n" by simp
      show ?thesis using out[of 255] oob255[OF ge, of "pointwise x y"] by simp
    qed
  qed
qed

subsection \<open>The scale constants\<close>

lemma invf_val: "sint_seq invf = 41978"
  unfolding invf_def probe_sint_seq by (simp add: word_seq_convs)

text \<open>\<open>invf \<cdot> 256 \<equiv> 2^64\<close> and \<open>7593442 \<cdot> 2^64 \<equiv> 1\<close> (mod q). Small numerals, closed by \<open>simp\<close>.\<close>

lemma invf_256: "[41978 * 256 = (18446744073709551616::int)] (mod 8380417)"
  by (simp add: cong_def)

lemma inv_2_64: "[7593442 * 18446744073709551616 = (1::int)] (mod 8380417)"
  by (simp add: cong_def)

subsection \<open>The composed theorem\<close>

theorem ntt_mult_correct:
  assumes ba: "ntt_bounded 8380416 a" and bb: "ntt_bounded 8380416 b" and k: "k < 256"
  shows "sint_seq (nth_seq (invntt (pointwise (ntt a) (ntt b))) k) mod 8380417
       = negconv_int (sf a) (sf b) k mod 8380417"
proof -
  let ?X = "ntt a" and ?Y = "ntt b"
  let ?P = "pointwise ?X ?Y"
  let ?C = "invntt ?P"
  define A where "A t = (\<Sum>j<256. sf a j * 1753 ^ ((2 * t + 1) * j))" for t
  define B where "B t = (\<Sum>j<256. sf b j * 1753 ^ ((2 * t + 1) * j))" for t
  define z where "z t = zpw (- (2 * int t + 1) * int k)" for t
  have bX: "ntt_bounded 75423752 ?X" by (rule ntt_out_bounded[OF ba])
  have bY: "ntt_bounded 75423752 ?Y" by (rule ntt_out_bounded[OF bb])
  have bP: "ntt_bounded 8380416 ?P" by (rule pointwise_out_bounded[OF bX bY])

  \<comment> \<open>forward: position m holds the transform at frequency brv 8 m\<close>
  have fx: "[sf ?X m = A (brv 8 m)] (mod 8380417)" if m: "m < 256" for m
    using ntt_signed_correct[OF ba m] unfolding cong_def A_def sf_def by simp
  have fy: "[sf ?Y m = B (brv 8 m)] (mod 8380417)" if m: "m < 256" for m
    using ntt_signed_correct[OF bb m] unfolding cong_def B_def sf_def by simp
  \<comment> \<open>pointwise: 2^32 * P_m == X_m * Y_m\<close>
  have pw: "[4294967296 * sf ?P m = sf ?X m * sf ?Y m] (mod 8380417)" if m: "m < 256" for m
    using pointwise_bridge[OF m pointwise_ok[OF bX bY]] unfolding cong_def sf_def by simp
  \<comment> \<open>inverse: 2^32 * C_k == invf * S\<close>
  have iv: "[4294967296 * sf ?C k = 41978 * (\<Sum>m<256. sf ?P m * z (brv 8 m))] (mod 8380417)"
    using invntt_signed_correct[OF bP k] unfolding cong_def sf_def z_def invf_val by simp

  \<comment> \<open>2^32 * S == sum over output positions of A * B * z, then reindex by brv 8\<close>
  have s1: "[4294967296 * (\<Sum>m<256. sf ?P m * z (brv 8 m))
              = (\<Sum>m<256. A (brv 8 m) * B (brv 8 m) * z (brv 8 m))] (mod 8380417)"
  proof -
    have "4294967296 * (\<Sum>m<256. sf ?P m * z (brv 8 m))
            = (\<Sum>m<256. (4294967296 * sf ?P m) * z (brv 8 m))"
      by (simp add: sum_distrib_left mult.assoc)
    also have "[\<dots> = (\<Sum>m<256. A (brv 8 m) * B (brv 8 m) * z (brv 8 m))] (mod 8380417)"
    proof (rule cong_sum)
      fix m assume "m \<in> {..<256::nat}"
      hence m: "m < 256" by simp
      have "[4294967296 * sf ?P m = A (brv 8 m) * B (brv 8 m)] (mod 8380417)"
        using cong_trans[OF pw[OF m] cong_mult[OF fx[OF m] fy[OF m]]] .
      thus "[4294967296 * sf ?P m * z (brv 8 m) = A (brv 8 m) * B (brv 8 m) * z (brv 8 m)]
              (mod 8380417)"
        by (rule cong_mult) (rule cong_refl)
    qed
    finally show ?thesis .
  qed
  have reidx: "(\<Sum>m<256. A (brv 8 m) * B (brv 8 m) * z (brv 8 m))
                 = (\<Sum>t<256. A t * B t * z t)"
  proof -
    have bij: "bij_betw (brv 8) {..<256} {..<256}"
      using brv_bij[of 8] by (simp add: atLeast0LessThan)
    show ?thesis
      by (rule sum.reindex_bij_betw[OF bij, where g = "\<lambda>t. A t * B t * z t"])
  qed
  \<comment> \<open>the convolution theorem\<close>
  have cv: "[(\<Sum>t<256. A t * B t * z t) = 256 * negconv_int (sf a) (sf b) k] (mod 8380417)"
    using conv_int[OF k, of "sf a" "sf b"] unfolding cong_def A_def B_def z_def zpw_def by simp

  \<comment> \<open>assemble: 2^64 * C_k == invf * 256 * N == 2^64 * N\<close>
  have "[18446744073709551616 * sf ?C k
          = 4294967296 * (41978 * (\<Sum>m<256. sf ?P m * z (brv 8 m)))] (mod 8380417)"
    using cong_scalar_left[OF iv, of 4294967296] by simp
  also have "4294967296 * (41978 * (\<Sum>m<256. sf ?P m * z (brv 8 m)))
               = 41978 * (4294967296 * (\<Sum>m<256. sf ?P m * z (brv 8 m)))"
    by (simp only: mult.left_commute)
  also have "[\<dots> = 41978 * (\<Sum>t<256. A t * B t * z t)] (mod 8380417)"
    using cong_scalar_left[OF s1[unfolded reidx], of 41978] .
  also have "[41978 * (\<Sum>t<256. A t * B t * z t)
               = 41978 * (256 * negconv_int (sf a) (sf b) k)] (mod 8380417)"
    using cong_scalar_left[OF cv, of 41978] .
  also have "41978 * (256 * negconv_int (sf a) (sf b) k)
               = (41978 * 256) * negconv_int (sf a) (sf b) k"
    by (simp only: mult.assoc)
  also have "[\<dots> = 18446744073709551616 * negconv_int (sf a) (sf b) k] (mod 8380417)"
    using cong_mult[OF invf_256 cong_refl] .
  finally have big: "[18446744073709551616 * sf ?C k
                        = 18446744073709551616 * negconv_int (sf a) (sf b) k] (mod 8380417)" .
  \<comment> \<open>cancel 2^64 with its inverse mod q\<close>
  have "[sf ?C k = (7593442 * 18446744073709551616) * sf ?C k] (mod 8380417)"
    using cong_mult[OF cong_sym[OF inv_2_64] cong_refl, of "sf ?C k"] by simp
  also have "(7593442 * 18446744073709551616) * sf ?C k
               = 7593442 * (18446744073709551616 * sf ?C k)" by (simp only: mult.assoc)
  also have "[\<dots> = 7593442 * (18446744073709551616 * negconv_int (sf a) (sf b) k)] (mod 8380417)"
    using cong_scalar_left[OF big, of 7593442] .
  also have "7593442 * (18446744073709551616 * negconv_int (sf a) (sf b) k)
               = (7593442 * 18446744073709551616) * negconv_int (sf a) (sf b) k"
    by (simp only: mult.assoc)
  also have "[\<dots> = negconv_int (sf a) (sf b) k] (mod 8380417)"
    using cong_mult[OF inv_2_64 cong_refl, of "negconv_int (sf a) (sf b) k"] by simp
  finally show ?thesis unfolding cong_def sf_def .
qed


text \<open>The same theorem read in \<open>R_q = Z_q[X]/(X^256 + 1)\<close>: the output coefficients of
\<open>invntt (pointwise (ntt a) (ntt b))\<close>, as a polynomial over \<open>Z_q\<close>, are the product of the input
polynomials reduced mod \<open>X^256 + 1\<close>.\<close>

corollary ntt_mult_ring:
  assumes ba: "ntt_bounded 8380416 a" and bb: "ntt_bounded 8380416 b"
  shows "Poly (map (\<lambda>k. of_int (sf (invntt (pointwise (ntt a) (ntt b))) k) :: fin8380417 mod_ring)
                   [0..<256])
       = (Poly (map (\<lambda>j. of_int (sf a j)) [0..<256]) * Poly (map (\<lambda>j. of_int (sf b j)) [0..<256]))
           mod (monom 1 256 + 1)"
proof (rule negconv_int_ring)
  fix k :: nat assume k: "k < 256"
  show "sf (invntt (pointwise (ntt a) (ntt b))) k mod 8380417
          = negconv_int (sf a) (sf b) k mod 8380417"
    using ntt_mult_correct[OF ba bb k] by (simp only: sf_def)
qed

end

end
