theory GFMul
  imports GFBridge
begin

text \<open>An executable GF(2^64) product on words, for checking facts about the model's constants in
  the kernel (code_simp; no evaluation oracle).\<close>

definition fold64w :: "64 word \<Rightarrow> 128 word" where
  "fold64w h = (let z = (ucast h :: 128 word) in z XOR push_bit 1 z XOR push_bit 3 z XOR push_bit 4 z)"

definition redw :: "128 word \<Rightarrow> 64 word" where
  "redw V = (let w = (ucast (ucast V :: 64 word) :: 128 word) XOR fold64w (ucast (drop_bit 64 V))
             in ucast (w XOR fold64w (ucast (drop_bit 64 w))))"

definition gfmulw :: "64 word \<Rightarrow> 64 word \<Rightarrow> 64 word" where
  "gfmulw a b = redw (foldl (clw_step a b) 0 [0..<64])"

lemma redw_poly: "pw (redw V) = pw V mod PG"
proof -
  define Lo where "Lo = pw (ucast V :: 64 word)"
  define Hi where "Hi = pw (ucast (drop_bit 64 V) :: 64 word)"
  have V: "pw V = Lo + monom 1 64 * Hi"
    using cutoff_shift[of "pw V" 64] by (simp add: Lo_def Hi_def pw_ucast pw_drop_bit)
  have "pw (redw V) = Lo + (Hi + monom 1 (Suc 0) * poly_cutoff 63 Hi + monom 1 3 * poly_cutoff 61 Hi + monom 1 4 * poly_cutoff 60 Hi)
           + ((poly_shift 63 Hi + poly_shift 61 Hi + poly_shift 60 Hi) + monom 1 (Suc 0) * (poly_shift 63 Hi + poly_shift 61 Hi + poly_shift 60 Hi)
              + monom 1 3 * (poly_shift 63 Hi + poly_shift 61 Hi + poly_shift 60 Hi) + monom 1 4 * (poly_shift 63 Hi + poly_shift 61 Hi + poly_shift 60 Hi))"
    by (simp add: redw_def fold64w_def Let_def pw_xor pw_ucast pw_push_bit pw_drop_bit Lo_def Hi_def add.assoc)
  also have "\<dots> = (Lo + monom 1 64 * Hi) mod PG"
    by (rule red_poly_eq) (simp_all add: Lo_def Hi_def coeff_pw_ge)
  finally show ?thesis by (simp add: V)
qed

lemma gfmulw_poly: "pw (gfmulw a b) = (pw a * pw b) mod PG"
  by (simp add: gfmulw_def redw_poly clw_correct)

lemma gfmulw_gf: "gfw (gfmulw a b) = gfw a * gfw b"
  by (rule gfw_eqI) (simp add: gfmulw_poly Rep_gfw)

end
