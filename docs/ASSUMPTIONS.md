# Trust base & assumptions

A proof is only meaningful relative to what it assumes. This file is the honest ledger.
**Update it the moment any assumption is introduced.** Reviewers will read this first.

## Standing assumptions
- **Compiler correctness.** We verify C (via its LLVM bitcode) and the FIPS spec; we assume the
  compiler faithfully lowers verified C. (Same assumption Apple states for corecrypto.)
- **Tool soundness.** We trust SAW, Cryptol, the cryptol-to-isabelle translator, and Isabelle.
- **Spec faithfulness.** We assume our (independently written, no Apple artifacts) Isabelle
  specification faithfully captures the intended Montgomery-reduction behavior / FIPS 204.
  Provenance noted in spec/README.md.

## Scope limits (v1)
- **Scope is the reduce.c layer plus forward-NTT functional equivalence.** SAW proves all four
  reduce.c primitives ≡ Cryptol model (`montgomery_reduce` under its precondition; `reduce32` under
  `a <= 2^31-2^22-1`; `caddq` unconditional; `freeze` compositional), AND the forward NTT
  `ntt(a[256])` ≡ Cryptol `ntt` under two's-complement wrapping (see overflow note below). The
  Isabelle model≡spec leg covers the **whole `reduce.c` layer** (`montgomery_reduce`, `caddq`,
  `reduce32`, `freeze`). The forward NTT is proven equal to the model under wrapping AND its
  **overflow-freedom / coefficient-bound composition is now proven in Isabelle** (`ntt_overflow_free`,
  v1.5; see proof results below). The Isabelle model≡FIPS forward-NTT-transform theorem is now proven
  too (`fwd_ntt_correct`, `Tier2` session, gated in `make verify`), but it is about the **normal-domain**
  lifted model `nttFwdAllRef`, not the **montgomery-domain** model the SAW C≡Cryptol leg checks. The
  bridge linking them (montgomery ≡ normal, mod q, in `work/Mont_Bridge.thy`) is now fully proven:
  per-layer (`mbfly0`..`mbfly7`, plus the per-position layer unfolds) and composed over all 8 layers
  into `ntt_bridge`: `bounded w ⟹ k<256 ⟹ sint_seq (ntt w ! k) mod q = (∑ j<256. cf w j ·
  ζ^((2·brv₈ k + 1)·j)) mod q`, with `ntt` the montgomery model the SAW C≡Cryptol leg checks. So the
  C→FIPS forward-NTT chain is closed mod q (both ends and the bridge machine-checked). The
  `-fwrapv` ⇒ no-signed-overflow-UB meta-step, formerly this chain's one argued link, is now
  MECHANIZED for the forward direction (2026-07-10): `proof/saw/ntt_nsw.saw` (`make ntt-nsw`)
  verifies `ntt()` on the DEFAULT (nsw) bitcode under the `±(2³¹−2²⁷)` input window, discharging
  all ~3000 signed-overflow side conditions AND functional equality to the model in one proof
  (SAW 1.5.1 + bitwuzla 0.9.1, a trusted SMT oracle in the same class as z3/yices; 12.5 h wall,
  out of band, not in `make saw`/CI). The inverse's meta-step remains argued (see below).
  ★ FORWARD FUNCTIONAL NOW ON THE SIGNED CENTERED WINDOW (2026-08-01, `Tier2_Signed` builds exit 0, no
  sorry/oops/smt, in-session verified, gated in `make verify` via `tier2-signed`): `ntt_signed_correct`
  (`spec/isabelle/tier2/signwork/Signed_Bridge.thy`) lifts the FUNCTIONAL forward bridge from the
  non-negative `[0,Q)` window (`ntt_bridge`, `bounded w` = unsigned `< Q`) to the SIGNED centered window
  `|coeff| < Q` (`ntt_bounded 8380416 w`), the inputs the deployed reference forward NTT actually receives
  (keygen/sign feed centered `s1`/`s2` coefficients that can be negative): `ntt_bounded 8380416 w ⟹ k<256
  ⟹ sint_seq (ntt w ! k) mod q = (∑ j<256. sf w j · ζ^((2·brv₈ k+1)·j)) mod q`, where `sf w j =
  sint_seq (w j)` is the SIGNED coefficient value. Route (cheap, ~200 lines, all existing machinery
  reused): the abstract closed form `applyN_inv` holds for ANY integer coefficient function (no
  non-negativity), and `mbfly0..7` already land on the signed view `sf`, so propagating
  `sf(ntt w) ≡ fwdBfly(sf w) (mod q)` (`sf_ntt_eq_fwdbfly`, a mirror of `ntt_bridge`'s Rcong chain but
  with a REFLEXIVE base `sf w ≡ sf w` instead of `sf w = cf w`, which is where non-negativity entered)
  dissolves the `[0,Q)` restriction. So on the deployed centered forward inputs we now have BOTH
  overflow-freedom AND functional model-to-spec equality. The `-fwrapv`⇒no-UB meta-step is unchanged
  (mechanized for the forward via `ntt_nsw.saw`).
- **Inverse NTT: functional chain (under `[0,Q)`) AND overflow-freedom (under signed `|coeff| < Q`, covers the call site) machine-checked.** SAW
  proves `invntt_tomont(a[256])` ≡ Cryptol montgomery `invntt` under two's-complement wrapping (same
  `-fwrapv` bitcode as the forward). The Isabelle chain is closed mod q: montgomery model ≡ normal
  `nttInvAllRef` (`Rcong_invcore` + the `invf = mont²/256` final scale, `invntt_scale_bridge`),
  `nttInvAllRef` ≡ the FIPS-204 inverse negacyclic DFT (`inv_ntt_correct`), composed into
  `invntt_bridge`: `bounded w ⟹ k<256 ⟹ 4294967296 · sint(invntt w ! k) ≡ sint(invf) · (∑ m<256.
  cf w m · ζ^(−(2·brv₈ m + 1)·k)) (mod q)` (`Tier2_InvWork` session, gated in `make verify` via
  `tier2-inv`). The functional bridge `invntt_bridge` uses the input predicate `bounded w` = every
  coefficient's UNSIGNED 32-bit value `< Q`, i.e. coefficients in `[0, Q)`, NON-NEGATIVE
  (`spec/isabelle/tier2/work/CT_Routing.thy:20`: `uint_seq (w i) < 8380417`); this is NOT the symmetric
  signed `|coeff| < Q`. `B_0 = 8380416` is the DERIVED output bound.
  ★ OVERFLOW-FREEDOM NOW ON THE SIGNED CALL-SITE WINDOW (2026-07-22, `Tier2_InvWork` builds exit 0, no
  sorry/oops): `invntt_overflow_free` is re-proven under `sbounded w` = signed `|coeff| < Q`
  (`-8380416 ≤ sint_seq (w i) ≤ 8380416`, defined in `Inv_Mont_Bridge.thy`), the CENTERED domain the
  reference's `montgomery_reduce`/`reduce32` outputs occupy at the `invntt_tomont` call site (they are
  centered and can be negative). So the overflow result now DOES cover the deployed call site, closing the
  former `[0,Q)` scope gap for overflow-freedom. Why it was cheap and NOT the "real work" an earlier
  version of this ledger predicted: the eight-layer bound tower (`invlevel*_bounded`, `gs_node_*`,
  `invlevel_bounded_gen`) runs entirely on the symmetric-signed magnitude predicate `ntt_bounded` and is
  sign-agnostic; the input window enters ONLY through the level-0 base bound (`ntt_bounded_of_sbounded`),
  so lifting `[0,Q)` → signed `|coeff| < Q` is a base-case swap, and the overflow bound does NOT depend on
  the montgomery-vs-normal functional bridge. `sbounded` subsumes the old `bounded` window
  (`sbounded_of_bounded`), so the theorem is non-vacuous. The `|coeff| < Q` window is `invntt_tomont`'s
  DOCUMENTED precondition (target/pqclean/ntt.c:71-73: inputs `|coeff| < Q`, outputs `|coeff| < Q`), not a
  tightness argument: the GS low leg is unreduced so the bound doubles per level, reaching
  `256*(Q-1) = 2145386496 < 2^31` after 8 levels. (Earlier ledger + comment wording "256*Q would not fit
  int32" was WRONG: 256*Q = 2145386752 < 2^31 = 2147483648, headroom ~2.1M. The true int32-safe ceiling is
  `B_0 <= 2^23-1 = 8388607`, above `Q-1 = 8380416` by ~8191, so `|coeff| < Q` sits inside it with slack; a
  full doubling to a `2Q` window WOULD overflow: `512*(Q-1) = 4290772992 > 2^31`.)
  ★ GAP NOW CLOSED (functional, inverse) ,  2026-08-02: `invntt_signed_correct`
  (`spec/isabelle/tier2/invsignwork/Inv_Signed_Bridge.thy`, session `Tier2_InvSigned`, no sorry/oops/smt,
  in-session verified, gated in `make verify` via `tier2-invsigned`) lifts the FUNCTIONAL inverse bridge
  from `[0,Q)` to the signed centered `|coeff| < Q` window (`ntt_bounded 8380416 w`): `ntt_bounded 8380416
  w ⟹ k<256 ⟹ (2^32 · sint(invntt w!k)) mod q = (sint(invf) · (∑ m<256. sf w m · zpw(−(2·brv₈ m+1)·k))) mod
  q`, the RHS over the SIGNED coefficient values `sf w m` (was `cf w m` = unsigned in `invntt_bridge`).
  Route, exactly the forward's + the scale: `invntt_scale_bridge` split into (i) a SIGN-AGNOSTIC scale
  part (`invntt_scale_coeff` + `invf_scale_cong`: `2^32·sf(invntt w) ≡ invf·sf(invnttCore w) mod q`, whose
  only bound need `invcore_bounded_nb` already runs on the signed `ntt_bounded`) and (ii) ONE `[0,Q)`-locked
  step (`Rcong_invcore`: `sf(invnttCore w) ≡ cf(nttInvAllRef w) mod q`). Only (ii) was replaced, by the
  abstract route `sf(invnttCore w) ≡ invBfly(sf w) mod q` (`mbfly_inv0..7` already on `sf` + a reflexive
  base) composed with the abstract closed form `applyG_inv` (holds for any coefficient function). The
  earlier ledger's prediction that this needed "re-deriving the bridge over signed coefficients" (the
  "real work") was WRONG: the abstract closed form + reflexive base made it as cheap as the forward.
  So BOTH NTT directions now have machine-checked functional model-to-spec equality on the signed centered
  window the deployed code uses (overflow-freedom was already there for both). No `[0,Q)` functional
  restriction remains anywhere in the NTT chain.
  The `-fwrapv` ⇒ no-signed-overflow-UB step for the inverse is still argued (not mechanized; the nsw SAW
  route was measured impractical), but now rests on an overflow bound covering the signed call-site window
  rather than only `[0,Q)`.
- Input range: the C documents the precondition `-2^31 * Q <= a <= Q * 2^31`. The SAW proof IS
  discharged under exactly this precondition (`mont_in_range` in the model); equivalence outside it
  is NOT claimed by the proof. (Empirically the Cryptol model is a bit-exact transcription that also
  matches the C outside the range, but that is not what SAW asserts.)
- **Call-site reachability (practical-safety context).** The *verified contract* (`|a| <= 2^31*Q
  ~= 2^54`) is ~256x wider than what ML-DSA actually feeds this function: pointwise-multiply and NTT
  butterflies produce products `<~ Q^2 ~= 2^46`. So OF-1's problematic endpoint (`a = 2^31*Q`) is
  unreachable in any real ML-DSA execution; the reference is mathematically correct in practice.
- **Parameter-set independence.** `montgomery_reduce` is byte-identical across ML-DSA-44/65/87 (same
  `Q`, `QINV`, `reduce.c`); the proof holds for all three. The "-44" pin is cosmetic for this function.
- **C undefined-behavior / overflow setting.** Two bitcodes are built (`scripts/build_bitcode.sh`):
  - *default (`nsw`)* ,  used for the **reduce.c** proofs, which therefore DO assert absence of
    signed-overflow UB in their documented input ranges (`montgomery_reduce` under `mont_in_range`,
    `reduce32` under `a <= 2^31-2^22-1`).
  - *`-fwrapv`* ,  used for the **forward and inverse NTT** functional proofs. The NTT does unreduced
    int32 add/sub (`a[j] ± t`) that overflow for unbounded inputs, so we prove functional equivalence
    under two's-complement wrapping (what the code computes; matches the mod-2^n model), for all
    inputs with no bound. **Forward: the nsw side is now ALSO proven directly** (2026-07-10,
    `proof/saw/ntt_nsw.saw`, `make ntt-nsw`): on the default (nsw) bitcode, under inputs in
    `±(2³¹−2²⁷)`, every signed add/sub is overflow-free and the result equals the model (SAW +
    bitwuzla, 12.5 h, out of band). The Isabelle `ntt_overflow_free` bound is the induction-style
    twin of the same fact on the model, so the forward `-fwrapv` ⇒ no-UB step is no longer an
    assumption on that domain. The **inverse** is overflow-free on the model under signed `|coeff| < Q`
    (`invntt_overflow_free` under `sbounded`, 2026-07-22; see the inverse-NTT scope bullet above), the
    centered domain that DOES cover the reference call site's `montgomery_reduce`/`reduce32` outputs; its
    `-fwrapv` ⇒ no-UB seam REMAINS the argued meta-step, but now rests on a bound covering that call-site
    window rather than only `[0,Q)`. (The functional `invntt_bridge` model≡FIPS leg is still `[0,Q)`;
    that gap is separate and open.) A direct nsw-build attempt for the inverse (2026-07-10..12, `proof/saw/
    invntt_nsw_probe.saw` + the goal-dump sweep) was closed as impractical: of 4609 obligations,
    3747 discharged unsat (most in seconds), 36 hit a 2 h per-goal cap, none was sat, and the
    late-level band (where the Gentleman-Sande doubling makes terms widest) resists the same
    bitwuzla abstraction-refinement that crossed the forward's unroll. Measured boundary datum,
    recorded in the script header; the inverse link stays argued.
  - *the polynomial layer* (2026-10-11): `proof/saw/poly_nsw.saw` runs the poly.c / polyvec.c
    functions on the multiplication paths on the default bitcode; see A-ROW item 3 for what it
    covers. It uses z3 only. The pinned bitwuzla 0.9.1 binary that `ntt_nsw.saw` needs links
    Homebrew's `libgmp` and `libmpfr`; until 2026-10-24 the development machine lacked `mpfr`, which
    is why earlier notes said the binary "does not load on macOS 13". With `brew install mpfr` it
    loads there. `make ntt-nsw` was still not re-run on it (12.5 h).
- Anything not listed as proven is, explicitly, NOT proven.

## v2 (Rust / RustCrypto `ml-dsa`) assumptions
- **Assumed specs for the constant-time primitive layer (inline asm SAW cannot read).** The crate's
  arithmetic bottoms out in CT primitives that SAW (MIR/LLVM) cannot translate, so the reduce proofs
  (`implementations/rustcrypto-ml-dsa/proof/reduce/reduce.saw`) replace them with `mir_unsafe_assume_spec`
  *assumed* specs. These are sound iff each spec reproduces the primitive's true input/output relation;
  they are NOT verified against the asm (SAW cannot see it). This is the standard SAW handling of
  inline-asm/intrinsic leaves, but it IS part of the trust base:
  - `<u32 as cmov::Cmov>::cmovnz` (`cmov-0.5.4 backends::aarch64::{impl#1}`): assumed
    `*self = (condition != 0) ? *value : *self`. Justified by reading the asm (`tst {cond},0xff;
    csel {self},{value},{self},NE`) ,  `csel ...,NE` selects `value` when the `tst` cleared Z, i.e.
    when `condition != 0`. This is exactly the crate's documented `cmovnz` ("move if non-zero")
    contract. It is the only asm primitive on the `reduce` path.
  - `<u32 as cmov::CmovEq>::cmoveq` (`cmov-0.5.4 backends::aarch64::{impl#4}`, reached via ctutils
    `ct_eq` in `decompose`): assumed `*output = (*self == *rhs) ? input : *output`. Justified by
    reading the asm (cseleq32: `eor t,{lhs},{rhs}; cmp t,0; csel {out},{input},{out},EQ` , 
    `csel ...,EQ` selects `input` exactly when `lhs ^ rhs == 0`; the surrounding Rust truncates the
    u16 temp back to the u8 `*output`, and all values flowing in are u8-range). Used by the hint-layer
    proofs (2026-06-12). The `cmovne`/u16/u64 variants are NOT overridden (not on any verified path).
  - `core::hint::black_box`: assumed identity (it is an optimizer barrier with no semantic effect).
- **Which `reduce` instances are covered (v2.2, 2026-06-12): ALL THREE moduli the crate uses.**
  The harness's sign/verify entry points force the M = q = 8380417 (final z reduction via
  `mod_plus_minus::<SpecQ>`) and M = 2*gamma2 = 190464 (Decompose) monomorphizations in addition to
  keygen's M = 2^d = 8192 (Power2Round). All three are proven `reduce(x) == x mod M` for **all**
  `u32 x`, no precondition: 2^d because the power-of-two Barrett shift is exact, q and 2*gamma2
  because both exceed 2^16 so the standard `x < M^2` Barrett condition covers the whole u32 domain , 
  and for those two the conditional-subtract branch is LIVE (the genuinely bug-prone Barrett-precision
  case), checked exactly by Z3 over all u32. **Parameter-set scope:** 2*gamma2 = 190464 is the
  ML-DSA-44 value; ML-DSA-65/87 use 2*gamma2 = 523776, a distinct monomorphization not in this MIR
  and not claimed (q and 2^d are parameter-set-independent).
- **Wide-Barrett spec for the NTT field layer (escape-2): CLOSED 2026-07-04.** The NTT
  butterflies multiply two field elements (`a,b < q < 2^23`) giving a product `< 2^46`, reduced by
  `module_lattice`/`ml_dsa`'s `barrett_reduce` (u64→u128 multiply by `8396807 = floor(2^46/q)`,
  `>> 46`, one conditional subtract). `proof/ntt/field_ops_bridged.saw` proves the `Elem` field core
  (`neg/add/sub/mul == arithmetic mod q`, shared with ml-kem) by chaining `mul` on a spec for
  `barrett_reduce`: `barrett_reduce(x) == x mod q for all x < 2^46`, supplied via
  `mir_unsafe_assume_spec` for speed. That spec is **no longer an admit**: it is proven directly on
  the deployed MIR (see CLOSED bullet). The `mir_unsafe_assume_spec` stays in `field_ops_bridged.saw`
  only so the fast field-op proofs don't each pay the ~23 min bitwuzla cost.
  - **CLOSED (2026-07-04, SAW + bitwuzla, `proof/ntt/barrett_reduce_bitwuzla.saw`):**
    `barrett_reduce(x) == x mod q for all x < 2^46` is a real `mir_verify` on the deployed RustCrypto
    MIR, discharged by SAW's What4 **bitwuzla** backend (`w4_unint_bitwuzla`), pinned bitwuzla 0.9.1.
    Tool-confirmed this session: mir_verify exit 0 in 1402s; the core BV goal (`escape2_barrett_bv.smt2`)
    is `unsat` in 551s; non-vacuity holds (a `+1` spec is rejected in 596s, and the `Q+1` mutant flips
    to `sat` instantly). This is the goal every eager bit-blaster stalls on (z3 3h15m without
    converging, saw-script #3306; z3/cvc5/yices/abc all time out past `2^34`); bitwuzla's CEGAR
    multiplier abstraction crosses it. Trust: bitwuzla is a trusted SMT oracle, the **same trust class**
    as the z3/yices used throughout this SAW development, so this is not a new kind of assumption. For
    an **oracle-free** proof of the same math, Route Y (below) stands as the complementary alternative.
    Cost means it runs out of band, not in the fast CI leg. bitwuzla is pinned in `scripts/setup.sh`.
    The bullets below record how the obligation was decomposed and narrowed before this direct closure.
  - EARNED (z3): `proof/ntt/escape2_core.saw` proves the Barrett identity `barrettInt X == X % q`
    over all `X ∈ [0, 2^46)` as an **unbounded-Integer** goal (the form that dodges bit-blasting).
  - EARNED (z3): `proof/ntt/barrett_bridge_evidence.saw` proves the **exact bit-vector mirror** of
    the impl arithmetic (`barrett_bridge.cry::barrettBV`) equals `x % q` for `x < 2^24` ,  i.e. the
    model used to reason about the impl is correct at tractable width.
  - ADMITTED (the gap): the BV↔bounded-Integer lift at width ~66+ (product `< 2^69`).
    SAW has no native tactic for it; hand-built bridge lemmas themselves cliff at W=64, and the
    direct `mir_verify` residual (`impl == barrettBV`) bit-blasts the wide multiply + `>>46` , 
    z3 ran **3h15m without converging** (measured 2026-06-17). This is saw-script discussion #3306,
    confirmed by SAW maintainer RyanGlScott: SMT tools "fundamentally struggle with" Barrett.
  - REDUCED (2026-07-02, `proof/ntt/spike2_lift.saw`, saw exit 0): the admitted gap above is
    demonstrated equivalent to **nine standard bvToInt homomorphisms**, not the whole function.
    `spike2_lift.saw` proves `barrettBV x == x mod q for x < 2^46` with the *only* admitted content
    being `toInteger` pushed through zext, `*`, `>>k`, `-`, truncate (each in unconditional
    `mod 2^n` form), plus `smallReduce`, `urem`-by-q, and the `==`/`<` reflections. The lifted
    Integer core is EARNED (cvc5; z3 stalls on the nested `mod 2^128`); the bridge then closes by
    specializing that core onto the goal (`goal_insert_and_specialize`) and modus ponens (z3). Each
    homomorphism is witnessed true in-file (z3 at small width; quickcheck-500 at full width for the
    nonlinear multiply/urem/smallReduce, which cliff for eager SMT ,  hence admitted). Companion
    `proof/ntt/spike1_endgame.saw` (saw exit 0) confirms the residual's lifted target is exactly the
    escape2_core identity. This is a demonstration of the reduced trust base; it is NOT yet wired
    into `field_ops_bridged.saw`, which still carries the whole-function admit above. De-admitting
    the nine (Route X: a SAWCore `bvToInt`-lifting tactic / Prelude lemmas; Route Y: Isabelle
    `Word_Lib` `unat`/`uint` lemmas) removes the assumption entirely.
  - MECHANIZED (2026-07-03, Route Y, Isabelle `Word_Lib`, `make barrett` / session `Barrett` exit 0):
    the nine bvToInt homomorphisms are de-admitted **as a word-model identity**. Theorem
    `spec/isabelle/tier2/barrett/Barrett_Bridge.thy::barrettBV_bridge_holds` proves `barrettBV_bridge x`:
    for `x < 2^46`, `barrettBV x` (the lifted BV Barrett model) equals `drop`{96} ((zext x) % q)`
    (`x mod q` truncated to 32 bits), with **no sorry/oops/admit and no smt**. The proof pushes `uint`
    through each word op onto the integer core: `ucast`/zext via `uint_up_ucast`, the two multiplies via
    `uint_word_ariths` (no overflow, product `< 2^69 < 2^128`), `>> 46` via `uint_shiftr_eq`, the subtract
    via `uint_sub_lem` (no underflow, `quot*q \<le> x`), truncate via `unsigned_ucast_eq`/`unsigned_take_bit_eq`
    (remainder `< 2q < 2^32`), `urem` via `uint_mod_distrib`, and the `==`/`<`/`\<le>` reflections via
    `word_uint_eq_iff`/`word_less_def`/`word_le_def`. It closes on the exported `Barrett_Core` facts
    `barrett_core` (the escape2_core integer identity) and `barrett_core_bounds`. Kernel-checked soundness:
    an `ML` block in `Barrett_Bridge.thy` runs `Thm_Deps.has_skip_proof`/`Thm_Deps.all_oracles` on the
    theorem and fails the build if the transitive cone uses ANY oracle, so "no smt / no sorry" is checked
    by the Isabelle kernel, not by grep. The lifted model is tool-gated: `scripts/lift_check_barrett.sh`
    (in `make barrett`) requires `Barrett_Lift.thy` to be byte-identical to
    `cryptol-to-isabelle(barrett_bridge.cry)` modulo the theory-name rename, so `barrettBV` here is the
    lift of the same `.cry` SAW reasons about, not a hand-transcription. Wired into `make verify` and CI.
    ROLE AFTER THE 2026-07-04 CLOSURE: Route Y proves the arrow `barrettBV == x mod q` with **no oracle**
    (kernel-checked). It is no longer the only route past the admit: the CLOSED bullet above proves the
    deployed `barrett_reduce == x mod q` directly on the MIR via bitwuzla. The two are complementary on a
    trust spectrum: bitwuzla discharges the deployed goal directly but trusts the solver; Route Y proves
    the word-model identity with no trusted solver, for higher assurance. The earlier belief that closing
    the admit required proving the SAT-hard `MIR == barrettBV` miter turned out to be unnecessary,
    bitwuzla proves `MIR == x mod q` directly. Not claimed: "first/novel verification of Barrett"
    (libcrux/hax verify ML-DSA `barrett_reduce` on deployed Rust; CryptoLine/Jazzline verify
    Kyber/Dilithium Barrett+NTT via algebra + range-SMT), nor "SMT fundamentally cannot verify Barrett"
    (the boundary is precisely eager bit-blasting vs abstraction-refinement, now measured: z3/cvc5/yices/abc
    stall, bitwuzla crosses it). The defensible contribution is the specific combination: a reproducible,
    deliberately-honest audit of an *unmodified third-party* RustCrypto ML-DSA impl via MIR-level SAW, with
    the one hard obligation both discharged by a multiplier-strong solver and given an oracle-free Isabelle
    proof, and the eager-vs-abstraction boundary characterized with numbers.
  Soundness: the escape-2 spec `barrett_reduce == x mod q` (x < 2^46) is now a proven `mir_verify` on the
  deployed MIR (SAW + bitwuzla, non-vacuity checked), same solver-trust class as the rest of the SAW leg,
  with an oracle-free Isabelle proof of the same identity as the complementary high-assurance route. The
  `mir_unsafe_assume_spec` in `field_ops_bridged.saw` is kept only for speed and is discharged by
  `barrett_reduce_bitwuzla.saw`. Same q = 8380417 (Dilithium) Barrett constants as the verified scalar
  `reduce` layer; the narrow `x < 2^28` BV form also proves directly in SAW (4.2s), and the full `x < 2^46`
  form now proves via bitwuzla (~23 min).
- **NTT layer proofs treat the field ops as uninterpreted routing symbols (2026-06-18).**
  `proof/ntt/layer_ntt_fwd.saw` / `layer_ntt_inv.saw` prove all 8 forward (`ntt_layer`) and 8 inverse
  (`ntt_inverse_layer`) layers equal to the FIPS 204 Alg 41/42 butterfly bodies. To make the goal
  tractable, the four `Elem` field ops are replaced (via `mir_unsafe_assume_spec`, no precondition)
  with **named, uninterpreted** Cryptol functions `addS/subS/mulS/negS`, and the proof is the
  *structural butterfly routing* (`w4_unint_z3`). What this means for the trust base:
  - The layer theorem says: *with each field op treated as an opaque function, `ntt_layer` wires the
    butterflies exactly as Alg 41/42 specifies* (correct indices, operand order, zeta selection,
    `m`-counter sequencing). It does NOT, by itself, assert the ops compute mod-q arithmetic.
  - The ops' arithmetic correctness (`add/sub/neg/mul == · mod q`) is the SEPARATE, **proven**
    obligation in `field_ops_bridged.saw` (which carries the escape-2 barrett assumption above).
    The two compose: proven routing ∘ proven (mod-q) leaves = the layer computes the Alg 41/42 map.
  - `negS` is kept *interpreted* on the inverse side (the impl const-folds `-ZETA[m]` to a literal).
  - Faithfulness of the compositional spec to the independent FIPS transcription (`fips204_ntt.cry`)
    is checked in `comp_faithful.saw` over test vectors for all 16 (len,iter,m0). Non-vacuity:
    each layer file rejects a +1-perturbed spec (`fails`). NOT assumed beyond the above; the
    coefficient-stays-in-range (no Elem invariant violation) property is the v1 overflow-freedom
    story, not re-established here.
- **NTT composition: layers mechanized, 8-layer call order by-inspection (2026-06-18, Tier 1).**
  The full forward/inverse NTT is the 8-fold composition of the verified layers. Mechanized
  (saw exit 0): each of the 16 layers (impl == FIPS Alg 41/42 body), and the *composed spec* is
  faithful to the independent `% q` transcription plus round-trip-consistent (`inv(fwd(w)) == 256·w
  mod q`, the 256^-1 tail scaling being outside the layers) ,  `proof/ntt/ntt_full_check.saw`.
  NOT mechanized: that the pinned `ntt()` invokes those 8 layers *in that exact order*. The
  implementation's `Polynomial::ntt` / `NttPolynomial::ntt_inverse` are `pub(crate)` (correct
  encapsulation, not a defect) and the full transform is inlined, so there is no callable entry to
  SAW-verify without modifying the vendored, pinned target ,  which we deliberately do NOT do (the
  pin is the value: we verify the crate as published). The call order is therefore taken
  **by inspection** of the pinned source (`ml-dsa-0.1.1/src/ntt.rs:80-87` forward / `142-149`
  inverse). This is the SAME category of trust as the existing "the harness's sign/verify entry
  points force the monomorphizations" reachability assumption above ,  cheap to eyeball, pin-breaking
  to mechanize. It is NOT a correctness gap in the layers; it is a reachability/wiring fact about
  which verified pieces run in which order.
- **Pinned, vendored target.** `ml-dsa 0.1.1` + `module-lattice 0.2.3` (provenance in
  `implementations/rustcrypto-ml-dsa/target/`). mir-json schema v8 = the commit SAW 1.5.1 bundles.

## Modeling choices for `montgomery_reduce` (model/cryptol/MLDSA_NTT.cry)
- Modeled at the **exact C bit widths** (`[64] -> [32]`), not over idealized `Integer`, because SAW
  checks bit-for-bit equivalence and the algorithm depends on two's-complement truncation/shift.
- `*` on `[n]` = multiply mod 2^n → matches C's wrapping `(uint64_t)` product and low bits of
  `(int64_t)t * Q`. `drop`{32}` = keep low 32 bits → matches the `(int32_t)` casts and the final
  int64→int32 assignment. `>>$` = ARITHMETIC right shift → matches `>> 32` on a signed `int64_t`
  (plain logical `>>` would be wrong here).
## Proof results (what a tool actually checked, and when)
- **C ≡ Cryptol for `montgomery_reduce`: VERIFIED.** `make saw` exits 0 on 2026-06-06.
  - Tool: SAW v1.5.1, solver Z3 (bundled). Bitcode: Apple clang 17 `-O0 -g`, `build/mldsa_ntt.bc`.
  - Claim discharged: `∀ a:[64]. mont_in_range a ⇒ C(a) == montgomery_reduce(a)`, i.e. the C function
    `PQCLEAN_MLDSA44_CLEAN_montgomery_reduce` returns exactly the model's value for every input in
    `-2^31*Q ≤ a ≤ Q*2^31`. Nothing outside that range is claimed.
  - SAW output: `Proof succeeded! PQCLEAN_MLDSA44_CLEAN_montgomery_reduce`.
  - **Non-vacuity checked.** A control run with a deliberately wrong model (`result + 1`) made SAW
    fail with counterexample `a = 0`, confirming the precondition is satisfiable and the equality
    postcondition is really being asserted. (An earlier control swapping `>>$`→`>>` correctly still
    passed ,  for this function the shift-by-32-then-truncate makes arithmetic/logical shift
    equivalent, so it is not a behavioral change.)
- **C ≡ Cryptol for reduce32 / caddq / freeze: VERIFIED** (`make saw`, exit 0). `reduce32` under
  `a <= 2^31-2^22-1` (bounds the `a+(1<<22)` add against int32 overflow); `caddq` unconditional;
  `freeze` proven compositionally using the `reduce32`/`caddq` overrides, inheriting reduce32's
  precondition.
- **C ≡ Cryptol for the forward NTT `ntt(a[256])`: VERIFIED under two's-complement wrapping**
  (`make saw`, exit 0). Proven on the `-fwrapv` bitcode (so all inputs, no bound precondition), with
  `montgomery_reduce` passed as an override and kept uninterpreted (`w4_unint_z3`) so the 1024
  butterfly calls reduce to a structural array equality. The Cryptol `ntt` model was also concretely
  cross-checked against the C on two input vectors.
- **Forward NTT overflow-freedom (model level, Isabelle): VERIFIED (2026-06-11).** `make verify`
  exits 0, no `sorry`/`oops`. Theorem `ntt_overflow_free` (`spec/isabelle/Assay_Equivalence.thy`):
  for inputs with every coefficient in `+/-(2^31 - 2^27)`, the lifted model NTT keeps every
  coefficient in `+/-2080309256 < 2^31 - 1` through all 8 levels. The per-butterfly lemmas
  (`sint_add/sub_inrange`, `butterfly_node_*_bound`) establish that **every int32 add/sub stays in
  `[-2^31, 2^31)` ,  no overflow** ,  and that every `montgomery_reduce` input stays in its half-open
  precondition (so the OF-1 endpoint is never hit). Proof = induction over 8 levels (`nttLevel_bounded`:
  one level grows `|coeff|` by `<= Q`, the montgomery output bound `|t| < Q` from
  `montgomery_reduce_correct`), with a *total* coefficient invariant that sidesteps modular index
  reasoning (OOB index = last element). This is the coefficient-bound composition that the `-fwrapv`
  functional-equivalence proof deliberately sidesteps.
  - **C-side claim (argued, not separately mechanized):** SAW gives C ≡ model for all inputs under
    `-fwrapv`; Isabelle shows the model does not wrap under the bound; the nsw and `-fwrapv` bitcodes
    differ only in signed-overflow poison, absent when no overflow occurs. Hence the reference C NTT
    is overflow-free (no signed-overflow UB) and equals the spec under the bound. The brute-force SAW
    mechanization of this bridge was computationally impractical (~3000 obligations; see ROADMAP /
    branch `v1.5-saw-overflow-wip`); the meta-level argument is standard and sound.
- The earlier 16-vector C-vs-Cryptol concrete cross-check (2026-06-01) remains as a secondary
  sanity check; the SAW proof above supersedes it for all in-range inputs.

- **model ≡ FIPS/math spec (Isabelle leg): VERIFIED (2026-06-07).** `make verify` (SAW + Isabelle)
  exits 0; `isabelle build -D spec/isabelle Assay` checks `montgomery_reduce_correct` with NO `sorry`
  / NO `oops`. Theorem: the cryptol-to-isabelle-lifted `montgomery_reduce` satisfies
  `is_montgomery_reduction (sint_seq a) (sint_seq (montgomery_reduce a))`, i.e. `2^32*r ≡ a (mod Q)`
  and strict `-Q < r < Q`, for every `a` with `-2^31*Q ≤ sint a < 2^31*Q` (half-open; see OF-1).
  Proof structure: `mont_core` (integer core) + `probe_bridge` (seq→word) + `red_value`
  (sint of the word computation = `(A - T*Q) div 2^32`, no overflow) + `tcong` (`T ≡ A*QINV mod 2^32`).
  - Trust base note: relies on `cryptol-to-isabelle` translating the Cryptol model faithfully (tool
    soundness assumption) and on the SAW Cryptol support library + AFP (`Word_Lib`,
    `Berlekamp_Zassenhaus`). Prerequisite built by `scripts/setup_isabelle_cryptol.sh` (AFP
    `afp-2026-06-05`; heavy).
  - **Chaining:** with the SAW leg (C ≡ Cryptol model) this gives end-to-end: the deployed C
    `montgomery_reduce` computes a correct Montgomery residue mod Q. Note the two legs use slightly
    different input predicates ,  SAW proves C ≡ model over the INCLUSIVE range `-2^31*Q ≤ a ≤ Q*2^31`
    (`mont_in_range`), while the Isabelle correctness spec uses the HALF-OPEN `-2^31*Q ≤ a < 2^31*Q`
    (`mont_input_ok`, where the strict `-Q<r<Q` actually holds; OF-1). The composed end-to-end
    correctness claim therefore holds on the half-open intersection (which is the honest, maximal
    domain for the strict-bound spec).
- **model ≡ spec for reduce32 / caddq / freeze (Isabelle leg): VERIFIED (2026-06-08).**
  `isabelle build -D spec/isabelle Assay` exits 0, no `sorry`/`oops`. The lifted Cryptol models satisfy:
  - `caddq_correct`: `is_caddq` (residue-preserving; maps `[-Q,Q)` into `[0,Q)`) ,  unconditional.
  - `reduce32_correct`: `is_reduce32` (residue-preserving; output in the TRUE window
    `[-6283009, 6283008]`, see OF-2) over the SAW domain `a <= 2^31-2^22-1`. The output-bound proof
    is a floor-division interval argument with a case split at the extreme quotient `t = -256`.
  - `freeze_correct`: `is_freeze` (residue-preserving; output in `[0,Q)`) over the same domain,
    proven compositionally ,  reduce32's window `[-6283009, 6283008]` lies in `[-Q, Q)`, satisfying
    caddq's precondition. Chained with the SAW leg this gives C ≡ spec for the full `reduce.c` layer.
- **NOT proven:** an Isabelle model≡FIPS-spec for the NTT *transform* (we have C≡model + model-level
  overflow-freedom, not the negacyclic-transform correctness); the full SAW mechanization of the
  nsw/`-fwrapv` overflow bridge; optimized/native code; constant-time.
- **RustCrypto ml-dsa Barrett `reduce`, all three moduli: VERIFIED (2026-06-12).**
  `saw implementations/rustcrypto-ml-dsa/proof/reduce/reduce.saw` exits 0 (SAW 1.5.1 + Z3, MIR via
  mir-json schema v8, nightly-2025-09-14). Claims discharged, each for **all** `u32 x` with no
  precondition: `reduce(x) == x mod q` (q = 8380417), `reduce(x) == x mod 190464` (2*gamma2,
  ML-DSA-44), `reduce(x) == x mod 8192` (2^d). The q and 2*gamma2 instances exercise the live
  conditional-subtract branch (Barrett precision). **Non-vacuity checked:** mutating each modulus in
  the spec (8380416 / 190465 / 8191) makes SAW fail with a counterexample. Trust base: the two
  assumed CT-layer specs above ("v2 assumptions") plus mir-json translation soundness.
- **RustCrypto ml-dsa scalar hint layer == FIPS 204 Algorithms 36/37/39/40: VERIFIED (2026-06-12).**
  `saw implementations/rustcrypto-ml-dsa/proof/hint/hint.saw` exits 0 (4 proofs). Claims, each for
  every field element (`x < q`, the crate's `Elem` domain), ML-DSA-44 monomorphizations:
  `decompose` == Algorithm 36 Decompose, `high_bits` == Algorithm 37 HighBits, `make_hint` ==
  Algorithm 39 MakeHint (all `z, r < q`), `use_hint` == Algorithm 40 UseHint. The Cryptol spec
  (`fips204_hint44.cry`) is transcribed from FIPS 204 over signed 64-bit words ,  exact integer
  semantics since every quantity in these algorithms has magnitude < 2^24, far below wrap ,  NOT from
  the implementation, so this is spec-conformance, not impl-vs-impl. **Non-vacuity checked:** four
  mutations (r0+1, r1+1, negated make_hint, use_hint+1) each fail with a counterexample.
  Trust base: the three assumed CT-layer specs (black_box, cmovnz, cmoveq) + mir-json soundness.
  NOT covered: `bit_pack`/`bit_unpack` (the literal GHSA-5x2r-hc65-25f9 site ,  the strictly-increasing
  index validation) and the polynomial/vector-level wrappers; scalar layer only.
- **RustCrypto ml-dsa scalar algebra (Power2Round / infinity norm / mod+- q): VERIFIED (2026-06-12).**
  `saw implementations/rustcrypto-ml-dsa/proof/scalar/scalar.saw` exits 0 (3 proofs), each for every
  field element (`x < q`): `power2round` == FIPS 204 Algorithm 35, `infinity_norm` == `|. mod+- q|`
  (Section 2.3 ,  this gates the security-critical z/ct0 norm checks), and `mod_plus_minus::<SpecQ>`
  == `r mod+- q` in the crate's mod-q representation. All three claims are parameter-set independent
  (q and d = 13 are fixed across ML-DSA-44/65/87). Spec `fips204_scalar44.cry`, same signed-[64]
  exact-integer transcription discipline. **Non-vacuity:** four mutations (r1+1, r0+1, norm+1,
  modpm+1) each fail with a counterexample. Trust base: the three assumed CT specs + mir-json.

## ML-KEM-512 reduce layer (go-wide slice 1, 2026-07-14)

Target: `target/pqclean-mlkem/reduce.c` (PQClean ml-kem-512/clean, same pin `202a8f9`; provenance
in `target/README.md`). Proofs: `proof/saw/mlkem_reduce.saw` via `make mlkem-reduce`, exit 0 on
2026-07-14 (SAW 1.5.1 + z3).

- **C ≡ Cryptol, `montgomery_reduce` ([32]→[16]): VERIFIED** under the documented input range
  `-q*2^15 ≤ a ≤ q*2^15 - 1` (q = 3329). Default (nsw) bitcode, so the proof also establishes no
  signed-overflow UB inside that range (outside it, `a - t*q` can overflow int32; nothing is
  claimed there). Result+1 mutant rejected with a counterexample.
- **C ≡ Cryptol, `barrett_reduce` ([16]→[16]): VERIFIED, unconditional.** The C's `t *= KYBER_Q`
  multiplies at int width (no overflow there: |v*a| < 2^30) and then narrows to `int16_t`; for
  inputs near ±2^15 that narrowing wraps. Narrowing conversion is implementation-defined, not UB
  (C17 6.3.1.3p3; clang wraps), and the model's mod-2^16 arithmetic matches it exactly. Result+1
  mutant rejected.
- **Math-level correctness, direct SMT (boundary datum):** `barrett_correct` (result ≡ a mod q,
  centered in ±(q-1)/2, all int16) Q.E.D. in ~13 s in the readable Integer form. The Montgomery
  congruence needed one restatement: the Integer form (`mont_correct`) stalls BOTH z3 and cvc5
  past 300-400 s (nonlinear Integer with mod), while the equivalent [48] bit-vector form
  (`mont_correct_bv`: nothing wraps at 48 bits, the 2^16 multiply is a shift, one signed remainder
  by the constant 3329) is Q.E.D. in ~11 s. Same integer fact, so the C functions inherit full
  Montgomery/Barrett correctness by composition with the equivalence proofs. Contrast with ML-DSA:
  the analogous 64/32-bit Montgomery statement needed Isabelle, and the Rust 2^46 Barrett needed
  bitwuzla. Goal SHAPE, not just width, decides tractability: even at 16-bit data widths the
  Integer-with-mod form is out of reach while the BV form is seconds.
- Not yet claimed for ML-KEM (reduce layer): FIPS 203 transform correctness. `fqmul` is static and
  inlined; it is covered by the forward-NTT proof below, not separately.

## ML-KEM-512 forward NTT (go-wide slice 2, 2026-07-16)

Target: `target/pqclean-mlkem/ntt.c` (same pin `202a8f9`). Model: `model/cryptol/MLKEM_NTT.cry`
(`ntt`, 7 Cooley-Tukey levels, mirrors the ML-DSA forward model at int16 widths). Proof:
`proof/saw/mlkem_ntt.saw` via `make mlkem-ntt`, exit 0 on 2026-07-16 (SAW 1.5.1). In `saw.yml`.

- **C ≡ Cryptol, `PQCLEAN_MLKEM512_CLEAN_ntt(a[256])`: VERIFIED under two's-complement wrapping.**
  Proven on the `-fwrapv` bitcode (all inputs, no bound precondition), with `montgomery_reduce`
  passed as an uninterpreted override so the 896 butterfly calls collapse to a structural array
  equality. Cross-checked before the proof by a differential test against the compiled C on two
  vectors (spread values and full int16 extremes): 256/256 identical. Non-vacuity: an inline
  result[0]+1 mutant is rejected with a counterexample (2026-08-14; previously this relied on a
  comment claiming `scripts/mutation_test.sh` coverage, which was inaccurate -- that script only
  mutates ML-DSA's montgomery_reduce and gave ML-KEM no coverage at all; fixed).
- **Solver datum (paper-relevant):** the equality discharges under SBV `unint_z3` in ~3.5 s, but the
  what4 `w4_unint_z3` backend does NOT terminate on it within 9 min (measured). This is the reverse
  of the reduce layer, where z3 discharged the equivalences and cvc5 stalled. Backend choice, not
  just width or goal size, decides tractability.
- **Overflow / no-UB setting (differs from ML-DSA).** ML-DSA's forward NTT needs a coefficient-bound
  proof because its int32 butterfly add/sub genuinely overflows for unbounded inputs. ML-KEM's
  coefficients are int16: `r[j] ± t` promotes both legs to int, the 32-bit add cannot overflow
  (|r|<2^15, |t|<q<2^12, so |r±t|<2^16), and the narrowing back to int16_t is implementation-defined
  (C17 6.3.1.3p3), not UB. So the C is UB-free with NO coefficient bound. That fact is ARGUED, not
  mechanized: on the default (nsw) bitcode SAW emits ~2700 no-signed-overflow side conditions that,
  though each individually trivial (17-bit sums, 30-bit products), do not discharge as one monolithic
  goal under either backend (both time out). We therefore use `-fwrapv` for the equivalence, as with
  ML-DSA, and record UB-freedom as an argued meta-step (narrower width removes the overflow ML-DSA
  had to bound; the nsw and `-fwrapv` bitcodes differ only in poison, absent when nothing overflows).
- **FIPS 203 forward-transform correctness: PROVEN (2026-07-23), gated in `make verify`** (see the
  next section). Still argued (shared with ML-DSA, per the no-UB note above): the nsw/`-fwrapv`
  overflow bridge to the C. The INVERSE NTT's C ≡ Cryptol leg is now also proven (see the
  2026-08-11 section below); its FIPS-203 correctness leg is not yet done.

## ML-KEM-512 forward NTT FIPS-203 residue correctness (go-wide slice 3, 2026-07-23)

Model ≡ FIPS-203, in Isabelle. Sessions `Kem_Base` (brick a) + `Kem_Work` (bricks b, c), on the AFP
`Number_Theoretic_Transform` + SAW `Cryptol` base. Proof: `make mlkem-isabelle` (also pulled by
`make verify`), 0 `sorry`/`oops`/`admit`; verified in-session 2026-07-23 (`Finished Kem_Base` +
`Finished Kem_Work`, exit 0; re-runs and fails on an injected false lemma, so the gate is not
vacuous). The no-sorry grep in verify.yml covers `spec/isabelle/kem`.

- **brick (a) `montgomery_reduce_correct_kem`** (`kem/Kyber_Mont.thy`): the lifted ML-KEM
  `montgomery_reduce` satisfies `2^16 * r ≡ a (mod 3329)` and `-q < r < q` on the input range
  `-2^15*q ≤ a < 2^15*q`. Stated over `sint_seq` (signed reading of the bits SAW checks the C
  against); full integer→word→seq chain, no admits.
- **brick (b) 7-level routing** (`kem/work/Kyber_Route.thy`): the model foldl over levels 0..6 ==
  the abstract Cooley-Tukey recurrence on the `sint_seq` coefficient view; per-level coefficient
  laws (level0..6) plus a magnitude-bound/congruence invariant compose into `ntt_recurrence`.
- **brick (c) `ntt_residue`** (`kem/work/Kyber_Residue.thy`): for `boundedK 3328 w` (reduced input,
  |coeff| ≤ q-1) and k < 256,

      sint_seq (ntt w ! k) mod 3329
        = (SUM m<128. sfk w (k mod 2 + m*2) * 17^((2*brv7 (k div 2) + 1)*m)) mod 3329

  output position k = 2i+c is the even (c=0) / odd (c=1) coefficient of the FIPS-203 degree-2 residue
  `f mod (X^2 - 17^(2*brv7(i)+1))`. `ntt` is the montgomery-domain model the SAW C ≡ Cryptol leg
  checks. This is the FIPS-203 forward NTT for Kyber's incomplete split (mod 3329, X^256+1 factors
  into 128 degree-2 terms: a 256th root of unity exists but no 512th, so unlike ML-DSA the transform
  does not split down to degree 1).
- **si16 vs sint_seq (brick a flagged it as a deferred bridge): confirmed cosmetic, not a gap.** The
  whole chain (`montgomery_reduce_correct_kem`, `butterfly_law_kem`, `ntt_residue`) is stated
  uniformly over `sint_seq`. `si16` is only an internal alternate predicate on the model of equal
  value; no correctness theorem or routing step depends on it.
- **Scope (stated plainly): forward FIPS-203 correctness only.** No ML-KEM overflow-bound theorem
  (not needed: the int16 butterfly cannot overflow int32, per the slice-2 no-UB note). The published
  claim is "the method generalizes across two NIST standards on the forward transform + reduce," not
  "complete NTT for ML-KEM." As of 2026-08-11 the inverse NTT's C ≡ Cryptol leg is proven (below);
  its FIPS-203 correctness leg is still future work, so "complete NTT for ML-KEM" is still not a
  claim this project can make.

## ML-KEM-512 inverse NTT, C ≡ Cryptol leg (go-wide slice 4, started 2026-08-11)

Target: `target/pqclean-mlkem/ntt.c`, function `PQCLEAN_MLKEM512_CLEAN_invntt`. Model:
`model/cryptol/MLKEM_NTT.cry` (`invntt`/`invnttLevel`, 7 Gentleman-Sande levels). Proof:
`proof/saw/mlkem_ntt.saw` (extended) via `make mlkem-ntt`, exit 0 on 2026-08-11 (SAW 1.5.1).

- **C ≡ Cryptol, `PQCLEAN_MLKEM512_CLEAN_invntt(a[256])`: VERIFIED under two's-complement
  wrapping.** Proven on the `-fwrapv` bitcode (all inputs, no bound precondition), with both
  `montgomery_reduce` and `barrett_reduce` passed as uninterpreted overrides. Non-vacuity checked
  inline (a result[0]+1 mutant is rejected) -- NOT by `scripts/mutation_test.sh`, which only
  mutates ML-DSA's `montgomery_reduce` and gives ML-KEM no coverage. The forward-NTT proof
  (previous entry) has since been given the same inline mutant (2026-08-14), so this is no longer
  a gap between the two.
- **Index derivation cross-checked, not just typechecked.** The closed-form zeta index
  (`zetas[top - b]`, `base = 1 << (6-ell)`, `top = 2*base-1`) was verified against a literal
  transliteration of the C's `k`-counter loop in Python (127/127 block-zeta assignments match)
  before being trusted, and the whole model was round-trip-checked in Cryptol
  (`invntt(ntt(x)) == MONT*x mod q`, `:check roundtrip`, 2000/2000) on barrett-reduced input.
- **Overflow / no-UB setting: simpler than the forward leg.** Unlike ML-DSA's inverse (unreduced
  low leg, doubles per level, needed an 8-level Isabelle induction to bound), this C re-reduces the
  low leg through `barrett_reduce` every level, so there is no per-level magnitude growth to
  compose. Expected to argue the same way the forward leg does (int16 legs cannot overflow int32),
  not yet done.
- **`barrett_reduce_correct_kem` PROVEN (2026-08-11)** (`kem/Kyber_Barrett.thy`, in the `Kem_Base`
  session, no sorry/oops): for every int16 input (no precondition, unconditional like the SAW
  proof), the lifted ML-KEM `barrett_reduce` returns the centered representative mod q:
  `(r - a) mod 3329 = 0` and `-1664 <= r <= 1664`. Structurally different from montgomery's bridge
  (this is a round-to-nearest Barrett reduction, not the conditional-subtract Barrett already
  proven for RustCrypto's wider domain in `spec/isabelle/tier2/barrett/` -- that lemma is not
  reused). The bound itself (`barrett_r_bound_kem`) is checked by `eval` enumerating the full
  65536-value int16 domain rather than an algebraic interval derivation, since the domain is small
  enough for that to be cheap and more robust than hand bounds. Non-vacuity checked by hand: a
  deliberately wrong bound (1663 instead of 1664) was confirmed to make the build FAIL before
  reverting. Needed because invntt's low leg re-reduces through `barrett_reduce` every level.
- **Not yet claimed:** FIPS-203 inverse-transform correctness in Isabelle (the CRT-recombination
  mirror of brick (c) `ntt_residue`, via a Gentleman-Sande mirror of `Kyber_Route.thy`) -- this is
  the bulk of the remaining work, comparable in scope to bricks (b)+(c) of the forward leg (which
  took roughly a week of iterative proof engineering, 2026-07-18 to 2026-07-23); the overflow/no-UB
  argument stated explicitly for the inverse; gating in `make verify` / `mlkem-isabelle` (currently
  only the forward leg is Isabelle-gated).

## Tool/version pins
Pinned and installed by `scripts/setup.sh` into `.tools/` (gitignored). Platform of record:
**macOS 26.3.1, Apple Silicon (arm64)**, set up 2026-06-01.

- SAW: **v1.5.1** (2026-05-22), asset `saw-1.5.1-macos-15-ARM64-with-solvers.tar.gz`.
- Cryptol: **3.5.0** (git 6173b60), bundled inside the SAW 1.5.1 tarball (used in-place to avoid skew).
- cryptol-to-isabelle: bundled standalone in the SAW 1.5.1 tarball (first release to ship it).
- Isabelle: **Isabelle2025-2** (Jan 2026), asset `Isabelle2025-2_macos.tar.gz` (universal bundle,
  upstream lists macOS 26 / Apple Silicon support).
- clang: **Apple clang 17.0.0 (clang-1700.0.13.5)**, system `/usr/bin/clang` (NOT vendored ,  see below).
  **Delta, 2026-08-22:** the Q-SEAL proofs were re-run on a second machine (Apple M2 Max, macOS 13.6)
  whose system compiler is Apple clang 14.0.3 (clang-1403.0.22.14.1). Every obligation discharges under
  both, which is mild evidence the results are not artefacts of one compiler's bitcode, but the pinned
  version is the 17.0.0 one and a timing or bitcode comparison across the two is not meaningful.
  `scripts/setup.sh` warns on the mismatch rather than failing.
- ProVerif: **2.05**, tarball pinned by sha256 `4871f53c32ab...ceabc4`, built from source (CLI only) by
  `scripts/setup.sh` when an OCaml toolchain is
  present; used solely for the Q-SEAL reachability property (section 16 property 5). Optional leg
  (`SKIP_PROVERIF=1`), not in the per-push SAW CI. Needs opam + OCaml 4.14.1 (see
  `qseal/proof/proverif/README.md`); the opam package's GTK2 GUI dependency is skipped by building the
  CLI directly.
- z3: 4.15.4 present on system, but the SAW "with-solvers" bundle ships its own solver set; the
  pipeline prefers the bundled solvers for reproducibility.

### Platform / toolchain caveats (introduced 2026-06-01)
- **SAW binary built for macOS 15, run on macOS 26.** No arm64 macOS-26-specific SAW build exists
  upstream; the macOS-15 arm64 build is what we run. Flagged here for honesty; gated on `saw --version`
  actually running before we depend on it.
- **Apple Silicon Gatekeeper.** On macOS arm64 a downloaded binary that is only ad-hoc signed and
  still carries the `com.apple.quarantine` xattr is SIGKILLed on exec ("Killed: 9"). `setup.sh`
  strips quarantine (`xattr -dr com.apple.quarantine`) and ad-hoc re-signs the Mach-O binaries
  (`codesign --force --sign -`). Neither alters behavior; they only satisfy the loader. Verified:
  `saw --version` → `1.5.1`, `cryptol --version` → `3.5.0` after this step.
- **Apple clang, not mainline LLVM/clang.** We emit LLVM bitcode for SAW with the system Apple clang
  (17.0.0). Apple's clang can emit a bitcode/IR version that differs from mainline; if SAW's LLVM
  parser rejects it, the documented fallback is a pinned mainline `clang`. Part of the trust base
  (see "Compiler correctness").

## Q-SEAL assumed specifications (`llvm_unsafe_assume_spec`)

The Q-SEAL proofs assume exactly two function specifications. Both are in
`qseal/proof/hybrid.saw` and both are deliberate, not workarounds for something that would not verify.

- **`qseal_verify_ecdsa`** (hybrid.saw:28) and **`qseal_verify_mldsa`** (hybrid.saw:37) are assumed to
  return 1 exactly when the abstract Cryptol predicates `vE pk tbs sig` / `vM pk tbs sig` hold. The C
  bodies in `qseal/ref/hybrid.c` are placeholders returning 0; a deployment links real ECDSA P-256 and
  ML-DSA-44 verifiers there. Assuming them is the point of property 3: the result is about the shape of
  the acceptance decision (both signatures required, over the same transcript bytes) and holds for
  whatever the real verifiers compute. Nothing about ECDSA or ML-DSA correctness is claimed, and the
  1312-byte and 2420-byte key and signature sizes are carried as array lengths only.
- **The tactic is load-bearing and is part of this assumption.** `vE` and `vM` have placeholder Cryptol
  bodies (`QSEAL_Verify.cry:20,23`) that are constantly `False`. Under plain `z3` those unfold, every
  acceptance term collapses to `False`, and the obligation holds for any implementation including the
  accept-on-either downgrade. Only `w4_unint_z3 ["vE","vM"]` keeps them uninterpreted and makes the
  result structural. Any future obligation in that file must use the same tactic.

## Q-SEAL property 5 (ProVerif) modeling assumptions

Rebuilt 2026-08-22 after OF-3. The model (`qseal/proof/proverif/property5.pv`) carries a signing key,
two transcript shapes so the assertion type is inside the signed bytes, a host command handler, a
profile-event source and a separate assertion builder behind a private channel. Four queries hold: the
event correspondence, the same statement over signatures the attacker can hold, that the attacker cannot
obtain an assertion over content it chose, and secrecy of the signing key. Assumptions and non-results,
all load-bearing:

- **No C == model link.** Property 5 is symbolic only. The guard it needs (the host path refuses type
  `0x04`) is separately enforced in the verified C by `qseal_validate_request`; nothing formally ties
  the two together.
- **Injectivity is not proved.** With the two events in separate processes ProVerif's abstraction lets
  one private-channel message be consumed more than once, so replaying one internal transition into
  several assertions is not excluded. The pre-OF-3 model did prove the injective form, but only because
  both events were emitted by one process, which was an artefact of the modelling rather than a fact
  about the design.
- **The transcript is ONE constructor, and that choice is load-bearing.** `property5.pv` builds every
  signed object with `tbs(type, ...)`, mirroring `QSEAL_TBS.cry` where `assertion_type` is one field of
  a single record. An earlier version used two disjoint constructors with the type absent from the
  observed one; the host path then could not build the term the queries range over no matter what it
  did, so the queries held with the spec 8.4 guard deleted. `verify_reachability.sh` now runs a
  generated guard-ablation variant that must report queries 2 and 3 false, so that class of error fails
  the gate. Found in review, not by the gate.
- **The witness and ablation variants are GENERATED from the model** by
  `qseal/proof/proverif/gen_variants.py` at verify time. They used to be checked-in copies, and a copy
  certifies the copy: deleting the honest emitter from the model alone left the witness still reporting
  the event reachable, with the gate green. That is OF-3 with one file of separation.
- **The fourth query was added 2026-08-22 after review.** The first rebuild of this model read the
  attested subject, digest and policy from the host channel, so the handset could obtain a signed
  observed-action assertion carrying content of its own choosing while the first two queries still
  reported true. `property5_mutant_hostdata.pv` preserves that version as a regression witness. The
  shipped model generates those fields inside the event source instead.
- **That a profile operation really occurred is still assumed.** The attested fields now come from the
  card rather than the handset, but nothing ties them to a state change; the host names a profile and
  the card attests fresh values.
- **No mutable profile state.** A variant holding the current profile state in a private channel and
  read-modify-writing it under replication did not terminate (ProVerif still generating rules after 10
  minutes on an M-series laptop). The shipped model uses a fresh event id per transition, so "a real
  state transition occurred" is assumed, not checked.
- **Abstract signing.** `sign` is a free constructor: no ML-DSA or ECDSA semantics, no verification
  rule, and the attacker's inability to forge is by construction, not by reduction.
- **No APDU layer.** Fragmentation, chaining and the applet's command dispatch beyond the assertion type
  are not modelled.

## Q-SEAL property 4 (single-use store) scope, restated 2026-08-22

Two versions are now verified. `qseal/ref/nonce.c` is the v0.1 append-only store: safe, fail-closed,
and wedged permanently once a host submits CAP distinct validated requests, since the key is
host-supplied. `qseal/ref/nonce_exp.c` adds expiry eviction, which is the retention mechanism the spec
names in section 10, and its theorem is windowed: a request cannot be replayed while the transcript it
came from is still valid. Availability returns once the recorded requests expire
(`expiry_restores_room`). Both are proved equal to their models by SAW.

What neither version establishes, stated plainly because the proofs are easy to over-read:

- **Nonce freshness is not established.** Nothing in either model ties the request's nonce to a
  challenge a verifier actually issued. The store answers "have I consumed this key before", not "did I
  issue this nonce". If that burden sits with the verifier's own challenge state, it sits outside every
  property verified here.
- **Persistence across a power cycle is assumed away.** Both stores are in RAM. The host is untrusted
  and the card is in the adversary's hands, so a power cycle is an adversary-triggerable event, not an
  unmodelled convenience: after one, a request consumed before the cycle is accepted again even inside
  its validity window. The expiring store does not fix this; only persistent storage or a monotonic
  counter would, and neither is modelled.
- **Sequential and atomic only.** Check-then-consume is one step in both models. The TOCTOU window
  between verifying and consuming under concurrency is not expressible, so two simultaneous submissions
  of the same key both seeing "fresh" is out of scope.

## Reproduction envelope: -O0 only

The proofs are run against bitcode built at `-O0`, which is what every runner script does and what the
figures come from. At `-O2` two of them do not reproduce, and both reasons are worth knowing:

- `hybrid.saw` fails, because clang inlines the placeholder verifier bodies in `qseal/ref/hybrid.c` and
  the `llvm_unsafe_assume_spec` overrides no longer have a call to attach to. This is an artefact of the
  placeholders, not of the property; a deployment links real verifiers and the overrides would apply.
  The cause is interprocedural constant propagation, and it is worse than an override problem.
  `clang -S -emit-llvm -O2` on `qseal/ref/hybrid.c` emits `ret i32 0` for `qseal_hybrid_accept`, for the
  downgrade mutant and for the split-transcript mutant alike: the placeholder verifiers are `readnone`
  and return a constant, so at `-O2` all three are the same constant function. `noinline` blocks
  inlining but not return-value propagation, so it does not help. **This is a scope limit on property 3,
  not a build quirk:** the property holds of the C as written, and the C as written is a constant
  function once the optimiser can see the placeholders. A deployment linking real verifiers would not
  collapse this way, and that deployment is not what was verified. `-O0` is the supported configuration and the only one the figures come from.
- `evidence.saw` crashes the symbolic simulator: "You have encountered a bug in Crucible's
  implementation ... Attempting to evaluate poison value". That is an upstream defect worth reporting to
  Galois. It has NOT been filed; disclosure goes through the human per CONTRIBUTING.md.

## Gating of the measured figures

- `make qseal-mutants` gates against a baseline recorded in `qseal/mutation/mutate.py` (58 mutants, 55
  killed, 3 survivors, measured 2026-08-22 on an Apple M2 Max with the bundled z3). It used to return 0
  unconditionally, so a run that killed nothing looked like a run that killed everything. Classifying a
  survivor is still a human job; the counts are not.
- `make eid-spec-mutation` reports which checks see a paired specification-and-code mutation. Its
  verdict now comes from `saw`'s exit code and its own obligation line rather than from a print
  statement, after a review found it reporting "PASSES" for a run where `saw` had exited non-zero.

## CVE anchor fidelity (cve-anchor/fidelity/)

- The comparison against the shipped decoder is a **test, not a proof**: 7840 boundary-heavy vectors out
  of an 84-byte space. Zero mismatches on those vectors is evidence about the transcription, not a
  theorem about it.
- The oracle builds a real ML-DSA-44 signature and replaces its 84-byte hint region, so a rejection is
  attributed to the hint bytes. Everything outside that region is a genuine signature from the crate.
- Vector generation is seeded (`random.Random(20260822)`), so the figures are reproducible; a different
  seed gives different counts.
- It needs `cargo` and pulls ml-dsa 0.1.1 from crates.io, so it is not part of the SAW push check; it
  runs in the Rust workflow.

## GSMA SGP.29 EID anchor (esim-eid/) assumptions

- **The spec-mutation experiment covers three clauses, not the standard.** `make eid-spec-mutation`
  measures three paired mutations. It says nothing about clauses nobody thought to mutate, and the
  mutation list is hand-written, so it inherits the same authorship problem it is designed to expose,
  one level up.

- **The SAW obligation targets the fold, not the standard's wording.** `eid.saw` proves
  `gsma_eid_valid == eidValid`, and `eidValid` uses `checkDigitsValidFold`. `checkDigitsValid`, the
  128-bit transcription of "the 32 digits as a decimal integer", is connected to it only by the bridge
  lemma plus the induction below. No machine step connects the C to the clause GSMA wrote.
- **The composition is argued, not mechanized.** The one-digit bridge lemma (reducing early equals
  reducing at the end when the accumulator is below 97) is proved, and the accumulator invariant is
  proved, but the step from those to "the 32-digit fold equals the standard's single remainder over the
  whole value" is an ordinary induction done on paper. The direct SMT obligation does not discharge:
  no result within 10 minutes as a 128-bit bitvector goal, and none over Cryptol `Integer` either.
  Mechanizing it would mean Isabelle, as with the ML-DSA NTT bound.
- **Digits, not characters.** The model and the C work on one digit per byte with value 0..9. Decoding
  ASCII or BCD into that form is out of scope, so a real deployment carries a decoding step this
  verification says nothing about.
- **EID.R01 is discharged by the type**, not by a check: the model works on a 32-element array, so a
  wrongly sized input cannot be expressed rather than being rejected. A deployment reading an EID off a
  wire must enforce the length itself.
- **Only three clauses are mechanized.** SGP.29 also governs assignment, ERHI structure and eligibility
  criteria; none of that is a property of a single identifier and none is modelled here.

## Q-SEAL: layers the results rest on and do not cover

The scope section of the write-up names these as out of scope. They were not written down here, which
meant the document that is supposed to hold every assumption was missing the ones the results lean on
hardest. Each is a real gap, not a formality.

- **Credential binding.** Nothing verified here ties `ak_id`, or the TBS-V2 `pair_commitment`, to a
  certificate chain or to an attestation key a verifier trusts. Both are opaque bytes in the transcript.
  A verifier that accepts a well-formed transcript without checking whose key signed it gets no help
  from any property in this repository.
- **Suite negotiation and downgrade at the protocol level.** Property 3 shows the acceptance decision is
  a conjunction over one transcript. It says nothing about how a verifier and an applet agree on HYB-1
  in the first place, so a downgrade achieved during negotiation is out of scope even though the
  in-transcript downgrade is covered.
- **Outer-envelope encoding, including low-S malleability.** The transcript is fixed-offset and
  injective. The ECDSA signature carried beside it is not covered at all: a non-canonical `S` value is a
  malleability the transcript's injectivity does not touch.
- **The ML-DSA context string.** The V2 revision assigns one. No property constrains it, and the FIPS
  204 context mechanism is not modelled.
- **Hash collision resistance.** The `pair_commitment` argument assumes SHA-256 is collision resistant.
  That is an assumption, not a result, and the format-level proof would hold for a broken hash.
- **APDU and TLV decoding.** Wire decoding, chaining and fragmentation of commands are out of scope; the
  evidence property covers reassembly of already-decoded fragments only.

## Open findings (handle per CONTRIBUTING.md → Responsible disclosure)
- **OF-5 (2026-10-24, found by SAW while verifying the HQC v5.0.0 AVX2 multiplier): `toom_3_mult`
  in `src/x86_64/common/hqc-1/gf2x.c` and `hqc-3/gf2x.c` reads one 64-bit word past the end of its
  static arrays `W0` and `W2`.** The interpolation step `W2 = (W2 + W0)/x` loads 256 bits from a
  one-word offset, so its last iteration reads word `8 * T_TM3R_3W_256` of arrays that have
  `8 * T_TM3R_3W_256` words. The word read lands in a lane the code zeroes before use; the SAW proof
  (A-HQC item 12, with one vector of slack on the two arrays and symbolic contents in it) shows the
  result does not depend on it. It is undefined behaviour in a `-O3 -flto` build and a sanitizer
  with global redzones would flag it. hqc-5's `toom_3_mult` sizes its arrays with `+ 2` and its proof
  runs without slack. Fix: one more vector in the two declarations, or stop the loop one vector early.
  - Reported by email to the HQC team on 2026-10-24; acknowledged on 2026-10-25. The team confirmed
    that the two loads in the last iteration read one 64-bit word beyond `W0` and `W2`, that the
    result does not depend on the value under our stated assumptions, and that the access is still
    invalid; their fix is one more element in each of the two static arrays (zero-initialized, being
    static). Not a security issue as far as we can tell: the word read is whatever the linker placed
    after the array in the object's static data, and it does not reach the output.
  - AddressSanitizer does not catch it as written: `_mm256_lddqu_si256` lowers to the
    `llvm.x86.avx.ldu.dq.256` intrinsic, which ASan does not instrument. The upstream hqc-1 AVX2
    KAT test built with `-O2 -fsanitize=address` for x86-64 and run under Rosetta on macOS 15 gives
    0 reports and matching answers (2026-10-24); with `_mm256_loadu_si256` substituted for `lddqu`
    in `gf2x.c`, ASan reports a 32-byte global-buffer-overflow in the first key generation.
- **OF-3 (2026-08-22, found in an audit of the submitted artifact): the Q-SEAL property-5 ProVerif
  result was vacuous.** In `qseal/proof/proverif/property5.pv` the channel `internalCb` is declared private and
  no process ever performs `out(internalCb, ...)`. `internalObserved` is the only process that emits
  `SignedObserved`, it is guarded on an input from that channel, so it never runs, the antecedent of the
  injective correspondence is unreachable, and ProVerif reports the query true regardless of the rest of
  the model. The mutant file was falsified only because it adds a *reachable* emitter in `hostCreate`,
  so the mutation check never tested the honest model.
  - Scope of the damage: property 5 only. The six SAW properties are unaffected; the whole artifact was
    rebuilt from scratch, including the mutation pass, and they reproduce. (That pass is now 58
    mutants, 55 killed, 3 survivors, re-measured 2026-08-22; the 41/39/2 figure was the July run.)
  - Lesson, now enforced: **a falsified mutant does not establish that the honest model is
    non-vacuous.** Every ProVerif query in this repo must be paired with a reachability witness showing
    the events in its antecedent can actually occur. `qseal/verify_reachability.sh` gates on this.
  - Also found in the same audit and fixed 2026-08-22: the claim "each proof carries an injected
    mutant it rejects" was false for properties 1 and 2 (`tbs_v1.saw` and `assertion.saw` had no `fails`
    guard). Mutants added and verified: aliased serializer, off-by-one parser, unbound-nonce builder,
    plus a no-commitment serializer for TBS-V2.
  - **Fixed and verified 2026-08-22.** `property5.pv` and `property5_mutant.pv` gained a
    `profileTransition` process that writes to the callback channel, `property5_reachable.pv` is a new
    reachability witness, and `qseal/verify_reachability.sh` exits 0 on all three runs with ProVerif
    2.05: the correspondence is true, `not event(SignedObserved(...))` is **false** (so the event is
    reachable and the positive result is not vacuous), and the mutant is refuted. The gate was itself
    checked against the pre-fix model, which reports the event unreachable and trips `FAIL (VACUITY)`.
  - Superseded 2026-08-22: the model was rebuilt again so the two events are emitted by different
    processes, and a fourth query was added after review found that the rebuilt model still let the
    handset choose the attested content (see the property-5 section below). The adjacency objection no
    longer applies; the remaining limits are listed there.
- **DISCLOSED 2026-06-09:** OF-1 and OF-2 were filed together (deliberate, human-routed) as a single
  upstream issue: **pq-crystals/dilithium#114** ("ref/reduce.c: doc-comment output bounds for
  montgomery_reduce and reduce32 are off by one at endpoints"). Both are documentation/contract fixes,
  not security or functional bugs; PQClean (re-namespaced copy, archiving) and mldsa-native/liboqs are
  downstream of this origin. Awaiting maintainer response on preferred phrasing before any PR.
- **OF-1 (2026-06-07): PQClean `montgomery_reduce` doc-comment postcondition is off by one at the
  upper input endpoint.** The comment in `target/pqclean/reduce.c` states, for input domain
  `-2^31*Q <= a <= Q*2^31` (inclusive), that it returns `r` with **`-Q < r < Q`** (strict). But at
  `a = 2^31*Q` the function returns `r = Q` (= 8380417), which violates the strict upper bound.
  Verified directly against the vendored C: `montgomery_reduce(17996808470921216) = 8380417`; the
  lower endpoint `a = -2^31*Q` returns `0` (fine). The congruence `2^32*r ≡ a (mod Q)` still holds.
  - Severity: **documentation/contract only, not a security or functional bug.** Real callers (NTT
    butterflies) feed products bounded well below `2^31*Q`, so the endpoint is not exercised in
    practice. The reference is mathematically correct; only the stated strict bound at the inclusive
    endpoint is wrong (the true guarantee over the inclusive domain is `-Q <= r <= Q`).
  - Origin & disclosure routing: the identical `montgomery_reduce` comment is in
    **`pq-crystals/dilithium/ref/reduce.c`** (verified 2026-06-07) ,  PQClean only re-namespaces it.
    So the finding originates upstream and also affects PQ Code Package `mldsa-native` and liboqs.
    PQClean is being archived (July 2026), so the right disclosure home is **pq-crystals/dilithium**,
    not PQClean. **Do NOT auto-file upstream** (CLAUDE.md); surfaced to the maintainer (human) on
    2026-06-07 to decide deliberately.
  - Impact on Assay: the SAW leg (C ≡ Cryptol model) is unaffected ,  it asserts no bound. The
    Isabelle correctness spec is stated over the **half-open** domain `-2^31*Q <= a < 2^31*Q`, where
    the strict `-Q < r < Q` is actually true; see `spec/isabelle/MLDSA_NTT_Spec.thy` (`mont_input_ok`).
  - Same issue in the standard (noted 2026-10-09): NIST's FIPS 204 potential-updates list
    (`fips-204-potential-updates.xlsx`, last updated 2026-07-31) says Appendix A's Montgomery
    reduction "incorrectly gives the upper bound of the input range as inclusive when it should be
    exclusive", and that Appendix A will be rewritten to match the reference implementation. The
    list credits no reporter, and we did not report this to NIST; it is an independent statement of
    the same endpoint issue. The same list's NTT entry (Sec. 2.5/7.5: `zeta_j` is
    `zeta^(2 BitRev8(j) + 1)`, not `w` evaluated there) matches the convention our theorems state.
    No other entry touches the NTT or multiplication.
- **OF-2 (2026-06-08): PQClean `reduce32` doc-comment output bound is off by one on the low end
  under its own (one-sided) precondition.** The comment in `target/pqclean/reduce.c` states, for
  `a <= 2^31 - 2^22 - 1`, that it returns `r` with **`-6283008 <= r <= 6283008`**. But the stated
  precondition is one-sided (no lower bound), so `a = -2143289344` is admissible (it is a valid
  `int32`, `>= -2^31`, and satisfies `a <= 2^31-2^22-1`), and there `reduce32(a) = -6283009`,
  which violates the stated lower bound by one. Verified by direct computation against the formula
  (`scripts`-level check, 2026-06-08): min over `a in [-2^31, 2^31-2^22-1]` is `-6283009` at
  `a=-2143289344`; max is `6283008` at `a=2143289343`. The congruence `r ≡ a (mod Q)` still holds.
  - Root cause: the documented bound `[-6283008, 6283008]` is correct only under the **symmetric**
    precondition `|a| <= 2^31-2^22-1` (which excludes `a=-2143289344`, since
    `2143289344 > 2143289343`). The doc's one-sided precondition is too weak for its postcondition , 
    either the precondition should be symmetric or the postcondition low end should be `-6283009`.
  - Severity: **documentation/contract only, not a security or functional bug** (same class as OF-1).
    The reduced value is always a correct residue; only the stated tightness is off, and ML-DSA call
    sites feed `reduce32` magnitudes far below this endpoint.
  - Origin & disclosure routing: same as OF-1 ,  identical comment in `pq-crystals/dilithium/ref`;
    route to **pq-crystals/dilithium**, not PQClean (archiving). **Do NOT auto-file** (CLAUDE.md);
    surfaced to the human 2026-06-08.
  - Impact on Assay: the SAW leg asserts no output bound, so it is unaffected. The Isabelle
    `is_reduce32` spec uses the **true reachable** window `-6283009 <= r <= 6283008` (not the doc's
    `-6283008`), proven over the SAW domain `a <= 2^31-2^22-1`; see `spec/isabelle/MLDSA_NTT_Spec.thy`.

## OF-4: the `by eval` oracle surface (recorded 2026-09-24)

`by eval` discharges a goal by running code the code generator emits, and trusts that code rather
than replaying the inference through the kernel. It is a standard Isabelle method and it is an
oracle. This development uses it **88 times**, **85 of them in sessions `make verify` builds**:

| file | uses |
|---|---|
| `spec/isabelle/tier2/invwork/Inv_Mont_Bridge.thy` | 34 |
| `spec/isabelle/kem/work/Kyber_Route.thy` | 25 |
| `spec/isabelle/tier2/work/Mont_Bridge.thy` | 18 |
| `spec/isabelle/kem/work/Kyber_Residue.thy` | 3 |
| `spec/isabelle/tier2/work/Negacyclic_Bridge.thy` | 3 |
| `spec/isabelle/kem/Kyber_Barrett.thy` | 2 |
| `spec/isabelle/Assay_Equivalence.thy`, `spec/isabelle/kem/Kyber_NTT_Route.thy`, `spec/isabelle/tier2/Bridge_Word.thy` | 1 each |

`Mont_Bridge.thy` and `Inv_Mont_Bridge.thy` hold `ntt_bridge` and `invntt_bridge`, so the two
headline transform theorems rest on the oracle 52 times between them. What the uses do is evaluate
the two concrete 256-entry zeta tables and a few gcd facts, which is a low-risk use, but it is still
outside the kernel and it was not disclosed anywhere before this entry.

Why this is recorded as a finding rather than a footnote: the project advertises
`Thm_Deps.all_oracles` freedom for `barrettBV_bridge_holds` and says "no `sorry`, `oops`, `smt`"
about the chain. Both statements are true. Together they invite a reader to conclude the chain is
kernel-checked, which it is not. The CI gate greps `sorry|oops|admit` only and is blind to this.

Declared count, gated by `scripts/claim-lint.sh` so it cannot grow silently:
<!-- EVAL-ORACLE-COUNT: 88 -->

Measured 2026-10-04 with `Thm_Deps.all_oracles`: `ntt_signed_correct`, `invntt_signed_correct` and
every v4 theorem built on them (`ntt_mult_correct`, `ntt_mult_ring`, `acc_mult_fips`,
`acc_mult_ring`) depend on exactly `Code_Generator.holds_by_evaluation`. A build-time gate in
`spec/isabelle/tier2/accwork/Acc_Bridge.thy` now asserts that set, and asserts that the ring-side
lemmas (`negconv_is_mult`, `conv_int`, `ntt_int_surj`, `negconv_sum_ring`) have no oracle. Still not
measured: `ntt_bridge`, `invntt_bridge` and the ML-KEM `ntt_residue`.

## A-ROW: the polynomial products, what they rest on beyond the proofs

`ntt_mult_ring`, `acc_mult_ring` and `ver_row_ring` (`spec/isabelle/tier2/`), with the SAW proofs of
the per-polynomial functions and the loops in `polyvec.c`, cover the multiplications in keygen,
signing and verification. Things they do not prove (`docs/COMPOSITION.md` lists every
hypothesis of the three theorems with the proof or `sign.c` line that discharges it):

1. The order in which `sign.c` calls them (ntt, then the pointwise or matrix loop, then reduce, then
   the inverse) is read from `sign.c` at the pin, which is not vendored. The loops themselves and
   the `poly_ntt` / `poly_invntt_tomont` wrappers are verified.
2. The theorem needs `|A coeff| <= 9q`. That holds because `rej_uniform` in `poly.c` masks each
   candidate to 23 bits (`t &= 0x7FFFFF`), so any stored value is below 2^23 < 9q, whether or not the
   `t < Q` test is right. This is read from the source; `poly_uniform` is not verified.
3. `poly_add`, `poly_sub`, the accumulator and the loops are proven equal to their models on the
   `-fwrapv` bitcode. Since 2026-10-11 the absence of signed-overflow UB on a normal build is
   mechanized for them too: `proof/saw/poly_nsw.saw` (`make poly-nsw`; z3; 1889 s, exit 0, on an
   Apple M2 Max, macOS 13.7, Apple clang 14.0.3; and exit 0 in about 48 min on the pinned Apple
   clang 17.0.0 in CI verify run 38100891287 on e264684, 2026-10-11) runs
   `montgomery_reduce`, `reduce32`, `poly_pointwise_montgomery` (both call forms), `poly_add`,
   `poly_sub`, `poly_reduce`, the accumulator, the matrix loop, the `pointwise_poly` loops (both
   forms), `polyveck_sub` and `polyveck_reduce` on the DEFAULT bitcode, where every signed add, sub
   and mul carries `nsw`. SAW shows none overflows and every callee precondition holds, given
   pointwise operands within 9q; the bounds after that (pointwise below q, sum below 4q, difference
   below 5q, reduced output below q) are carried from call to call inside the script.

   Each spec has a mutant that widens or drops one input bound and is rejected, and one more checks
   the chain: the accumulator against a `poly_add` that needs `|a| < 2q` fails at the third add.
   The specs state bounds, not functional results. `scripts/check_wrapv_diff.sh` checks that the
   default and `-fwrapv` IR are identical once `nsw` and `inbounds` flags are stripped, so with no
   flagged operation overflowing the default build computes what the `-fwrapv` proofs describe.
   Stripping `inbounds` is safe because crucible-llvm rejects a pointer offset that leaves its
   allocation on either build (checked with a probe in review). The script compiles fresh IR with
   the same flags as `build_bitcode.sh` rather than disassembling `build/*.bc` (no `llvm-dis` in the
   toolchain), so it relies on clang being deterministic.

   Still not mechanized on this route:
   `invntt_tomont` (argued, see the inverse NTT entry), the `ntt` / `invntt` wrappers and loops on
   the default bitcode (`ntt` itself is `ntt_nsw.saw`, out of band), and the 9q operand bound,
   which comes from `ntt_out_bounded` for transform outputs and from item 2 for A.
4. ML-DSA-44 only: L = K = 4 are fixed in the models and the theorems.
5. Input ranges. Since 2026-10-12 the unpack functions' output ranges are proved, for every input
   byte string, on the default bitcode (`proof/saw/poly_ranges.saw`, in `make saw`, about 7 s,
   z3, exit 0): `polyt1_unpack` gives [0, 1023], `polyt0_unpack` [-4095, 4096], `polyeta_unpack`
   [-5, 2] and `polyz_unpack` [-(2^17 - 1), 2^17]. Each spec has two mutants, one tighter at each
   end, that SAW rejects. That `packing.c` and `poly_uniform_gamma1` call these functions to produce
   `t1`, `t0`, `s1`, `s2`, `z` and `y` is read from the source. Still read from the source
   entirely: `c` has coefficients in {-1, 0, 1} from `poly_challenge` (via an
   implementation-defined `uint64` to `int32` conversion; its rejection loop has no fixed bound),
   keygen's `s1`, `s2` come from `rej_eta`, and A from `rej_uniform` (item 2). A one-call spec for
   the two rejection samplers was attempted and did not finish in z3 or yices; the measurements are
   in the `poly_ranges.saw` header. The theorems need only `|z|, |c|, |y|, |s1|, |s2|, |t0| < q`,
   `|A| < 9q` and `t1` in [0, 1023]; `chknorm` also rejects `|z| >= gamma1 - beta` before
   verification's product.
   `poly_shiftl` shifts a signed int, which C defines only for non-negative values whose result
   fits. SAW does not see that undefined behaviour on either bitcode: clang emits a plain `shl`, and
   a review probe showed `poly_shiftl` verifies with no precondition on the default module too.
   `poly_nsw.saw` checks the C11 6.5.7p4 condition as arithmetic instead (for `0 <= x <= 1023`,
   `x * 2^13` is in `[0, 2^31)` and equals the 32-bit `x << 13`; at `2^18` it fails). That is a
   fact about the range, not about the C: definedness still rests on the `t1` range, which is
   proved for `polyt1_unpack`'s output and read from the source for the call in `unpack_pk`.

## A-POINTWISE: `poly_pointwise_montgomery` is verified for the two forms the reference uses

`proof/saw/mldsa_ntt.saw` proves it with `c`, `a` and `b` disjoint (the signing and keygen calls)
and, since 2026-10-09, with `c` aliasing `b` (verification's
`polyveck_pointwise_poly_montgomery(&t1, &cp, &t1)`, `sign.c` at the pin). The form with `c` aliasing
`a` is not proven; the reference does not call it that way at the pin. (Before 2026-10-09 this entry
said the aliasing case was not covered; earlier still it named the wrong argument, `a`.)

The unproven `c == a` form is a narrower claim than the function's contract, not a gap in any call
the reference makes. The loop reads and writes the same index, so that aliasing is harmless by
inspection, but this project does not count harmless-by-inspection as proven.

The rest of `poly.c` is compiled into the same translation unit. Verified from it:
`poly_pointwise_montgomery` (the two forms above), `poly_add` (`c == a`), `poly_sub` (`c == a`),
`poly_reduce`, `poly_shiftl`, `poly_ntt` and `poly_invntt_tomont`. Everything else in `poly.c`
(sampling, packing, rounding, hints, `chknorm`) is not.

## A-AC2: second C semantics, AutoCorres2 on the vendored `reduce.c` (recorded 2026-10-19)

`proof/autocorres2/` (`make ac2`, after `scripts/setup_autocorres2.sh`) runs AutoCorres2 from the
pinned AFP on `target/pqclean/reduce.c` and proves in Isabelle that each abstraction takes no
undefined-behaviour guard and returns the value of the lifted Cryptol model SAW checks the bitcode
against: `montgomery_reduce_ac2_model` (under `mont_input_ok`), `caddq_ac2_model` (all int32),
`reduce32_ac2_model` and `freeze_ac2_model` (under `reduce32_input_ok`). What this rests on:

1. AutoCorres2 and its C-parser, as a second, independent reading of the C source (SAW reads the
   `-O0` bitcode). AutoCorres2's generated `ac_corres` theorems connect each abstraction to the
   C-parser's Simpl semantics; the C-parser's own semantics is trusted.
2. Preprocessing: `proof/autocorres2/gen.sh` runs `clang -E -P` over the unchanged vendored file
   with a typedef-only `<stdint.h>`/`<stddef.h>` shim. AutoCorres2's own `cpp -CC` step keeps the
   `//` comment inside `params.h`'s `QINV` macro and the parse then fails. The preprocessor is
   trusted to do macro expansion only.
3. The AFP copy used is the pinned AutoCorres2 with one change, the default `clang_path`
   (record layouts), so a clang >= 15 can be used; the setup script prints the diff. It runs from
   its own Isabelle user home, `.tools/isa-ac2-home`.
4. `declare [[arithmetic_right_shift]]`: right shift of a negative `int32_t` is
   implementation-defined in C; this takes clang's arithmetic shift, as SAW's bitcode does.
5. `no_signed_word_abs` for `montgomery_reduce`: AutoCorres2's default signed word abstraction
   turns `(int32_t)((uint64_t)a * QINV)` into a guarded signed multiply that fails for almost every
   input, though C has no undefined behaviour there. Without that abstraction the remaining guards
   are exactly C's int64 overflow conditions. This is a precision limit of the tool's default, and
   is conservative (it reports UB that is not there, not the reverse).

Checked: `make ac2` exit 0; `Thm_Deps.all_oracles` is empty for the four theorems; a deliberately
false lemma fails; a mutant C (`caddq` adding q + 1) makes `caddq_ac2_model` fail at the
negative-input case. Scope: `reduce.c` only. `ntt.c`, `poly.c`, `polyvec.c` and `sign.c` are not
yet covered, and the theorems are about function values, not the composition in `sign.c`.

## A-SIGN: `sign.c` key generation and verification composition (recorded 2026-10-21)

`proof/saw/sign_compose.saw` (in `make saw`) proves that `crypto_sign_verify` returns
`MLDSA_Sign::verify` and that `crypto_sign_keypair` writes `MLDSA_Sign::keypair rb`. It rests on
the following beyond the per-function proofs it uses as overrides.

1. **Vendored files.** `sign.c`, `sign.h` and `packing.h` from `crypto_sign/ml-dsa-44/clean/` and
   `randombytes.h` from `common/`, PQClean `202a8f9`, unchanged, SHA-256 pinned in
   `scripts/check_target_identity.sh`. `sign.c` is compiled into the same translation unit as the
   other vendored files (`scripts/build_bitcode.sh`).
2. **Assumed specs** (`llvm_unsafe_assume_spec`). Each callee below is not simulated. Its spec
   says it writes exactly the listed outputs, as an opaque Cryptol function of its inputs, kept
   uninterpreted in the proof, and leaves its inputs unchanged. What is trusted is that frame: the
   function terminates, writes nothing else (no out-of-bounds write, no write to its const inputs),
   and its outputs depend only on the listed inputs. Nothing is assumed about the values computed.
   - `PQCLEAN_MLDSA44_CLEAN_unpack_pk`: writes `rho` (32 bytes) and `t1` from `pk`.
   - `PQCLEAN_MLDSA44_CLEAN_unpack_sig`: writes `c`, `z`, `h` from `sig`, returns an int.
   - `PQCLEAN_MLDSA44_CLEAN_polyvecl_chknorm`: called with bound `GAMMA1 - BETA`, returns 1 or 0
     (`polyvec.c:152-156`); whether it returns 1 is the opaque `chkZ z`.
   - `shake256`: 64 bytes of output from the 1312-byte public key.
   - `shake256_inc_init`, `shake256_inc_absorb` (lengths 64, 2, 0 with a NULL input, 32, 768),
     `shake256_inc_finalize`, `shake256_inc_squeeze` (lengths 64 and 32),
     `shake256_inc_ctx_release`: the state is modelled as the 26 words `fips202.c` allocates
     behind `shake256incctx.ctx`; init allocates them, release reads them and does nothing else
     the proof can see. The initial state `incInit` is a constant (zero) rather than opaque,
     because SAW unfolds constants on one side of the comparison; as it only flows into opaque
     functions this does not narrow the claim.
   - `PQCLEAN_MLDSA44_CLEAN_poly_challenge`: writes `cp` from the 32-byte `c`.
   - `PQCLEAN_MLDSA44_CLEAN_polyvec_matrix_expand`: writes the 4x4 matrix from `rho`.
   - `PQCLEAN_MLDSA44_CLEAN_polyveck_use_hint`: in the aliased form `(w1, w1, h)`.
   - `PQCLEAN_MLDSA44_CLEAN_polyveck_pack_w1`: writes 768 bytes from `w1`.
   - Key generation: `PQCLEAN_randombytes` (32 bytes, returns 0; the bytes are the ghost value
     `rng`, which the keypair spec binds as its input `rb`), `shake256` in the in-place form
     `(seedbuf, 128, seedbuf, 34)`, `PQCLEAN_MLDSA44_CLEAN_polyvecl_uniform_eta` (nonce 0) and
     `PQCLEAN_MLDSA44_CLEAN_polyveck_uniform_eta` (nonce 4), `PQCLEAN_MLDSA44_CLEAN_polyveck_power2round`
     in the aliased form `(t1, t0, t1)`, `PQCLEAN_MLDSA44_CLEAN_pack_pk`,
     `PQCLEAN_MLDSA44_CLEAN_pack_sk`.
   - Signing: `PQCLEAN_MLDSA44_CLEAN_unpack_sk` (writes `rho`, `tr`, `key`, `t0`, `s1`, `s2` from
     `sk`), `shake256` in the form `(rhoprime, 64, key, 128)` (`key`, `rnd`, `mu` are contiguous in
     `seedbuf`), `PQCLEAN_MLDSA44_CLEAN_polyvecl_uniform_gamma1` (any nonce),
     `PQCLEAN_MLDSA44_CLEAN_polyveck_decompose` in the aliased form `(w1, w0, w1)`,
     `PQCLEAN_MLDSA44_CLEAN_pack_sig` in the form `(sig, sig, z, h)`, and the four loop checks:
     `polyvecl_chknorm` (bound `GAMMA1 - BETA`), `PQCLEAN_MLDSA44_CLEAN_polyveck_chknorm` (bounds
     `GAMMA2 - BETA` and `GAMMA2`), returning 1 or 0 (`polyvec.c:315-319`), and
     `PQCLEAN_MLDSA44_CLEAN_polyveck_make_hint`, which writes `h` and returns a count. sign.c uses
     that count only in `n > OMEGA` (`sign.c:186`), so its spec returns 81 when the opaque
     `hintBad` holds and 0 otherwise, instead of the count. This is a step read from the source, not
     proved. The checks' specs take their verdict from SAW ghost state and assert, as an override
     precondition, that the opaque check on the actual arguments equals it; that makes the loop's
     branches concrete without assuming anything about the verdicts beyond the top-level schedule.
3. **Message length 32 bytes, empty context.** The message absorb is specified at length 32, so the
   result is for `mlen = 32` and the `crypto_sign_verify` and `crypto_sign_signature` entry points
   (`ctx = NULL`, `ctxlen = 0`). Other lengths would need their own absorb spec or a symbolic-length one.
4. **Not covered.** Signing schedules with three or more passes of the `goto rej` loop, and
   `crypto_sign_open`. Signing is proved for pass 0 accepted, and for pass 0 rejected at each of
   the four checks with pass 1 accepted; each schedule is a precondition on the model, so the
   result says what the C writes when the model's checks come out that way. The final 32-byte
   comparison in verification is simulated, not assumed.
5. **A free input is needed.** Key generation has no input other than the random bytes. In the
   first version `randombytes` returned an opaque function of its length, so every term was closed,
   SAW evaluated the placeholder bodies, and a wrong composition (s1 not transformed) passed. The
   random bytes are now a symbolic input bound through ghost state, and the five keygen mutants
   fail.
6. **Opaque names checked live.** The proof would be weaker if SAW unfolded the opaque functions
   to their placeholder bodies (for example `absorbM s _ = s` would make the message irrelevant).
   Mutants that drop the message absorb, the `unpack_sig` check, or the `chknorm` check are
   rejected, which can only happen if those functions stay uninterpreted. For signing, a run with
   the schedule's ghost verdicts but no precondition on the model must fail, and does: the check
   specs' verdict obligations are then unprovable.
7. **Ghost-bound variables in override preconditions.** A first version of the signing proof bound
   the verdict from ghost state into a fresh variable and used it in the override's `llvm_precond`.
   Under SAW 1.5.1 the obligation failed with that variable free in the counterexample, though the
   same obligation with the verdict written as a constant passed. The verdicts are now concrete per step (one override per
   check and step, selected by a concrete ghost counter). It failed rather than passed, so no claim
   depended on it.

## A-HQC: HQC `vect_mul` (recorded 2026-10-22)

For hqc-1, hqc-3 and hqc-5, two results compose:
- `make hqc` (SAW) proves that `vect_mul` in `target/hqc/gf2x.c` (HQC v5.0.0) writes `vmul a b`
  (`model/cryptol/hqc/KM<p>.cry`) for every pair of N-word inputs.
- `make hqc-isabelle` proves `HQC_P<p>.vmul_correct`: for inputs whose polynomials have degree
  below n, `vmul a b` is `(a * b) mod (x^n - 1)` over GF(2).

What that rests on:

1. **The model.** `vmul a b = fold`{n} (km<N> a b)`. `km<s>` is one Karatsuba level (`kstep`,
   written to follow `karatsuba_mul`'s step 4) over `km<s/2>` and `km<s - s/2>`, down to `km1`, a
   64-bit shift-and-XOR loop (`clmul1`). `fold` is the reduction stated on bits. The model has
   no `pmult` because SAW's Isabelle library has none. At the leaf sizes it is cross-checked against
   Cryptol's `pmult` with `rme` (in `make hqc`), but that check is not part of the chain.
2. **The lift.** `cryptol-to-isabelle` is trusted. `make lift-check` regenerates `GF2X`, `Fold` and
   `KM<p>` and diffs them against the committed theories.
3. **Isabelle.** The theorems use no `sorry`, `smt` or `by eval`. `HQC_Gate` fails the build if
   `vmul_correct` depends on any oracle or proof hole. GF(2) is `HOL-Library.Z2`. Since 2026-10-26
   it also fails the build on axioms: the kernel's dependency record does not list them, so the gate
   compares the context's axioms with those of `Main` and requires every additional one to be a
   definition (in the theory's specification table) or a type axiom generated by typedef, typedecl or
   datatype (226 of them; 4377 axioms beyond Main in all). The Cryptol support session that SAW ships
   contains `Unsupported.thy` with `axiomatization where unsupported: "\<And>P. PROP P"`, which proves
   every proposition; no theory we import imports it, and the gate fails if it is in the context.
   HOL's own axioms are trusted. Checked by a throwaway theory that adds `axiomatization where bogus:
   "False"` (the same ML rejects it).
4. **The degree hypothesis.** `vmul_correct` assumes deg a, deg b < n: the inputs have no bit at or
   above n in their last word, which is how HQC stores vectors. The SAW result has no
   precondition. On other inputs the C still equals `vmul`, but `vmul` is not a product mod
   x^n - 1 there, because the fold assumes the product has degree below 2n.
5. **Children are uninterpreted in each level's SAW proof.**
   - Each `karatsuba_mul(s)` proof uses the proved specs of the two child sizes as overrides and
     keeps `km<child>` uninterpreted, so the obligation is the step-4 assembly and the buffer flow.
   - The leaf `karatsuba_mul(s)` keeps `km<s>` uninterpreted for the same reason.
6. **Solvers.**
   - `schoolbook_mul` is proved against `km<s>` with SAW's `rme` backend (algebraic normal form
     over GF(2)).
   - The levels and `vect_mul` use z3, and the mutants use abc.
   - On the PQClean HQC `base_mul` (not in this repo), abc, z3 and yices did not finish in over
     10 minutes where `rme` took 0.17 s. That measurement is from scratch work, recorded to
     explain the choice of backend.
   - False obligations (2026-10-25, `scripts/hqc_solver_study.sh 1 8 600 false|cmut`, M2 Max while
     other proofs ran, so the times are upper bounds). The specification with bit 0 flipped is
     refuted by every backend: rme 2 s, abc 62, z3 108, yices 6, cvc5 12, bitwuzla 6. The true
     specification against the C with one schoolbook term dropped (the `ref-schoolbook-carry`
     source mutant of item 15) is refuted by abc in 59 s, z3 108, yices 4, bitwuzla 4, and not by
     rme or cvc5 in 600 s. So "rme does not refute" is wrong as a generality: it refutes a
     constant difference at once and did not refute a difference of many monomials in the time
     given; the SAT-based backends refute both. Output: `build/hqc/solvers_false.out`,
     `build/hqc/solvers_cmut.out`.
7. **tmp_buffer.**
   - Each `karatsuba_mul(s)` spec allocates exactly the words the recursion uses (8s plus the
     larger child's).
   - Leaves get one word, so that a child pointer at the end of its parent's buffer matches an
     allocation.
   - SAW checks every access against those allocations, so `vect_mul`'s
     `TMP_BUFFER_WORDS = 16 * VEC_N_SIZE_64` is shown to suffice. Counting the one-word leaf
     slack, that is 4313 of 4432 words (hqc-1), 8865 of 8976 (hqc-3) and 14217 of 14416 (hqc-5).
8. **Generated files.** `proof/hqc/gen_hqc.py` writes the SAW scripts, `KM<p>.cry` and
   `HQC_P<p>.thy`. `make hqc` and `make hqc-isabelle` run it with `--check` and fail if a
   committed copy differs.
9. **Compiler.** `-O0` bitcode from the host clang, as for the ML-DSA target.
10. **Mutants.** Every SAW spec has a `_mut_spec` that must fail: the result for a different `b`
    at every size, and `fold` at n - 1 for `vect_mul`.
11. **GF(2^8) and Reed-Solomon (`proof/hqc/gf.saw`, `proof/hqc/code_<p>.saw`).**
    - The field is defined by Cryptol's `pmult` and `pmod` modulo 0x11D (`GF256.cry`), the
      polynomial of v5.0.0 and of the 2025-08-22 specification. The 2026-10-12 specification
      changes it to 0x11B; these results are for v5.0.0 and will be regenerated for the next release.
    - The Reed-Solomon spec is a property, not an algorithm: the top k bytes are the message and
      the codeword vanishes at alpha^1 .. alpha^(2 delta) with alpha = 2. Two codewords with the same
      message part differ in a polynomial of degree below 2 delta with 2 delta roots, so the
      property fixes the codeword. That uniqueness argument is not mechanized.
    - `gf.c`, `reed_solomon.c`, `reed_muller.c`, `crypto_memset.c` and `code.c` are compiled as one
      unit (`build/hqc/_code.c`) so the RS proof uses a `gf_mul` proved in the same module, not an
      assumed one, and the `code_encode` proof (item 14) uses the RS and RM specs proved there.
    - `gf_reduce` is documented for degree at most 14; it is proved for every 16-bit input.
    - Field facts (a^254 is the inverse of nonzero a) are checked by z3 over all 256 elements, not
      in Isabelle.
12. **The AVX2 implementation (A-HQC-AVX, recorded 2026-10-24, repaired source since 2026-10-25).**
    `target/hqc/avx2/` vendors `src/x86_64/common/hqc-<p>/gf2x.c` of the same v5.0.0 commit.
    `make hqc-avx` proves, for each parameter set, that its `vect_mul` writes `vmulBytes a b`: the bytes of `fold`{n}` applied to a
    Toom-3 / Karatsuba model (`AVX<p>.cry`, `AVXK.cry`, `Toom.cry`) whose leaf is `pclmulqdq`.
    `make hqc-isabelle` proves `AVX_P<p>.vmulA_correct` for the three sets: the word-level model
    is `(a * b) mod (x^n - 1)` for inputs of degree below n. The Toom step is `Toom.cry` (hqc-1
    and hqc-3, y = x^64, generic in the third size) and `Toom5.cry` (hqc-5, y = x^256, the
    sizes written out: 312-word thirds padded to 320, 640-word products), each split into small
    functions with one Isabelle lemma per function (`AVX_Toom`, `AVX_Toom5`); the exact divisions
    by y and 1 + y are `Pl_tl`/`Pl_drop4` and `Pl_pxl`/`Pl_pxb`.
    - **Bitcode.** The C is cross-compiled for x86_64 (`--target=x86_64-apple-darwin`, the host
      SDK) at `-O0` with `-mavx -mavx2 -mbmi -mpclmul -D_FORTIFY_SOURCE=0`. Upstream builds it with
      `-O3 -flto`. The proof is about the `-O0` IR, as for every other target here. The compiler
      is Homebrew clang 22.1.8 (`AVX_CLANG` in the Makefile, default `/opt/homebrew/opt/llvm@22`),
      not the Apple clang 17 used for the other targets: the IR rewrite below works on the textual
      IR and needs `llvm-dis`/`llvm-as`, which Apple's toolchain does not ship.
    - **The one-line repair (hqc-1 and hqc-3, since 2026-10-25).** The gated `make hqc-avx` does not
      prove the hqc-1/3 source as shipped: `toom_3_mult` reads one word past `W0` and `W2` (OF-5),
      and SAW stops at the read. It proves the source with the maintainers' fix, which they confirmed
      on 2026-10-25: `W0` and `W2` declared one vector larger (`AVX_FIX_SED` in the Makefile, applied
      with `sed` to a copy in `build/hqc/fixed/`; the build fails unless exactly one line changed).
      This is the only edit to any C under proof in this repository. The vendored file is untouched
      and pinned. hqc-5 is proved as shipped. The source as shipped is proved out of band by
      `make hqc-avx-asis` on bitcode where the two arrays get one `<4 x i64>` of symbolic slack
      instead (`scripts/hqc_avx_ir.py --slack`); that proof shows the word read does not reach the
      result, and it holds only under the assumption that the over-read does not fault; run
      2026-10-25, exit 0 in 4111 s for the three sets with other proofs running
      (`build/hqc/make_avx_asis.out`). First full run of the repaired, symbolic-lane configuration: 2026-10-25, `make hqc-avx` exit 0 in 4103 s
      with other proofs running (`build/hqc/make_avx_fixed.out`); hqc-1 alone 267 s on the idle
      machine.
    - **IR normalization** (`scripts/hqc_avx_ir.py`, run by `make hqc-avx`). Two things in the
      bitcode are rewritten, and each is a trusted step:
      (a) poison operands. Vector literals such as `(__m256i){a, b, 0, 0}` lower to constants with
      `poison` lanes, and `shufflevector` gets a whole-`poison` second operand; Crucible refuses to
      evaluate them. Since 2026-10-25 each such operand is replaced by a load from its own fresh
      global `@__poison_k` (15, 15 and 6 of them; the defined lanes of a partly poison constant are
      re-inserted after the load), and every SAW spec allocates every such global with fresh
      symbolic contents and restates them unchanged after the call (the sidecar
      `build/hqc/avx_<p>.bc.poison.saw` lists them). The proofs therefore hold for every value of
      every undefined lane: the lanes are quantified over, not refined. Before that date the lanes
      were set to zero (gated) and to all ones (`make hqc-avx-poison`, 2026-10-24, all three sets
      passed in 1283, 1732, 2367 s), which was evidence and not a proof; `--poison=zero|ones` remain
      as options for the record;
      (b) two constant GEPs with a negative index (`&ro256[T] - 2`), which Crucible rejects, are
      rewritten as the same address in bytes from the array base.
      Since 2026-10-26 both rewrites are checked by `hqc_avx_ir.py` before it makes them, and the build
      fails otherwise: `poison_never_read` requires every poison lane to be dead (9 insertelement chains
      per set at hqc-1/3 whose intermediates have no other use and which write every poison lane, 6
      shufflevectors per set whose mask selects only the first operand; no other instruction has a
      poison operand), so the rewrite does not change the program's semantics; and each GEP rewrite
      requires the byte offset to lie inside the array. The checked script emits bitcode byte-identical
      to the bitcode `make hqc-avx` proved (compared for all three sets). Trusted: the lane-wise LLVM
      semantics of insertelement/shufflevector, and the script's textual (regex) reading of the IR.
    - **Intrinsics.** `llvm.x86.pclmulqdq` is implemented by SAW 1.5.1 and trusted. Three others
      have no semantics in SAW and are given theirs as assumed specs: `llvm.x86.avx.ldu.dq.256`
      loads 32 bytes; `llvm.x86.avx2.psrli.q` and `llvm.x86.avx2.pslli.q` shift each 64-bit lane (a count of 64
      or more gives 0, as in Cryptol). The counts used are 5/59, 11/53 and 37/27.
    - **Scratch state.** The static scratch arrays of `toom_3_mult` and `karat_mult_5` start with
      arbitrary (symbolic) contents in every spec, so the result is shown not to depend on them.
      Static arrays whose contents are read before being written in a call would show up here.
      Static scratch also makes the function non-reentrant: the theorems are about one sequential
      call with no concurrent access to those arrays, which is how HQC calls it.
    - **Output.** `vect_mul` writes `VEC_N_SIZE_BYTES` bytes (2209, 4482, 7205) with `memcpy`, so
      the SAW spec is a byte view (`vmulBytes`), defined from `vmulA` by splitting words
      little-endian. The Isabelle theorem is about `vmulA`.
    - **Mutants.** Every spec has a mutant (bit 0 of the result flipped) that must fail, at every
      Karatsuba size, the multi-way level, Toom and `vect_mul`. `make hqc-avx` (and, since 2026-10-25,
      `make hqc`: the encoder mutants' model dumps killed a CI runner) runs SAW at `-v 3`
      because at the default level SAW prints each rejected mutant's solver model, including the
      model of the uninterpreted child function, as a term; for the hqc-3 `vect_mul` mutant that
      print exhausted the machine's memory. At `-v 3` the scripts' own `print` lines are not shown,
      so make echoes the VERIFIED line on SAW's exit status (0 only if every `llvm_verify` passed
      and every `fails` mutant was rejected).
    - **Composition with the reference.** `HQC_P<p>.vmul_correct` and `AVX_P<p>.vmulA_correct`
      give the same polynomial for inputs of degree below n, so (with the two SAW results) the
      reference `vect_mul` and the AVX2 `vect_mul` agree on such inputs, for all three sets, on the
      `VEC_N_SIZE_BYTES` bytes the AVX2 function writes: the reference writes `VEC_N_SIZE_64` whole
      words, the AVX2 `reduce` copies `VEC_N_SIZE_BYTES` bytes and leaves the rest of the 284-,
      572- or 936-word output buffer as the caller had it.
13. **Reed-Muller encoding (`proof/hqc/code_<p>.saw`, recorded 2026-10-24).** `target/hqc/reed_muller.c`
    (with `reed_muller.h`, `data_structures.h`) is vendored from the same commit.
    - The spec is a property (`RM.cry`): the RM(1,7) codeword of a message byte m is the vector of
      the 128 values of the affine function x -> m7 + m0 x0 + ... + m6 x6 over F_2^7, bit j of the
      codeword being the value at the point with binary digits j. The C's generator rows (the masks
      0xaaaaaaaa, 0xcccccccc, ... and the word pattern for bits 5 and 6) are not restated; SAW
      shows they produce that function. The duplicated code repeats each codeword n2/128 times
      (3, 5, 5) and the n1 bytes (46, 56, 90) give n1 * n2 = 17664, 35840, 57600 bits.
    - The input is the first n1 bytes of the `VEC_N1_SIZE_64`-word message array, as the C reads
      it; the output is the `VEC_N1N2_SIZE_64` words (276, 560, 900) as little-endian bytes. The
      bit order inside a codeword (bit j of the 128-bit value is bit j mod 64 of word j / 64) is
      part of the spec; it is what `reed_muller_decode` and the specification's byte layout assume.
    - The mutant flips bit 0 of the output.
    - Whether the HQC specification document's generator matrix for RM(1,7) matches this code is a
      question about the document (see upstream issue 27); the property proved here is the
      standard definition of RM(1,7) and does not depend on the document's presentation.

14. **The concatenated encoder `code_encode` (`proof/hqc/code_<p>.saw`, recorded 2026-10-24).**
    `target/hqc/code.c`, `code.h` and `crypto_memset.c` are vendored from the same commit.
    - The property: the output `e` (`VEC_N1N2_SIZE_64` words) satisfies `e == rmEncode c`,
      `drop c == msg` and `isRS c` for `c = rmExtract e`, i.e. `e` is the Reed-Muller encoding of a
      word that is a Reed-Solomon codeword with the k message bytes on top. `rmExtract` reads each
      byte back from the first copy of its codeword (value at 0 is m7, value at e_i is m7 + m_i).
    - The proof uses the `reed_solomon_encode` and `reed_muller_encode` specs of items 11 and 13 as
      overrides, rewrites with the lemma `rmExtract (rmEncode c) == c` (proved by z3 in the same
      script, `rm_inv`), and discharges the rest with `isRS` and `rmEncode` uninterpreted: after the
      rewrite the goal is the two callees' postconditions. The mutant flips bit 0 of the output.
    - `code_encode` zeroizes its Reed-Solomon buffer through `memset_volatile`, a `volatile` function
      pointer initialised to `memset` (`crypto_memset.c`). The spec allocates that global with its
      initializer; SAW resolves the indirect call to its `memset` override. The zeroization is
      executed, not assumed, but nothing is claimed about it (the buffer is a local).
    - The composition is proved: `code_encode` is verified against the code with the callees as
      proved overrides, not read from the source. Nothing is claimed about `code_decode`.
15. **Source-level mutants, a measurement (`scripts/hqc_c_mutants.sh`, `make hqc-c-mutants`, run
    2026-10-24).** The gated mutants of item 10 perturb the specification. This script instead makes
    a one-line change to a copy of the C (target/ is never edited), compiles it as the gated run does,
    and runs the unchanged hqc-1 script against it, with 1200 s per run; a run that reaches the limit
    is "no result", never "caught". It does not gate anything.
     - Reference `gf2x.c`, `karatsuba_1.saw`: dropping the high-word half of a schoolbook term; dropping
       `z0` from the Karatsuba middle term; placing the recursive child's buffer at `7 * n` instead of
       `8 * n` (an overlap); shifting by `PARAM_N - 1` instead of `PARAM_N` in `reduce`; dropping the
       final mask in `reduce`. The last four are caught in 147 to 159 s, each at the level the change
       belongs to (`karatsuba_mul(17)`, the child override, `vect_mul`, `vect_mul`). The schoolbook
       mutant gets no result in 1200 s under the script's `rme` leaf tactic, and is caught in 54 s with
       that one tactic swapped to `abc`: `rme` builds a canonical form, so it proves a true equality in
       seconds but did not refute a false one in 20 minutes (the gated leaf mutant of item 10 uses `abc`
       for the same reason).
     - AVX2 `hqc-1/gf2x.c`, `avx_1.saw`, two mutants. Dropping the `DD2` term from the middle product
       of `karat_mult_1` (the pclmul leaf): no result in 1200 s under the script's `rme` leaf tactic,
       caught in 8 s with that tactic swapped to `abc`, the same pattern as the reference leaf.
       Replacing the prefix XOR of `divide_by_x_plus_one_256` by a copy: no result. The script's
       earlier levels pass and z3 is inside the `toom_3_mult` obligation at 1200 s on the M2 Max; a
       second run on an otherwise idle Apple M4 Pro was killed at the 4 h limit (14400 s) with no
       result. The true `toom_3_mult` obligation is proved within the 263 s the whole hqc-1 script
       takes, so here the symbolic refutation costs at least fifty times the proof. A universal claim
       is refuted by one instance, so the row `avx-prefix-xor/concrete` runs the same mutant against
       the script with the two inputs of `toom_3_mult` fixed to concrete values (`a_i = i *
       0x9E3779B97F4A7C15 + 0x0123456789ABCDEF`, `b_i` likewise with other constants) and `km96`
       interpreted (the C child is still replaced by its proved override; the 13 static arrays stay
       symbolic, as in the gated proof), so the goal no longer depends on the inputs: caught in 364 s
       (2026-10-25, the time includes the Karatsuba levels the script proves first). The control row
       `avx-prefix-xor/ctl` runs that concrete script against the unmodified C: saw exit 0 in 701 s,
       so the concrete script is not itself broken; the extra time is the script's own gated
       `toom_3_mult` mutant, which the failed run never reached. The concrete runs stop after `toom_3_mult` (a concrete-input result cannot serve
       as the `vect_mul` override).
     - What this shows: a wrong program at four of the five reference levels makes the unchanged
       script fail where the change is, and so does a wrong AVX2 leaf once the leaf tactic can refute;
       it says nothing about C bugs of other shapes, and a symbolic refutation can cost far more
       than the proof (the `rme` leaves, and z3 on the AVX2 Toom level, where only a concrete
       instance refuted the mutant). Under its own tactics the hqc-1 AVX2 script rejected neither
       source mutant within 1200 s.
16. **Aliasing and alignment (recorded 2026-10-25).** Every SAW specification in `karatsuba_<p>.saw`,
    `avx_<p>.saw`, `gf.saw` and `code_<p>.saw` allocates the output and each input as its own
    buffer, so the results assume the output does not alias an input (the C is called that way).
    The AVX2 specifications allocate 32-byte-aligned buffers (`llvm_alloc_aligned 32`), as the
    256-bit loads and stores require. "For all inputs" in the README and the paper means all input
    values under these two conditions.

17. **Native differential test, evidence and not a proof (`scripts/hqc_native/run.sh`, 2026-10-26).**
    The repaired AVX2 `vect_mul` (hqc-1/3; hqc-5 as shipped) against the reference `vect_mul`, both
    compiled for x86-64 with Apple clang 14.0.3 (built on the M2 Max) and again with Apple clang 17.0.0
    (the committed script, built and run on the M4 Pro) at `-O0`, at `-O3 -flto` (the upstream flags) and with
    `-O1 -fsanitize=address`, run under Rosetta 2 on the M4 Pro (macOS 15.8). Per set and configuration
    3016 operand pairs (316 with ASan): 3000 random of degree below n and the 16 pairs from {0, 1,
    x^(n-1), all ones}. Result: 0 mismatches in all nine runs, no byte written past
    `VEC_N_SIZE_BYTES`, bits at and above n zero, no ASan report. Negative control: hqc-1 with
    `W2[i] ^= _mm256_lddqu_si256` replaced by `=` differs on 215 of 216 pairs. This covers the gap
    between the `-O0` bitcode the proofs are about and the production flags only by testing.
18. **Clean-room run of the review artifact (2026-10-27).** `dist/hqc-artifact.zip` as built by
    `scripts/hqc_artifact.sh` at f5e6f72 (146 files), unpacked into an empty directory on the M2 Max and
    run with `HOME` set to an empty directory and `PATH` limited to the system directories, so no tool
    from this checkout or from `~/.isabelle` was visible. The artifact's `setup.sh` fetched and checked
    SAW, the solvers and Cryptol (exit 0). The TUM Isabelle server was unreachable that day and the
    Cambridge mirror returned 404, so the pinned Isabelle2025-2 directory was copied in from this
    checkout's `.tools` and the rest of the Isabelle setup ran from the artifact (exit 0, 529 s). Plain
    `make` then ran `hqc`, `hqc-avx` and `hqc-isabelle`: every SAW script exited 0 with its mutants
    rejected (gf, `code_<p>`, `karatsuba_<p>` and `avx_<p>` for all three sets) and session `HQC`
    finished with the oracle and axiom gates in place, `make` exit 0 after 5185 s, peak SAW RSS
    15193 MB. The first attempt, on the zip from 11d922f, failed at `hqc-avx` because the packaging
    script had dropped the Makefile block defining `AVX_CLANG`; f5e6f72 keeps those blocks and makes
    the packaging fail when a documented target expands an undefined variable.


## A-HQC-FFT: the additive-FFT multiplier, GF(2^64) reference (recorded 2026-10-25, SAW layer complete 2026-10-26)

Target: `target/hqc-fft/gf264_ref/`, the portable reference of the Frobenius additive-FFT multiplier
over GF(2^64) from the artifact of Chen, Chiu, Peng and Yang (TCHES 2026, ePrint 2026/014), commit
c94c84d, public domain; the AVX2 and NEON variants the artifact deploys share its structure. The
milestone (docs/ROADMAP.md) is in two parts: the model multiplies (Isabelle), and the C implements
the model (SAW). Nothing below is a result about the multiplier yet; it is the first SAW layer.

1. **Bitcode.** `make hqc-fft-bitcode`: the ten `.c` files compiled for the host at `-O0` with the
   Homebrew clang 22 (`AVX_CLANG`; `llvm-link` lives beside it), linked into one module, no `-g`
   (SAW's bitcode reader warns on clang 22's debug metadata). The C is not edited.
2. **Model** (`model/cryptol/hqc-fft/FFTRef.cry`, `FFTEnc.cry`). Mirrors the C function by function:
   `mull64` (= `clmul1`), `gf264` (the 128-bit `mull64` product reduced by applying x^64 = x^4 +
   x^3 + x + 1 twice with shifts and XORs, the "0x1b" of `gf264.h`; until 2026-10-29 it was written
   `pmod (pmult a b)`, which cryptol-to-isabelle cannot lift, and `FFTCheck.cry` proves the two equal), the Karatsuba ladder `km2 .. km64` as `kstep` and `km24 = k3step km8`, the Cantor
   basis table and `cantor` (the F2-linear index-to-element map), `butterfly`/`ibutterfly`,
   `stage`/`istage` with twiddle `cantor ((2 m) ^ (scalar >> si))` for unit m of stage si, `btfy9` /
   `ibtfy9` (the 9-stage networks on 512 elements with scalar 2^41), `gf264v`, and `encode`/`decode`
   as the F2-linear maps of `_enc_mat`/`_dec_mat` on the 32 x 512 bit view (element e of the
   encoding is the image of column e; bit 512 t + e of the decoding, t < 64, is bit t of the image
   of element e; the decoding is 512 words, the product's size). `FFTBC.cry` is the basis conversion
   `bc_1`/`ibc_1` at 16384 and 32768 bits as the 25 (resp. 28) layers the C's comments name, each
   layer dividing every 2L-bit block by x^L + x^T in closed form (q = hi + hi div x^(L-T), r = lo +
   q x^T mod x^L, valid because 2T <= L in every layer; proved equal to `pdiv`/`pmod` at two small
   sizes by Cryptol). `FFTTop.cry` is `polymul_280U64_input` and `_mul` as the composition of the
   stage models on the C's word views, cross terms included. Checked against the C on probe inputs
   (scratch harnesses, not committed): `gf264_mul`, `cantor_to_gf264`, `encode_64`, `decode_64`,
   `bc_1`/`ibc_1` at both sizes (13 probes) and, on one random 280-word pair, the two entry points
   themselves (all 512 and 560 words agree).
3. **Proved by SAW, one process per script, each spec paired with a bit-flip mutant that must fail
   (the claim lint pairs them; spec-building functions with a size argument are keyed `kspec(32)`).
   Times are wall-clock for the whole script; "M4 Pro" marks runs on the 24 GB machine, the rest ran on
   the M2 Max (64 GB).**
   hqc-1 (`make hqc-fft`, seven processes). `ref_1.saw` (2026-10-25, 266 s, 29 mutants): `_mull_64 ==
   mull64` (rme); `_gf264_mul` and `gf264_mul == gf264` (rme; the wrapper with the inline as override);
   `karat_mult_128 .. _4096 == km2 .. km64` and `karat_mult_1536 == km24`, each with the level below
   as a proved override and its model uninterpreted (z3); `gf264v_mul(512) == gf264v` with the inline
   `_gf264_mul` as override; `butterfly_64` and `i_butterfly_64` at every unit 2 .. 512 against
   `butterfly`/`ibutterfly` (z3, `gf264` uninterpreted). `ref_2.saw` (2026-10-25, 365 s including
   script 1): `btfy_64`/`ibtfy_64` (9 stages, 512 elements, scalar 2^41) == `btfy9`/`ibtfy9` with the
   kernels as overrides (z3; the twiddles come from the real const tables at concrete indices).
   `ref_3.saw` (2026-10-26, 10 s, M4 Pro): `linear_map_x8 == lin8` (rme) and `encode_64(512, 32) ==
   encode` with it as override (z3, `lin8` uninterpreted). `ref_3d.saw` (2026-10-26, 171 s, M4 Pro):
   `transpose_8x8 == transpose8` (z3) and `decode_64(512) == decode` with it as override (rme, for the
   mutant too: under abc the mutant run was killed at 2320 s on 24 GB). `ref_4.saw` (2026-10-25, 74 s):
   `bc_1(poly, 2048)` == `bc1w` and `ibc_1(poly, 2048)` == `ibc1w` with their routines `repr_s8_1_16384`
   / `irepr_s8_1_16384`, `bc_256(64)` / `ibc_256(64)`, `bc_1_256(64)` / `ibc_1_256(64)` proved first
   (rme) and used as overrides. `ref_4b.saw` (2026-10-25, 86 s): `ibc_1(poly, 4096)` == `ibc1_32768w`
   with `irepr_s8_1_32768`, `ibc_256(128)`, `ibc_1_256(128)` the same way. `fft_1.saw` (2026-10-26, 15 s,
   331 MB): `polymul_280U64_input == inputT` and `polymul_280U64_mul == mulT` with the routines' specs
   assumed (item 8).
   hqc-3 (`make hqc-fft-3`, six processes). `r3_net.saw` (2026-10-26, 533 s, 1.6 GB; includes `ref_1`):
   `gf264v_mul(1024)`, the kernels at unit 1024, and `btfy_64`/`ibtfy_64` (10 stages, scalar 2^42) ==
   `btfy10`/`ibtfy10`. `r3_enc.saw` (10 s, M4 Pro): `encode_64(1024, 32) == encode3`. `r3_dec.saw`
   (4576 s, M4 Pro): `decode_64(1024) == decode3` in 4 batch-range parts (rme; replaced 2026-10-28 by one contract in runs, item 8). `r3_bc.saw` (335 s,
   10 GB): `bc_1(4096)` == `bc1_32768wc`, `ibc_1(8192)` == `ibc1_65536w`, with `irepr_s8_1_65536`,
   `bc_256(128)` / `ibc_256(256)`, `bc_1_256(128)` / `ibc_1_256(256)`. `fft_3.saw` (42 s):
   `polymul_576U64_input/_mul == inputT3/mulT3`.
   hqc-5 (`make hqc-fft-5`, six processes). `r5_net.saw` (2026-10-26, 1654 s, 1.6 GB; includes
   `ref_1`): `gf264v_mul(2048)`, the kernels at units 1024 and 2048, `btfy_64`/`ibtfy_64` (11 stages,
   scalar 2^43) == `btfy11`/`ibtfy11`. `r5_enc.saw` (15 s, M4 Pro): `encode_64(2048, 32) == encode5`.
   `r5_dec.saw` (11368 s, 25.6 GB): `decode_64(2048) == decode5` in 8 batch-range parts (rme; replaced 2026-10-28, item 8).
   `r5_bc.saw` (1052 s, 18 GB): `bc_1(8192)` == `bc1_65536wc`, `ibc_1(16384)` == `ibc1_131072w` (the
   generic `irepr_s8_1` / `ibc_256(512)` / `ibc_1_256(512)` path). `fft_5.saw` (135 s):
   `polymul_input_transform(1024) / polymul_output(1024) == inputT5/mulT5`.
   Every script above exited 0 on its own. As single invocations (2026-10-26, M4 Pro): `make hqc-fft`
   exit 0 in 761 s with 78 anticipated failures (the mutants of its seven scripts, `ref_2` and the
   network scripts re-running `ref_1`'s), `make hqc-fft-3` exit 0 in 5561 s with 80; `make hqc-fft-5` exit 0 in 14585 s with 86
   (2026-10-26, M2 Max, peak SAW resident set 25.7 GB). Rerun 2026-10-27 after the `decode_64`
   repair (item 7) and the shared specifications (item 8), one SAW process per script in the make
   targets' order, every script exit 0: hqc-1 762 s (M4 Pro; ref_1 206, ref_2 260, ref_3 6, ref_3d 173,
   ref_4 50, ref_4b 57, fft_1 10), hqc-3 5544 s (M4 Pro; ref_1 211, r3_net 437, r3_enc 8, r3_dec 4601,
   r3_bc 255, fft_3 32), hqc-5 14847 s (M2 Max; ref_1 281, r5_net 1730, r5_enc 15, r5_dec 11632 at
   25.1 GB peak, r5_bc 1053 at 18.5 GB, fft_5 136), with 78, 80 and 86 anticipated failures, the same
   counts as before. 2026-10-28, with `decode_64` as one contract in runs (item 8), the changed scripts
   only, every one exit 0: `r3_dec` 4515 s and `fft_3` 298 s (M4 Pro), `r5_dec` 10077 s at 15.8 GB and
   `fft_5` 1002 s at 6.5 GB (M2 Max), each with its mutant rejected; with the unchanged scripts' times
   above, hqc-3 5724 s and hqc-5 14158 s, 77 and 79 anticipated failures, peak 18.5 GB (r5_bc).
   2026-10-29, after the model edits that make it liftable to Isabelle (`gf264` in shift/XOR form,
   `dbytes3`/`dbytes5` with the finite index list `[i0 + k | k <- [0 .. 31]]` in place of
   `take`{32} [i0 ...]`, the two `pdiv`/`pmod` checks moved out of `FFTBC.cry`), every target rerun
   in full, every script exit 0: `make hqc-fft` 934 s at 22.1 GB peak, 78 anticipated failures (M2
   Max); `make hqc-fft-3` 6034 s at 11.6 GB, 77 (M4 Pro); `make hqc-fft-5` 16624 s at 19.7 GB, 79 (M2
   Max); `make hqc-fft-asis` 244 s at 16.0 GB, 3 (M2 Max). `make hqc-fft-lemmas` proves the edits
   equal to the old forms (`FFTCheck.cry`: `gf264_is_pmod`, `divBlock_is_pdiv_pmod` at two sizes,
   `runIdx3`/`runIdx5` for the run indices), 13 Q.E.D. by abc. An earlier model with `pdiv`/`pmod` per layer made rme take 30 GB on
   `repr_s8_1_16384` and was replaced by the closed form; rme on `encode_64` in the byte-gather form of
   the model reported every input as a counterexample at 1024 words, which is why the model is written
   in index form and `encode_64` is proved through the `linear_map_x8` override.
4. **Table identity, checked by evaluation, not proved.** `cantor_to_gf264_2x[k] == cantor_to_gf264(2k)`
   for all 16384 k (a C harness, 2026-10-25); the model's `stage` uses the computed form. A SAW
   proof of `btfy_64` against `btfy9` will read the real table (concrete indices), so it will
   re-establish the entries it uses.
5. **Not yet.** The AVX2 variant of the artifact.
   (Done 2026-10-26: the model lemmas. `make hqc-fft-lemmas` proves by abc, in one Cryptol process,
   exit 0 in 1152 s on the M4 Pro, that `encode`/`decode` equal the index-form `encodeIdx`/`decodeIdx`
   of item 2 at all three sizes, and that the batch runs `dbytes3`/`dbytes5` of the partwise
   `decode_64` proofs cover `decode3`/`decode5` at every part and offset; rme had run out of memory on
   the first two.)
   (Done 2026-10-30: part (1) for the three entry points, item 10. Still not done: the reduction
   modulo x^n - 1, which HQC applies after these entry points and which is not in the model.)
6. **Reference test.** `scripts/hqc_fft_native/run.sh` compiles the ten files natively (the repaired
   `dencoder.c` of item 7 and the file as shipped, each at `-O0`, `-O2`, and `-O1` with
   AddressSanitizer and UndefinedBehaviorSanitizer) and compares the entry points at all three lengths
   with a schoolbook product: 36 boundary pairs (zero, one, single bits at the word and length edges,
   all ones) and 500 random pairs (100 under the sanitizers), alternately of degree below n and of full
   buffer width. 2026-10-27: no mismatch in any configuration, no sanitizer report; the negative
   control (one bit of `decode_64` flipped) disagreed on all 46 of its pairs at each length. Evidence
   that the vendored code is the working code and that the repair changes no output, nothing more.
7. **`decode_64` repaired in a copy.** `decode_64` advances its output pointer `ptr += step` after its
   last store, so for batch i it forms the address i bytes past one-past-the-end of the output (up to
   63, 127, 255 bytes at the three lengths). The pointer is never dereferenced; forming it is undefined
   behaviour in C (C11 6.5.6p8) and Crucible stops there. The proofs run on `build/hqc-fft/src/dencoder.c`,
   made by `FFT_FIX_SED` in the Makefile: the store is indexed (`ptr[(k*8+j)*step]`) and the increment
   deleted, one line changed and one deleted, which the rule checks; `target/` is not edited.
   `make hqc-fft-asis` covers the file as shipped at hqc-1 (`asis_1.saw`): `decode_64 == decode` with
   8 words of slack after the output (and a flip mutant rejected), and `fails` without the slack, the
   log naming "a pointer to an address outside of the allocation" (2026-10-28, M2 Max, exit 0, 219 s, transpose_8x8 mutant included;
   22 GB). Reported to the authors on 2026-10-27. Until 2026-10-26 the proofs used the shipped file
   with that slack (8, 16, 32 words) in the specification.
8. **Assumed specifications in `fft_1.saw` (the entry points).** `make hqc-fft` runs seven SAW processes
   in order: `ref_1.saw`, `ref_2.saw`, `ref_3.saw`, `ref_3d.saw`, `ref_4.saw`, `ref_4b.saw` prove every routine against
   its model, and `fft_1.saw` then proves `polymul_280U64_input` and `polymul_280U64_mul` with those
   routines as overrides whose specifications it assumes (`llvm_unsafe_assume_spec`): `karat_mult_512`,
   `karat_mult_1024`, `karat_mult_1536` (ref_1), `gf264v_mul` (ref_1), `btfy_64`, `ibtfy_64` (ref_2),
   `encode_64` (ref_3), `decode_64` (ref_3d, its own process: after other goals in one process its
   rme goal did not finish within 24 GB, alone it takes 110 s), `bc_1` on 2048 bytes (ref_4), `ibc_1` on 4096 bytes (ref_4b). The
   assumed specs are linked to the proved ones as described below. One SAW
   process for all of it ran out of memory on the `decode_64` goal (SAW's term cache grows over a
   long script; 2026-10-26), which is why the target is split. The same structure at the other two
   lengths: `make hqc-fft-3` runs `ref_1`, `r3_net`, `r3_enc`, `r3_dec`, `r3_bc`, then `fft_3.saw`, which assumes
   `karat_mult_4096`, `gf264v_mul` (1024), `btfy_64`/`ibtfy_64` (10 stages), `encode_64`/`decode_64`
   (1024 elements), `bc_1` (4096 bytes), `ibc_1` (8192 bytes); `make hqc-fft-5` runs `ref_1`, `r5_net`,
   `r5_enc`, `r5_dec`, `r5_bc`, then `fft_5.saw`, which assumes `gf264v_mul` (2048), `btfy_64`/`ibtfy_64` (11
   stages), `encode_64`/`decode_64` (2048 elements), `bc_1` (8192 bytes), `ibc_1` (16384 bytes, the
   generic path). Since 2026-10-27 every specification is a SAWScript function in
   `proof/hqc-fft/specs.saw`, included by all scripts, and each assumed specification is an expression
   over it; `scripts/hqc_fft_links.py`, run by the three make targets before SAW, fails unless each
   `llvm_unsafe_assume_spec` in `fft_<p>.saw` has a `llvm_verify` of the same function with the same
   expression (whitespace aside) in a script of the same target, no script redefines a name of
   `specs.saw`, and only `fft_<p>` assumes (it found 10, 8 and 7 links; two planted mismatches, a
   `bc_1` buffer one byte short and a `decode_64` output with slack, were rejected), and no script of a
   target uses `admit`, `assume_unsat` or `quickcheck` (a planted `admit` was rejected). Each routine
   script also proves `linear_map_x8` and `transpose_8x8`, the helpers its `encode_64`/`decode_64`
   proofs use as overrides. At hqc-3 and hqc-5 the `decode_64` contract (`dec3_runs`, `dec5_runs` in
   `proof/hqc-fft/dec_runs.saw`, generated by `scripts/hqc_fft_dec.py`) states the output as 256 and
   512 runs of 32 bytes: batch i writes bytes i + (n/8) t, so the run (i0, t) for i0 a multiple of 32
   is `dbytes<p> x i0 t`, and each run is its own `llvm_points_to_untyped` on a byte view of the output,
   so its own goal over 256 input words. One points-to for the whole output needed more than 45 GB
   under rme at hqc-5. It is one contract with one precondition, proved by one `llvm_verify` in
   `r3_dec.saw` / `r5_dec.saw` and assumed verbatim by `fft_3.saw` / `fft_5.saw`, so the link checker
   covers it like the others. The models of the entry points use `decode3`/`decode5` on words;
   `asm3`/`asm5` (FFTEnc.cry) assemble the runs into words, `fft_<p>` proves `decode<p> x == asm<p> x`
   by rme (`prove_print`, 244 s and 2.3 GB at hqc-3 alone; abc passed 20 GB and sbv_abc 20 minutes
   without an answer), and the entry-point proof unfolds `mulT<p>`, rewrites with that theorem and
   keeps `dbytes<p>` uninterpreted. Until 2026-10-27 the contract was proved in 4 and 8 parts by batch
   range, and the step from the parts to the whole was an argument outside the tools; the run form
   removes it. The generator asserts that the runs cover each output byte once. Item 3 lists what has passed.
9. **Source mutants** (`scripts/hqc_fft_c_mutants.sh`, 2026-10-27, M2 Max, 1800 s and 36 GB per run;
   a mutant counts as caught only if SAW fails on a goal after the last anticipated failure, a crash or
   limit is "no result"). Four one-line edits to copies of the C, each in code that runs at hqc-1,
   against the unchanged scripts: a dropped Karatsuba cross term in `polymul_280U64_mul` (fft_1, z3)
   caught in 115 s; one layer of `bc_256` (ref_4, rme) and one row of `linear_map_x8` (ref_3, rme) no
   result, rme exceeding 24 GB in 36 s and 491 s; a twiddle index `k^1` in `btfy_64` (ref_2, z3) no
   result in 1800 s, also under yices. Variants with a different solver or input: the `bc_256` and
   `linear_map_x8` mutants caught by abc in 10 s and 6 s, the twiddle mutant caught when `btfy_64` runs
   on the concrete input 1 .. 512 (302 s), on which the unchanged C passes (302 s). So the gated scripts
   catch one of four. Two first choices, a shift in the generic `cvt` of `bc_256` (runs only for sizes
   other than 64, 128, 256) and `j<<2` in `btfy_64` (j is always 0 at hqc-1), edited dead code and SAW
   accepted them; they were replaced.



10. **Part (1), Isabelle (2026-10-30, `make hqc-fft-isabelle`, exit 0).** At hqc-1: `Assemble.mulT_correct`:
   for every pair of 280-word operands a, b, `Pl (L (mulT a b (inputT a) (inputT b))) = Pl (L a) * Pl (L b)`
   in GF(2)[x], about the lifted FFTTop.cry (the model SAW proves `polymul_280U64_input` and
   `polymul_280U64_mul` against). Two hypotheses, `encode = encodeIdx` and `decode = decodeIdx`, are the
   FFTEnc.cry lemmas `make hqc-fft-lemmas` proves with abc; since 2026-10-30 Isabelle proves them too
   (item 12), and `Uncond.thy` states the theorems without them. The rest is in Isabelle: the generic theory in `spec/isabelle/hqc-fft/math` (Cantor-basis
   subspace polynomials, the Lin-Chung-Han butterfly network evaluates on the coset `cantor(base + u)`,
   the iterative stage chain equals the recursive transform and the inverse chain undoes it, the
   inverse basis conversion over any schedule tree gives the polynomial from its novel-basis
   coordinates, encode as partial evaluation) and the bridge to the lifted model (GF(2^64) as F2[x] mod
   the gf264.h modulus, the lifted gf264 as its product; the 64 Cantor constants, the 64 encMat rows and
   the 64 decMat checks as kernel computations by code_simp on an executable product proved correct;
   the lifted stage, btfy9, ibtfy9, encodeIdx, decodeIdx, mulBlock/divBlock layers and the 25/28-layer
   bc/ibc chains as the theory's objects). `FFT_Gate.thy` fails the build if `mulT_correct`,
   `forward_eval`, `fftpart_correct` or `beta_cantor` depends on an oracle or a skipped proof, or if the
   context has an axiom other than a definition or a generated type axiom; a lemma proved by `eval`
   added to its list fails the build (checked 2026-10-30).
   At hqc-3 and hqc-5 (session `HQC_FFT35`, `spec/isabelle/hqc-fft/n35`): `Top3.mulT3_correct`, for every
   pair of 576-word operands, `Pl (L (mulT3 a b (inputT3 a) (inputT3 b))) = Pl (L a) * Pl (L b)` (FFT on
   the low 512 words, base 2^42, 1024 points; km64 cross terms), and `Top5.mulT5_correct`, for every pair
   of 1024-word operands, `Pl (L (mulT5 (inputT5 a) (inputT5 b))) = Pl (L a) * Pl (L b)` (base 2^43, 2048
   points, no cross terms). Hypotheses: `encode3/5 = encodeIdx3/5` and `decode3/5 = decodeIdx3/5`, the
   same abc lemmas, discharged in Isabelle by item 12. The hqc-5 conversions take the C's generic path, whose recursive cvt runs each
   node's hi subtree before its lo subtree; `Commute.layersR_layers` proves that order equal in effect
   to the tree order (a layer with L and T multiples of W commutes with any additive per-W-block map).
   `Gate35.thy` is the same oracle and axiom gate for these theorems; a lemma proved by `eval` added to
   its list fails the build (checked 2026-10-30).
   Scope: the theorems are about the lifted models, and each states the unreduced product of the
   padded operands. Not yet done: the composition with the SAW results into one statement about the
   C, and the reduction modulo x^n - 1 that HQC applies afterwards. (Both done 2026-10-30, item 11.)
11. **The HQC integration, end to end (2026-10-30).** `target/hqc-fft/hqc_wiring/gf2x.c` is the artifact's
   `vect_mul` (its `cachekey` build), vendored byte for byte with the three parameter headers
   (`target/README.md`). The artifact links it against its AVX2/NEON GF(2^64) multipliers, and its
   portable build against a different multiplier (`lib/bitpolymul_ref`); we link it against `gf264_ref`,
   which has the same interface. That combination is what is verified; the artifact does not build it.
   SAW (`make hqc-fft-wire`, `proof/hqc-fft/wire_<p>.saw`): `polymul_17920_input/mul` and
   `polymul_36864_input/mul` (the wrappers) and `vect_mul` equal their FFTWire.cry models at the three
   sets, with the entry points' specifications assumed (`polymul_280U64_input`, `polymul_280U64_mul`,
   `polymul_576U64_input`, `polymul_576U64_mul`, `polymul_input_transform`, `polymul_output`) and tied
   by `scripts/hqc_fft_links.py` to the scripts that prove them (`fft_1`, `fft_3`, `fft_5`); each spec has a bit-flip mutant that fails. Isabelle (`Wire.vmulF<p>_correct`
   with item 10's hypotheses, `Uncond.vmulF<p>_correct_unc` without them, item 12): for inputs of degree below n, `vmulF<p> a b = (a * b) mod (x^n - 1)`. Composed,
   the C `vect_mul` computes the HQC product, with the same right-hand side as the reference and AVX2
   theorems. The padding copies `VEC_N_SIZE_BYTES` bytes, so the last word keeps only its low bytes;
   the degree hypothesis is what makes that the operand.
   Spec change for this: `encode_64` and `decode_64` read `_enc_mat` / `_dec_mat` from mutable globals,
   and a spec that sets up a global in its precondition but does not restate it afterwards leaves it
   unknown to the caller, so `vect_mul`'s second transform could not match its override. `mats_post`
   (`specs.saw`) restates both matrices after `encode_64`, `decode_64` (whole and in runs), the entry
   points and the wrappers; SAW thus also proves the code leaves them unchanged. Rerun with it on
   2026-10-30: `make hqc-fft` (exit 0, 766 s on the M4 Pro, 78 mutants rejected), `make hqc-fft-3` (exit 0, 5730 s on the
   M4 Pro, 77 mutants rejected) and `make hqc-fft-wire` (exit 0, 59 s on the M2 Max, 7 mutants
   rejected). `make hqc-fft-5` and `make hqc-fft-asis` (exit 0, 79 and 3
   mutants rejected; run on the M2 Max after `make hqc-fft`, the three together 15463 s).
12. **The encode/decode lemmas in Isabelle (2026-10-30).** `spec/isabelle/hqc-fft/n35/EncDec.thy` proves
   `encode<p> fx = encodeIdx<p> fx` and `decode<p> fx = decodeIdx<p> fx` for every input at hqc-1, hqc-3
   and hqc-5 (`encode_eq_encodeIdx`, `decode_eq_decodeIdx` and the 3/5 forms). Both sides are
   characterized bit by bit (`encode` word by word, as an XOR of `_enc_mat` rows), and the gather
   indices of `collect64/128/256` and the transpose-and-scatter indices of `decode` are shown to land on
   the bits the index forms name. The theory is generated from the hqc-1 proof by
   `scripts/hqc_fft_gen/encdec_eq.py` (931 lines); `make hqc-fft-isabelle` checks that the committed
   file equals the generator output. `Uncond.thy` instantiates item 10's and item 11's theorems with
   these lemmas: `mulT_correct_unc`, `mulT3_correct_unc`, `mulT5_correct_unc` (the product, no
   hypothesis) and `vmulF1/3/5_correct_unc` (only the degree bounds). `Gate35.thy` checks all twelve for
   oracles and proof holes; a lemma proved by `eval` added to its list fails the build (checked
   2026-10-30: "ORACLE GATE: Uncond.neg_eval depends on [Code_Generator.holds_by_evaluation]", exit 2).
   `make hqc-fft-isabelle` exit 0; HQC_FFT35 rebuilt clean in 3 min 31 s on the M2 Max. The abc lemmas of
   `make hqc-fft-lemmas` are no longer used by any theorem and stay as an independent check.
