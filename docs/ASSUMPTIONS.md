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
  ★ GAP NOW CLOSED (functional, inverse) — 2026-08-02: `invntt_signed_correct`
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
  - *default (`nsw`)* — used for the **reduce.c** proofs, which therefore DO assert absence of
    signed-overflow UB in their documented input ranges (`montgomery_reduce` under `mont_in_range`,
    `reduce32` under `a <= 2^31-2^22-1`).
  - *`-fwrapv`* — used for the **forward and inverse NTT** functional proofs. The NTT does unreduced
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
    csel {self},{value},{self},NE`) — `csel ...,NE` selects `value` when the `tst` cleared Z, i.e.
    when `condition != 0`. This is exactly the crate's documented `cmovnz` ("move if non-zero")
    contract. It is the only asm primitive on the `reduce` path.
  - `<u32 as cmov::CmovEq>::cmoveq` (`cmov-0.5.4 backends::aarch64::{impl#4}`, reached via ctutils
    `ct_eq` in `decompose`): assumed `*output = (*self == *rhs) ? input : *output`. Justified by
    reading the asm (cseleq32: `eor t,{lhs},{rhs}; cmp t,0; csel {out},{input},{out},EQ` —
    `csel ...,EQ` selects `input` exactly when `lhs ^ rhs == 0`; the surrounding Rust truncates the
    u16 temp back to the u8 `*output`, and all values flowing in are u8-range). Used by the hint-layer
    proofs (2026-06-12). The `cmovne`/u16/u64 variants are NOT overridden (not on any verified path).
  - `core::hint::black_box`: assumed identity (it is an optimizer barrier with no semantic effect).
- **Which `reduce` instances are covered (v2.2, 2026-06-12): ALL THREE moduli the crate uses.**
  The harness's sign/verify entry points force the M = q = 8380417 (final z reduction via
  `mod_plus_minus::<SpecQ>`) and M = 2*gamma2 = 190464 (Decompose) monomorphizations in addition to
  keygen's M = 2^d = 8192 (Power2Round). All three are proven `reduce(x) == x mod M` for **all**
  `u32 x`, no precondition: 2^d because the power-of-two Barrett shift is exact, q and 2*gamma2
  because both exceed 2^16 so the standard `x < M^2` Barrett condition covers the whole u32 domain —
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
    the impl arithmetic (`barrett_bridge.cry::barrettBV`) equals `x % q` for `x < 2^24` — i.e. the
    model used to reason about the impl is correct at tractable width.
  - ADMITTED (the gap): the BV↔bounded-Integer lift at width ~66+ (product `< 2^69`).
    SAW has no native tactic for it; hand-built bridge lemmas themselves cliff at W=64, and the
    direct `mir_verify` residual (`impl == barrettBV`) bit-blasts the wide multiply + `>>46` —
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
    nonlinear multiply/urem/smallReduce, which cliff for eager SMT — hence admitted). Companion
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
  mod q`, the 256^-1 tail scaling being outside the layers) — `proof/ntt/ntt_full_check.saw`.
  NOT mechanized: that the pinned `ntt()` invokes those 8 layers *in that exact order*. The
  implementation's `Polynomial::ntt` / `NttPolynomial::ntt_inverse` are `pub(crate)` (correct
  encapsulation, not a defect) and the full transform is inlined, so there is no callable entry to
  SAW-verify without modifying the vendored, pinned target — which we deliberately do NOT do (the
  pin is the value: we verify the crate as published). The call order is therefore taken
  **by inspection** of the pinned source (`ml-dsa-0.1.1/src/ntt.rs:80-87` forward / `142-149`
  inverse). This is the SAME category of trust as the existing "the harness's sign/verify entry
  points force the monomorphizations" reachability assumption above — cheap to eyeball, pin-breaking
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
    passed — for this function the shift-by-32-then-truncate makes arithmetic/logical shift
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
  `[-2^31, 2^31)` — no overflow** — and that every `montgomery_reduce` input stays in its half-open
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
    different input predicates — SAW proves C ≡ model over the INCLUSIVE range `-2^31*Q ≤ a ≤ Q*2^31`
    (`mont_in_range`), while the Isabelle correctness spec uses the HALF-OPEN `-2^31*Q ≤ a < 2^31*Q`
    (`mont_input_ok`, where the strict `-Q<r<Q` actually holds; OF-1). The composed end-to-end
    correctness claim therefore holds on the half-open intersection (which is the honest, maximal
    domain for the strict-bound spec).
- **model ≡ spec for reduce32 / caddq / freeze (Isabelle leg): VERIFIED (2026-06-08).**
  `isabelle build -D spec/isabelle Assay` exits 0, no `sorry`/`oops`. The lifted Cryptol models satisfy:
  - `caddq_correct`: `is_caddq` (residue-preserving; maps `[-Q,Q)` into `[0,Q)`) — unconditional.
  - `reduce32_correct`: `is_reduce32` (residue-preserving; output in the TRUE window
    `[-6283009, 6283008]`, see OF-2) over the SAW domain `a <= 2^31-2^22-1`. The output-bound proof
    is a floor-division interval argument with a case split at the extreme quotient `t = -256`.
  - `freeze_correct`: `is_freeze` (residue-preserving; output in `[0,Q)`) over the same domain,
    proven compositionally — reduce32's window `[-6283009, 6283008]` lies in `[-Q, Q)`, satisfying
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
  (`fips204_hint44.cry`) is transcribed from FIPS 204 over signed 64-bit words — exact integer
  semantics since every quantity in these algorithms has magnitude < 2^24, far below wrap — NOT from
  the implementation, so this is spec-conformance, not impl-vs-impl. **Non-vacuity checked:** four
  mutations (r0+1, r1+1, negated make_hint, use_hint+1) each fail with a counterexample.
  Trust base: the three assumed CT-layer specs (black_box, cmovnz, cmoveq) + mir-json soundness.
  NOT covered: `bit_pack`/`bit_unpack` (the literal GHSA-5x2r-hc65-25f9 site — the strictly-increasing
  index validation) and the polynomial/vector-level wrappers; scalar layer only.
- **RustCrypto ml-dsa scalar algebra (Power2Round / infinity norm / mod+- q): VERIFIED (2026-06-12).**
  `saw implementations/rustcrypto-ml-dsa/proof/scalar/scalar.saw` exits 0 (3 proofs), each for every
  field element (`x < q`): `power2round` == FIPS 204 Algorithm 35, `infinity_norm` == `|. mod+- q|`
  (Section 2.3 — this gates the security-critical z/ct0 norm checks), and `mod_plus_minus::<SpecQ>`
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
- clang: **Apple clang 17.0.0 (clang-1700.0.13.5)**, system `/usr/bin/clang` (NOT vendored — see below).
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

## Q-SEAL property 5 (ProVerif) modeling assumptions

Rebuilt 2026-08-22 after OF-3. The model (`qseal/proof/proverif/property5.pv`) carries a signing key,
two transcript shapes so the assertion type is inside the signed bytes, a host command handler, a
profile-event source and a separate assertion builder behind a private channel. Three queries hold: the
event correspondence, the same statement over signatures the attacker can hold, and secrecy of the
signing key. Assumptions and non-results, all load-bearing:

- **No C == model link.** Property 5 is symbolic only. The guard it needs (the host path refuses type
  `0x04`) is separately enforced in the verified C by `qseal_validate_request`; nothing formally ties
  the two together.
- **Injectivity is not proved.** With the two events in separate processes ProVerif's abstraction lets
  one private-channel message be consumed more than once, so replaying one internal transition into
  several assertions is not excluded. The pre-OF-3 model did prove the injective form, but only because
  both events were emitted by one process, which was an artefact of the modelling rather than a fact
  about the design.
- **No mutable profile state.** A variant holding the current profile state in a private channel and
  read-modify-writing it under replication did not terminate (ProVerif still generating rules after 10
  minutes on an M-series laptop). The shipped model uses a fresh event id per transition, so "a real
  state transition occurred" is assumed, not checked.
- **Abstract signing.** `sign` is a free constructor: no ML-DSA or ECDSA semantics, no verification
  rule, and the attacker's inability to forge is by construction, not by reduction.
- **No APDU layer.** Fragmentation, chaining and the applet's command dispatch beyond the assertion type
  are not modelled.

## Open findings (handle per CONTRIBUTING.md → Responsible disclosure)
- **OF-3 (2026-08-22, found in an audit of the submitted artifact): the Q-SEAL property-5 ProVerif
  result was vacuous.** In `qseal/proof/proverif/property5.pv` the channel `internalCb` is declared private and
  no process ever performs `out(internalCb, ...)`. `internalObserved` is the only process that emits
  `SignedObserved`, it is guarded on an input from that channel, so it never runs, the antecedent of the
  injective correspondence is unreachable, and ProVerif reports the query true regardless of the rest of
  the model. The mutant file was falsified only because it adds a *reachable* emitter in `hostCreate`,
  so the mutation check never tested the honest model.
  - Scope of the damage: property 5 only. The six SAW properties are unaffected; the whole artifact was
    rebuilt from scratch, including the 41-mutant pass (39 killed, 2 survivors), and they reproduce.
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
  - Still open at the level of the claim, not the code: the corrected model still satisfies its
    correspondence by syntactic adjacency of the two events in one process, so it establishes very
    little. Rebuilding it with applet state, a transcript and a host process is tracked in the rewrite
    plan held outside this repo.
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
    **`pq-crystals/dilithium/ref/reduce.c`** (verified 2026-06-07) — PQClean only re-namespaces it.
    So the finding originates upstream and also affects PQ Code Package `mldsa-native` and liboqs.
    PQClean is being archived (July 2026), so the right disclosure home is **pq-crystals/dilithium**,
    not PQClean. **Do NOT auto-file upstream** (CLAUDE.md); surfaced to the maintainer (human) on
    2026-06-07 to decide deliberately.
  - Impact on Assay: the SAW leg (C ≡ Cryptol model) is unaffected — it asserts no bound. The
    Isabelle correctness spec is stated over the **half-open** domain `-2^31*Q <= a < 2^31*Q`, where
    the strict `-Q < r < Q` is actually true; see `spec/isabelle/MLDSA_NTT_Spec.thy` (`mont_input_ok`).
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
    `2143289344 > 2143289343`). The doc's one-sided precondition is too weak for its postcondition —
    either the precondition should be symmetric or the postcondition low end should be `-6283009`.
  - Severity: **documentation/contract only, not a security or functional bug** (same class as OF-1).
    The reduced value is always a correct residue; only the stated tightness is off, and ML-DSA call
    sites feed `reduce32` magnitudes far below this endpoint.
  - Origin & disclosure routing: same as OF-1 — identical comment in `pq-crystals/dilithium/ref`;
    route to **pq-crystals/dilithium**, not PQClean (archiving). **Do NOT auto-file** (CLAUDE.md);
    surfaced to the human 2026-06-08.
  - Impact on Assay: the SAW leg asserts no output bound, so it is unaffected. The Isabelle
    `is_reduce32` spec uses the **true reachable** window `-6283009 <= r <= 6283008` (not the doc's
    `-6283008`), proven over the SAW domain `a <= 2^31-2^22-1`; see `spec/isabelle/MLDSA_NTT_Spec.thy`.
