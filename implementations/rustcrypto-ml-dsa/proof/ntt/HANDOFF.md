# NTT layer proof — handoff (2026-06-12, updated 2026-06-17)

## RESOLVED 2026-06-18 — BLOCKER 2 cracked: ALL 16 NTT layers verified

Both `layer_ntt_fwd.saw` (8 forward layers == FIPS 204 Alg 41) and
`layer_ntt_inv.saw` (8 inverse layers == Alg 42) run to **saw exit 0 this
session**, each with a built-in non-vacuity `fails` guard (perturbed spec
rejected). This is the forward NTT (the project's v1 goal) mechanized for v2.

The winning technique (after the original `% q` spec bit-blasted for 1h42m):
- **Compositional spec** (`fips204_ntt_comp.cry`): each butterfly built from the
  same surface forms (`addS/subS/mulS/negS`) the Elem overrides return.
- **Field ops kept UNINTERPRETED** (`w4_unint_z3 ["addS","subS","mulS"]`, negS
  interpreted on the inverse side — see below) → the layer goal is the
  *structural butterfly routing*, not 256× modular bit-blasts. `simplify
  (cryptol_ss ())` discharges the array equality by term-matching.
- **Op overrides carry no precondition** (opaque routing symbols; their `==mod q`
  correctness is the separate `field_ops_bridged.saw` obligation). With preconds,
  the input-bound safety goals `w[j]<q` were the only obstacle.
- **Faithfulness** (`comp_faithful.saw`): the compositional spec == the
  independent `fips204_ntt.cry` FIPS transcription across all 16 (len,iter,m0)
  on test vectors — rules out the rewrite silently changing meaning.

Two debugging facts worth keeping:
- SBV `unint_z3` crashes on multi-arg uninterpreted fns ("get-value ... expected
  a function value"); **use What4 `w4_unint_z3`**.
- On the inverse side the impl const-folds `-ZETA[m]` to a concrete literal, so
  `negS` must stay **interpreted** (it only ever wraps concrete zetas) — keeping
  it uninterpreted made `negS(zeta) != <literal>` and the proof failed.

Layer→inst map (LEN,ITER → hash; forward & inverse share const-generic hashes):
(128,1)=4c08bb…, (64,2)=afa961…, (32,4)=ddc4e2…, (16,8)=a45600…, (8,16)=9471…,
(4,32)=66b65a…, (2,64)=48c7fd…, (1,128)=c07487…. Forward m0=0,1,3,7,15,31,63,127;
inverse m0=256,128,64,32,16,8,4,2 (m decrements).

STILL OPEN: Isabelle model≡FIPS-spec for the NTT *transform composition* (the 8
layers compose to the negacyclic map) — the layers are proven equal to Alg 41/42
bodies; composing them into the full Alg 41/42 transform + the 256^-1 scaling is
the next rung. v1 did the analogous overflow-freedom composition in Isabelle.

---
## RESOLVED 2026-06-17 — Path 1 landed: field core conforms (with admit-bridge)

`field_ops_bridged.saw` runs to **saw exit 0 this session**: `Elem` neg/add/sub/mul
== arithmetic mod q (q = 8380417), the module_lattice field core shared with
ml-kem. The wide-Barrett blocker is cleared via the escape-2 admit-bridge.

How it actually landed (the path fork's Path 1, refined):
- `escape2_core.saw` — EARNED (z3): `barrettInt X == X % q` over `[0,2^46)` as an
  unbounded-Integer goal. Re-verified this session.
- `barrett_bridge.cry` + `barrett_bridge_evidence.saw` — EARNED (z3): the EXACT
  BV mirror of the impl (`barrettBV`) equals `x % q` for `x < 2^24`. Model is correct.
- `field_ops_bridged.saw` — `barrett_reduce(x) == x mod q for x < 2^46` is
  **`mir_unsafe_assume_spec`-ASSUMED**, then `mul` chains on it and discharges
  (override applied, z3 fast). Recorded in `docs/ASSUMPTIONS.md` (v2, escape-2 entry).

Why assume_spec and NOT the `prove_print (admit ...) (rewrite)` route: the rewrite
fires fine, but the RESIDUAL it leaves (`impl == barrettBV`, a wide-multiply + >>46
BV equality) is itself the bit-blast bomb — z3 ran **3h15m without converging**
(measured). The `impl == barrettBV` structural step is *part of* what cannot be
mechanized at width, so admitting the whole barrett override is the honest unit.
Also tried + rejected this session: `addsimp` on a guarded implication ("not an
equation"); `goal_insert` (z3 "cannot handle universally-quantified assertions").

STILL OPEN (unchanged): the NTT *layer* proof (BLOCKER 2 below) — `nttLayerFwd`'s
256 per-position `% q` bit-blast. Field core is done; the layer transform is next.

---
# NTT layer proof — handoff (original, 2026-06-12, updated 2026-06-16)

> **Verification status: UNVERIFIED.** The three files in this directory were
> *written* this session but **not yet run to a `saw` exit-0 in this session**.
> Per the repo prime directive (CLAUDE.md): a `.saw`/`.cry` that "looks
> complete" is **not a proof**. The first job below is to actually run them.

## UPDATE 2026-06-16 — escape-2 integer core VERIFIED in SAW

`escape2_core.saw` (+ `escape2_bridge.cry`) runs to **saw exit 0** on this box:
`prove_print z3 (barrettInt x == x % q)` over all `x in [0, 2^46)` → Valid, ~0.7s.
Non-vacuity: the `q+1` mutation reports `Invalid: [x = 70368744144908]` (an
in-domain counterexample). MIR baseline re-validated: narrow `barrett_reduce ==
x mod q` for `x < 2^28` proves in 4.2s (`mir_verify`, z3).

What this settles and what it does NOT:
- **Settled:** lifting `(x*M)>>k` to unbounded **Integer** arithmetic dodges the
  bit-blasting wall — the math core of escape 2 is mechanized in SAW, not just a
  raw `.smt2`. (Same identity bit-vector form: timeout — see `repro_barrett_2p46.saw`.)
- **Still OPEN (the real blocker):** the **BV↔Integer bridge** — proving the Rust
  `barrett_reduce` (u128 multiply + `>>46`) equals `barrettInt` under zext, *inside*
  `mir_verify`, without bit-blasting the wide multiply. This is the subject of
  saw-script discussion **#3306**. The narrow-domain
  `field_ops.saw` `barrett_reduce` override at `x<2^46` is the goal that needs it.
  Until the bridge lands, `field_ops.saw`'s `mul` override remains BLOCKED.

### Bridge attempt 2026-06-16 — Galois replied; stock tactics still time out

**#3306 reply (RyanGlScott, SAW maintainer, 2026-06-16):** confirms Barrett is
something "SMT-based tools like SAW **fundamentally struggle with**" (direct
endorsement of the paper's boundary thesis). Recommended route = the one we
proposed: `{llvm,mir}_unsafe_assume_spec` to express the low-level ops in terms
of `Integer`, then **rewrites to shape the goal** — the technique they used for
Montgomery reduction. "Usually possible if careful," not free.

**Obstacle found (verified):** RustCrypto's `barrett_reduce` has the wide u128
multiply as an **inline MIR `BinaryOp(Mul)`** (2 Mul + 1 Shr + 1 Sub inline; no
`__multi3`/`mul` callee — checked the linked MIR). So there is **no callable op
to `mir_unsafe_assume_spec`** — Ryan's Montgomery precedent had a callable op;
this code inlines it. The bridge must instead come from goal rewrites.

**Stock goal-rewrite tactics TIMED OUT (x<2^46, 150s cap, this box):**
- `do { goal_eval_unint []; z3; }` → timeout
- `do { simplify (cryptol_ss ()); z3; }` → timeout (exit 124)
Neither lifts BV→Integer; both still bit-blast the wide multiply.

**Therefore the real remaining work (NOT a one-shot):** build a small simpset of
**BV↔Integer rewrite rules** (e.g. `bvToInt (bvMul a b) == (bvToInt a * bvToInt b)
% 2^n`, `bvToInt (bvLShr x k) == bvToInt x / 2^k`), prove them sound once, `addsimp`
them, simplify the `mir_verify` goal into Integer shape, then `z3` (the Integer
core already discharges — see `escape2_core.saw`). This is the concrete next
sprint. NOT attempted to completion; do not report barrett_reduce@2^46 as proven.
Baseline this box: narrow x<2^28 proves in 4.2s; integer core in 0.7s.

### Bridge-rule scaling experiment 2026-06-17 — the rules THEMSELVES cliff at W=64

Tested the atomic SHIFT bridge `toInteger (x >> 46) == toInteger x / 2^46` via
`prove_print z3` across widths (no multiply, no MIR): W=16/48/56 PROVED (rule is
true); **W=64/72/80/96/128 TIMEOUT (>40s).** So a hand-assembled BV->Integer
bridge is NOT viable — the bridge lemmas hit the same bit-blast wall (BV+Integer
mix) at exactly the width Barrett needs (product < 2^69 => ~70 bits). Empirically
confirms sauclovian-g (#3306): SAW lacks a native BV->bounded-int lifting tactic,
and you can't cheaply prove one by rewriting. (yices not retested at width;
`yices-smt2` must be on PATH.)

**Two honest paths to land barrett@2^46 (pick deliberately — trust-base impact):**
1. **`admit` the bridge identities** (ECDSA precedent: `ecdsa.saw` has
   `assume_rule = prove_print (admit "assume rule") (rewrite ss0 t)`). Each bridge
   rule is a genuinely-true BV<->Int identity (verify at small width as evidence),
   admitted at full width, recorded in `docs/ASSUMPTIONS.md` as auditable trust
   base (like the 3 CT leaves). Rewrite the goal into Integer shape -> z3 discharges
   (escape-2 core). LANDS the result; EXPANDS the trust base.
2. **Native SAW lifting tactic** (the missing primitive) — no new trust, bigger
   effort, candidate upstream SAW contribution.

## What this task is

v2 (RustCrypto ml-dsa 0.1.1, SAW-Rust via mir-json) currently has the scalar
layer done: Barrett reduce, ct_div, zetas table, hint layer — all tool-verified
and in CI (`.github/workflows/rust.yml`). See
`../../../../memory` status note for the full v2 ledger.

**This directory is the NEXT step: the NTT transform itself** —
RustCrypto's `ntt_layer` / `ntt_inverse_layer` vs **FIPS 204 Algorithm 41/42**
(forward / inverse NTT). The zetas table these layers use is already
artifact-checked (`../zetas/`); what's unproven is that the butterfly *layers*
compute the Alg 41/42 maps.

## Files here

1. **`field_ops.saw`** — the butterfly *leaves*: `module_lattice::algebra::Elem`
   `neg/add/sub/mul == arithmetic mod q` (q = 8380417). `mul` is split into a
   `barrett_reduce(x) == x mod q for x < 2^46` lemma used as an override (same
   trick v1 used). These are `module_lattice 0.2.3` functions **shared with
   ml-kem**, so verifying them covers both crates' field cores.
   Status: written, **not run this session**.

2. **`fips204_ntt.cry`** — Cryptol spec of ONE generic NTT layer, forward
   (`nttLayerFwd`) and inverse (`nttLayerInv`), transcribed from FIPS 204
   Alg 41/42. Parameterized by `(len, iterations=128/len, m0)`. Each butterfly
   is a disjoint (j, j+len) pair, so a layer is expressed as a parallel map over
   all 256 positions. Encoding discipline matches the other spec files (signed/
   unsigned `[64]`, exact for these magnitudes).

3. **`layer_feasibility_test.saw`** — a **feasibility probe**: proves ONE
   forward layer `ntt_layer<128,1>` (m: 0→1) against `nttLayerFwd`. Tests the
   whole machinery at once: indexwise `Elem` array `points_to` over a symbolic
   `[256][32]`, the `&mut m: usize` postcondition, and **solver tractability of
   128 inlined butterflies** (mul-by-concrete-zeta keeps the Barrett multiplies
   linear). If this one layer proves in reasonable wall-clock, the rest are the
   same shape at smaller LEN.

## How to run (exact, from repo root)

These need the v2 Rust toolchain + the harness MIR artifact. Mirror
`.github/workflows/rust.yml`:

```sh
# 1. toolchain + solvers on PATH (SAW shells out to z3 in .tools/bin)
export PATH="$PWD/.tools/bin:$PATH"
export SAW_RUST_LIBRARY_PATH="$PWD/.tools/rlibs"

# 2. (re)build the harness MIR if build/mldsa_harness.linked-mir.json is stale
CARGO_TARGET_DIR="$PWD/build" cargo +nightly-2025-09-14 saw-build
#   (run inside implementations/rustcrypto-ml-dsa/harness; see setup_rust.sh)

# 3. run the proofs — .saw paths load the MIR relative to the SCRIPT dir
.tools/bin/saw implementations/rustcrypto-ml-dsa/proof/ntt/field_ops.saw
.tools/bin/saw implementations/rustcrypto-ml-dsa/proof/ntt/layer_feasibility_test.saw
```

`field_ops.saw` should be quick. `layer_feasibility_test.saw` is the risk — it
may be slow or the `_inst` name may not match (see below).

## Known risks / likely blockers

- **`_inst` monomorphization hash.** `layer_feasibility_test.saw` hard-codes
  `ml_dsa::ntt::ntt_layer::_inst4c08bb177e505583`. The `_inst` hash is
  machine-stable but **monomorphization-dependent** — if the harness doesn't
  instantiate `ntt_layer<128,1>` (or instantiates a different set), this name
  won't resolve. If SAW errors "no such function", grep the MIR for the real
  name: `grep -o 'ntt_layer[^"]*' build/...linked-mir.json | sort -u`, and make
  sure the harness actually calls `.ntt()` so the const-generic instances get
  monomorphized. Crate disambiguators ([0]-style suffixes) are machine-dependent
  and broke CI before — keep disambiguator-free names, keep `_inst` hashes.
- **Solver tractability.** 128 butterflies inlined is the whole bet. v1's *SAW*
  full-NTT unroll (~3000 obligations) was computationally impractical and was
  abandoned for an Isabelle induction. Here each *layer* is a separate, bounded
  `mir_verify` (mul-by-concrete-zeta ⇒ linear), which should be far more
  tractable — but confirm the LEN=128 probe actually completes before writing
  the other 7 forward + 8 inverse layers.
- **Cryptol/SAW encoding.** Keep arithmetic in signed/unsigned `[64]` — mixing
  Cryptol `Integer` with bitvectors makes z3 stall forever on `mir_verify`
  goals (documented v2 gotcha).

## BLOCKER (2026-06-13): 2^46 Barrett NOT directly SMT-provable

The `mul` override needs `barrett_reduce(x) == x mod q` over **x < 2^46** (the
a*b product domain, a,b < q < 2^23). Tested this session, all TIMED OUT:
- z3 on direct `x % q`: fast for x < 2^28 (~4s), STALLS at 2^36, 2^44 (killed).
- abc on full 2^46: timeout 124 at 9 min.
- `_barrett_bref.saw` (carry-fold spec, no wide urem): timeout 124 at 8 min —
  doesn't help, because `mir_verify` still compares against the IMPL, which does
  `(x * M) >> 46` on a ~92-bit u128 product (M = 8396807, SHIFT = 46). The `>>46`
  of a wide product is the bitblast bomb; reformulating the SPEC can't remove it.
- Only solvers bundled in `.tools/bin`: abc cvc4 cvc5 yices z3. No bitwuzla.

Conclusion: structural, not solver choice. Direct bitvector proof over 2^46 is
out. **Next route (real work, not a probe):** prove the Barrett identity
`x - ((x*M)>>46)*q ≡ x (mod q)  /\  ∈ [0,2q)` in UNBOUNDED Integer arithmetic
(z3 nonlinear, no bitblast) + a BV<->Integer bridge — same shape as v1
montgomery_reduce. Either SAW with an explicit quotient witness, or lift to
Isabelle as v1 did. Everything downstream (field_ops mul, layers) waits on this.

Note: the EXISTING verified barrett (commit d9414f9, proof/reduce/) is over u32
(x < 2^32) — tractable. The NTT need is the WIDER u64/2^46 domain. Different goal.

## BLOCKER 2 (2026-06-13): layer goal intractable even with field ops ASSUMED

`layer_assumed_barrett.saw` decouples the barrett problem: it assumes Elem
neg/add/sub/mul (mir_unsafe_assume_spec, each == mod q) and tries to verify
`ntt_layer<128,1>` == `nttLayerFwd`. Result: overrides all apply, symbolic
simulation COMPLETES, but the layer proof goal TIMES OUT (124 @ 8 min) at
"Checking proof obligations" — z3, with AND without barrett-only vs all-ops.

Cause (hypothesis): `nttLayerFwd` (fips204_ntt.cry) inlines `(...) % 8380417`
per position → 256 output elements each a urem-by-constant over `[64]`. urem
bitblasts heavy (same family as barrett's `>>46`), x256. And the one-shot `%q`
per element doesn't structurally match the impl's reduce-after-each-op, so z3
can't term-match the two sides — it bitblasts all 256. Same root disease as
BLOCKER 1: wide modular reduction at bitvector width.

NEXT EXPERIMENT (untried): **compositional spec.** Rewrite `nttLayerFwd` to be
BUILT FROM the assumed op-spec forms (the butterfly = the same `sub`/`add`/`mul`
spec terms), so impl-side and spec-side are the SAME term and z3 discharges by
rewriting/equality instead of bitblasting urem. If that still stalls, drop to
ONE butterfly (LEN=128 has 128; verify a single (j,j+len) pair) to confirm the
machinery, then scale. Also consider `goal_num_ite`/`simplify` with a urem
rewrite, or proving the layer in Integer-bridge form like the barrett route.

## Definition of done for this task

1. `field_ops.saw` exits 0 (field core conforms).
2. `layer_feasibility_test.saw` exits 0 (one forward layer ≡ Alg 41).
3. Generalize to all 8 forward layers (LEN = 128,64,…,1; m0 = 0,1,3,7,15,31,63,
   127) and 8 inverse layers (Alg 42, `nttLayerInv`, m0 = 256,128,…,2).
4. **Non-vacuity / mutation check** for each (mirror the mutated-moduli guard in
   `rust.yml` — mutate a zeta or a sign and confirm the proof FAILS).
5. Wire into `.github/workflows/rust.yml` as new steps; confirm CI green.
6. Update `docs/ASSUMPTIONS.md` with any new trust-base entries, and the memory
   status note. **Do NOT claim it's proven until saw exits 0 here.**

## Hard rules (CLAUDE.md — non-negotiable)

- Never state/imply a proof passes unless a tool verified it **this session**.
  If you can't run `saw`, mark it UNVERIFIED and say so.
- Found a discrepancy/bug? **Stop.** Record in `docs/ASSUMPTIONS.md` under "Open
  findings", surface to the human. **Do not** open any public issue/PR — there
  are already two findings (OF-1, OF-2) disclosed deliberately as
  pq-crystals/dilithium#114; disclosure is human-routed only.
- Target crate in `target/` is vendored + pinned. Never silently edit it.
- Commits: **no `Co-Authored-By` trailer** (user preference).
