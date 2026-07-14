# Target: the C under verification

The implementation being verified is **vendored and pinned** here so the proof is reproducible
against an exact, unmodifiable snapshot.

## Note on PQClean's deprecation (2026-06)
PQClean announced it will be archived read-only in **July 2026** (recommending the
[PQ Code Package](https://github.com/pq-code-package) for maintained PQC). **This does not affect
Assay:** the target files are vendored into this directory (committed, SHA-256 recorded) and built
locally, so nothing here fetches PQClean at build/CI time; and the pinned commit `202a8f9` remains
readable even after the repo is archived. More importantly, this `reduce.c` is **verbatim
`pq-crystals/dilithium` reference code** (PQClean only adds the `PQCLEAN_MLDSA44_CLEAN_` symbol
prefix) — `montgomery_reduce` and its doc comment are byte-identical to
`pq-crystals/dilithium/ref/reduce.c`. So the verification targets the canonical Dilithium reference
shared by PQClean, PQ Code Package's `mldsa-native`, and liboqs — not a single dying distribution.
The natural v2 target (optimized ≡ reference) is **PQ Code Package `mldsa-native`**.

## v1 target (this session: modular reduction only — NOT the NTT yet)
- Source: **PQClean** reference ML-DSA (ML-DSA-44), the `clean` C implementation.
- Subsystem: the **modular-reduction primitives** in `reduce.c`. The forward NTT (`ntt.c`) is
  explicitly out of scope for now; we prove the smaller piece it depends on first.
- The `reduce.c` translation unit defines four functions:
  | Function | Signature | What it does |
  |---|---|---|
  | `..._montgomery_reduce` | `int32_t(int64_t a)` | Montgomery reduction: `r ≡ a·2⁻³² (mod Q)`, `−Q<r<Q`, for `−2³¹·Q ≤ a ≤ Q·2³¹` |
  | `..._reduce32` | `int32_t(int32_t a)` | Barrett-style reduction: `r ≡ a (mod Q)`, `−6283008 ≤ r ≤ 6283008`, for `a ≤ 2³¹−2²²−1` |
  | `..._caddq` | `int32_t(int32_t a)` | Conditional add: `a + (a>>31 & Q)` (adds Q iff `a` negative) |
  | `..._freeze` | `int32_t(int32_t a)` | `caddq(reduce32(a))` → canonical representative in `[0, Q)` |
  (symbol prefix: `PQCLEAN_MLDSA44_CLEAN_`)
- **First proof target (recommended):** `montgomery_reduce` — it is the reduction the forward NTT
  actually calls in its butterflies, so it is "the modular reduction the NTT relies on" per
  docs/ROADMAP.md, and it is fully self-contained (single `int64_t → int32_t`, no memory, no loops).
  *Pending the human's confirmation of which function to target (see checkpoint 2 in the session).*

## RECORD BEFORE PROVING (do not skip)
- Upstream repo URL: https://github.com/PQClean/PQClean
- Commit hash: `202a8f96315f9ed219387a50f7e40d04af037ea8` (committed 2026-05-14)
- Path within repo: `crypto_sign/ml-dsa-44/clean/`
- Date identified: 2026-06-01
- Date vendored: 2026-06-01 (into `target/pqclean/`, verbatim from the pinned commit)
- Files vendored (the exact compile closure for `reduce.c`), with SHA-256 for integrity:
  - `reduce.c`  (the primitives) — `8f57fd817a50d4e9d0e6f719da352ad503ac0bacf76ea492a7f3885520857af9`
  - `reduce.h`  (prototypes + `MONT = -4186625`, `QINV = 58728449`) — `c56a083ce9ea4da55a17e9c2f2da74e7277cdede5b2f8e758e441ff9e0813863`
  - `params.h`  (defines `Q = 8380417`, `N = 256`; self-contained, no further includes) — `0210251cea61d26e49b2dad16c4ed86d65474fbffa54c61af7a22c677ddd3cd2`
  - `LICENSE`   (CC0 dedication, kept alongside) — `5d7798eec4d8c8ef0a72dfe805ec54dfd7b212d3928bf9695fda4095d22829ab`
  - `ntt.c`     (forward NTT + invntt + 256-entry `zetas` table) — `c9fd2b30ef1175f2c66b14c4385a68b22bf500e8349c16d0b5fe1fecf31e5470`
  - `ntt.h`     (prototypes for `ntt` / `invntt_tomont`) — `72e60747ac88f6e3dc9ea7b7b67aed3fa120633bb1e2acfc9a9db948069cecf1`
- Build note: `ntt()` calls `montgomery_reduce`, so `scripts/build_bitcode.sh` compiles a single
  translation unit that `#include`s both `reduce.c` and `ntt.c` (wrapper in `build/`, vendored files
  unedited) — there is no `llvm-link` in the toolchain.
- License of vendored code: **Public Domain (CC0)** — per the per-directory `LICENSE`:
  > Public Domain (https://creativecommons.org/share-your-work/public-domain/cc0/)
  `reduce.c`/`reduce.h`/`params.h` carry no per-file copyright header. The LICENSE's Keccak/AES
  public-domain attribution note does **not** apply to these files. CC0 imposes no attribution or
  header-retention obligation; we keep the `LICENSE` file alongside the vendored code regardless.
- Upstream provenance (per `crypto_sign/ml-dsa-44/META.yml`): the `clean` implementation tracks
  pq-crystals/dilithium commit `cbcd8753a43402885c90343cd6335fb54712cda1`, imported via
  mkannwischer/package-pqclean tree `69049406ed50d83a792f2fa67f6c088dbd0e335e`.

## ML-KEM target (go-wide, vendored 2026-07-14 into `target/pqclean-mlkem/`)

Second algorithm through the same pipeline (reviewer advice on paper-1: two algorithms with a
reusable pipeline beat one deep). Same repo, same pinned commit as the ML-DSA target.

- Upstream repo URL: https://github.com/PQClean/PQClean
- Commit hash: `202a8f96315f9ed219387a50f7e40d04af037ea8` (same pin as above)
- Path within repo: `crypto_kem/ml-kem-512/clean/`
- Date vendored: 2026-07-14 (verbatim, fetched per-file from raw.githubusercontent.com at that hash)
- Files vendored (the compile closure for `ntt.c`), with SHA-256:
  - `ntt.c`     (forward NTT + invntt + basemul + 128-entry signed `zetas`) — `835f1a855990217c4ee0b910631a0d6d29221da936817089172f5250ed0147ea`
  - `ntt.h`     — `b3920d95d1ec5e4151fffee4a5af83c7707655bae7095dcfd247556ee452eb3f`
  - `reduce.c`  (`montgomery_reduce` R=2^16, `barrett_reduce` shift 26) — `b3747f6e4175037781b16f8f299b004412512636029ac1b6ee8f8e9ed0185c71`
  - `reduce.h`  (`MONT = -1044`, `QINV = -3327`) — `264f6e3c6d96ff8d2ad4bf97b9642e318ba6c11f90bcf3744b6fb335c38b89c0`
  - `params.h`  (`KYBER_Q = 3329`, `KYBER_N = 256`) — `db7c409f864ebf0864051516e18515081b3fbc9fa932b2a53c3d10b3287610f4`
  - `LICENSE`   (CC0, byte-identical to the ML-DSA directory's) — `5d7798eec4d8c8ef0a72dfe805ec54dfd7b212d3928bf9695fda4095d22829ab`
- Upstream provenance (per `crypto_kem/ml-kem-512/META.yml`): the `clean` implementation tracks
  pq-crystals/kyber commit `10b478fc3cc4ff6215eb0b6a11bd758bf0929cbd`, imported via
  mkannwischer/package-pqclean tree `85197ff`.
- Scope note: only the NTT compile closure is vendored (ntt/reduce/params); Keccak and the KEM
  layer are out of scope, so the LICENSE's Keccak/AES attribution note does not apply to any
  vendored file here either.
- Width note (why this target doubles as a boundary datum): ML-KEM's reductions are 16-bit
  (Montgomery R=2^16 over q=3329, Barrett shift 26), far below the ~2^46 wide-Barrett wall measured
  on the RustCrypto ML-DSA side, so the reduce layer is expected to discharge with plain eager SMT.

## Rules
- Never edit vendored C silently. If SAW needs a transformation (e.g. isolating a function),
  document exactly what and why here, and prefer a wrapper over an edit.
- When vendored, the files go under `target/pqclean/` (ML-DSA) or `target/pqclean-mlkem/` (ML-KEM)
  and are treated as read-only.
