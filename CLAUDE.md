# Working in this repo (read me first)

This is a **formal verification** project. The output is a machine-checked proof, not just code.
That changes the rules you usually operate under.

## Prime directive
**Never state or imply that a proof passes unless a tool actually verified it in this session.**
A `.thy` file that "looks complete" is not a proof. A SAW script that you wrote is not a result
until `saw` exits 0. If you cannot run the tool, say so and mark the step UNVERIFIED. Fabricated
or assumed proof results are worse than useless here — they destroy the entire point of the project.

## What we are doing
The core claim is the PQClean ML-DSA-44 reference C against FIPS 204: the reduction primitives,
the forward and inverse NTT, and the polynomial layer, via
1. C → Cryptol model (`model/cryptol/`)
2. SAW proves C ≡ Cryptol (`proof/saw/`)
3. `cryptol-to-isabelle` lifts the Cryptol model into Isabelle
4. Isabelle proves the lifted model ≡ FIPS-204 spec (`spec/isabelle/`)

The README's Proved and Not-proved tables are the authoritative scope; `docs/COMPOSITION.md`
separates proved composition from composition read from the source. Do not widen scope without
updating `docs/ROADMAP.md` and those tables.

## Conventions
- Pin every tool version in `scripts/setup.sh`. Reproducibility is the product.
- Every assumption (compiler correctness, checked input ranges, anything out of scope) goes in
  `docs/ASSUMPTIONS.md` the moment it is introduced. Be loud about limitations.
- The target C in `target/` is **vendored and pinned** (commit hash recorded in `target/README.md`).
  Never silently edit it — if a transformation is needed for SAW, document it.
- Before reusing any Apple Isabelle theory, confirm its license in `spec/README.md`.

## Writing (commits, docs, ROADMAP/ASSUMPTIONS, PRs, review comments)
Write plainly, the way a working engineer would. State what changed or what to do, with the
reason and the numbers, then stop. No marketing register, no filler emphasis. Specifics: no
em-dashes (use a period, comma, colon, or parentheses); avoid the stock LLM vocabulary
(comprehensive, robust, leverage, crucial, pivotal, seamless, underscore, testament, "plays a
vital role", "it is important to note", "in conclusion"); no decorative rule-of-three or "not
just X, it's Y" constructions; do not bold every term or add a summary line to every section.
For this repo specifically: a proof result is a fact, so report it like one (theorem name, what
it states, that the tool exited 0), never dress it up.

## If you find a discrepancy / bug
Stop. Do not open any public issue or PR automatically, and do not commit it: this repo is
public, so recording it in `docs/ASSUMPTIONS.md` would disclose it. Keep the details outside the
tree (or in a GitHub private security advisory) and surface it to the human. Disclosure must be
deliberate and go through maintainers first; it goes into "Open findings" only after that (see
`CONTRIBUTING.md`).

## Useful commands
- `make verify`   run the full pipeline (fails loudly if any step doesn't check)
- `make saw`      just the C ≡ Cryptol step
- `make isabelle` just the Isabelle session
- `make clean`    remove build artifacts
