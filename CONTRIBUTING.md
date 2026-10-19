# Contributing & reproduction

## Reproducing the result
1. `./scripts/setup.sh` — installs and pins the exact tool versions.
2. `make verify` — runs the full pipeline. A zero exit code means every step checked.
3. If a step fails, it should fail loudly and name which step. Open an issue with the log.

## Proof conventions
- No step is "done" until its tool verifies it. See `CLAUDE.md` prime directive.
- Keep the target C unmodified and pinned. Document any required transformation.
- Record every assumption in `docs/ASSUMPTIONS.md` as you introduce it.

## Responsible disclosure
If verification surfaces a real discrepancy in a deployed implementation:
1. Do **not** post it publicly first. This repo is public, so a commit is a publication: do not
   record the finding in `docs/ASSUMPTIONS.md` or anywhere else in the tree yet.
2. Keep the details in a GitHub private security advisory on this repo (Security tab, "Report a
   vulnerability"), or outside the repo.
3. Report to the implementation's maintainers (e.g. the upstream repo's security contact).
4. After the maintainers have fixed it or agreed to disclosure, record it under
   `docs/ASSUMPTIONS.md` → "Open findings".
5. Notify the PQC standards community (pqc-forum) only after maintainer contact.
Coordinated disclosure is both the right thing and the higher-reputation path.
