# Q-SEAL reachability (ProVerif)

Section 16 property 5: `PROFILE_ACTION_OBSERVED` (assertion type `0x04`) cannot be reached through a
host-exposed APDU path. Unlike properties 1-4/6/7, this is a reachability question over the command
surface, not a fixed-format identity, so it is checked in ProVerif (symbolic / Dolev-Yao) rather than in
the SAW/Cryptol pipeline.

## The model

`property5.pv` models two entry points to the applet:

- `hostCreate`, reading from a public channel `host` (attacker-controlled), the host-exposed APDU path.
  It signs an assertion of the type the handset asks for, but only `if t <> OBSERVED` (spec 8.4: that
  type must not be callable by a handset application).
- `internalObserved`, reading from a private channel `internalCb` (the trusted internal eUICC event
  callback, which the attacker cannot use). It signs the `OBSERVED` assertion.

The query is the correspondence

    event(Signed(OBSERVED)) ==> event(InternalFired())

"any signing of an OBSERVED assertion is preceded by the trusted internal callback." ProVerif proves it
**true** for `property5.pv`. `property5_mutant.pv` drops the `if t <> OBSERVED` guard on the host path,
and ProVerif reports the same query **false** (it finds a trace where the attacker obtains an OBSERVED
assertion through `host` with no internal callback). `../../verify_reachability.sh` runs both and exits 0
only if the good model proves the query and the mutant refutes it.

## Scope, and what this does NOT prove

This is a symbolic model of the command surface, not a proof about the C code (there is no C == model
link here, unlike the SAW properties). "Host-exposed" is modelled as a public channel and the trusted
callback as a private one; the real secure-element access boundary (spec section 12) is assumed to map
onto that channel privacy. The model abstracts the applet to the assertion-type dispatch; it does not
model the full CREATE_ASSERTION field validation, READ_EVIDENCE, sessions, or APDU framing. The guard it
proves necessary (the host path must refuse type `0x04`) is exactly the authorization check the property
7 field gate does not make, so this is where that gap is closed at the model level.

## Reproduce

    ./qseal/verify_reachability.sh      # or: make qseal-reachability

Needs `proverif` on PATH (or in `.tools/bin`). ProVerif is not in the SAW toolchain tarball and is not
in the per-push CI (it is a separate OCaml-based tool); it is pinned in `scripts/setup.sh` as an
optional leg.

## Installing ProVerif

`scripts/setup.sh` builds ProVerif 2.05 from source (CLI only) if an OCaml toolchain is present. The
opam package pulls a GTK2 GUI dependency that is not needed, so the source build is simpler:

    brew install opam pkg-config
    opam init --bare --yes
    opam switch create proverif 4.14.1 --yes
    eval "$(opam env --switch proverif)"
    # then re-run scripts/setup.sh, or build by hand:
    curl -LO https://bblanche.gitlabpages.inria.fr/proverif/proverif2.05.tar.gz
    tar xzf proverif2.05.tar.gz && cd proverif2.05 && ./build
    cp proverif <repo>/.tools/bin/
