# Q-SEAL reachability (ProVerif)

## STATUS (2026-08-22): the previous result was vacuous; fixed and re-verified

An audit of the submitted artifact found that the previous `property5.pv` proved nothing. `internalCb`
was declared private and no process ever wrote to it, so `internalObserved`, the only emitter of
`SignedObserved`, could never run and the injective correspondence held for any model body. The mutant
file was falsified only because it adds a reachable emitter on the host path, so the mutation check did
not catch this. Recorded as OF-3 in `docs/ASSUMPTIONS.md`.

Changed here on 2026-08-22:

- `property5.pv` and `property5_mutant.pv` gain a `profileTransition` process that writes to
  `internalCb`, so the observed path is live.
- `property5_reachable.pv` is new: the same model with a reachability query on `SignedObserved`, so a
  dead honest path fails the run instead of passing it.
- `verify_reachability.sh` gates on all three runs and fails loudly with `FAIL (VACUITY)` if the event
  is unreachable.

Verified with ProVerif 2.05 on 2026-08-22, `./qseal/verify_reachability.sh` exit 0:

    RESULT inj-event(SignedObserved(...)) ==> inj-event(InternalFired(...)) is true.      # property5.pv
    RESULT not event(SignedObserved(...)) is false.                                       # reachable
    RESULT inj-event(SignedObserved(...)) ==> inj-event(InternalFired(...)) is false.     # mutant

The middle line is the one that matters: ProVerif proves the negation of a reachability query, so
"is false" means a trace emitting the event exists. Running the witness against the pre-fix model (no
`profileTransition`) gives "is true", i.e. unreachable, and the script fails with `FAIL (VACUITY)`. The
gate discriminates.

Even once it runs, the model is thin: `InternalFired` and `SignedObserved` are consecutive statements in
the only process emitting either, so the correspondence is close to syntactic. Rebuilding it with applet
state, a transcript and a host process is tracked outside this repo, with the rest of the rewrite plan.


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

The query is an injective, parameterised correspondence

    inj-event(SignedObserved(id, subject, digest, policy)) ==>
    inj-event(InternalFired(id, subject, digest, policy))

"every observed-action signing, carrying its event data, is preceded by a distinct trusted internal
callback carrying the same data." Injectivity rules out replaying one internal callback into several
assertions; the parameters rule out an unrelated callback standing in for a different observed action.
ProVerif proves it **true** for `property5.pv`. `property5_mutant.pv` drops the `if t <> OBSERVED` guard,
so on an OBSERVED request the host obtains the assertion with its own event data and no internal callback,
and ProVerif reports the query **false**. `../../verify_reachability.sh` runs both and exits 0 only if the
good model proves the query and the mutant refutes it.

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
