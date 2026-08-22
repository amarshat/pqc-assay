# Q-SEAL reachability (ProVerif)

Section 16 property 5: `PROFILE_ACTION_OBSERVED` (assertion type `0x04`) must not be obtainable through
a host-exposed APDU path. This is a **safety** property over the command surface (earlier text called it
a reachability property, which is the wrong term), so it is checked in ProVerif under a Dolev-Yao
attacker rather than in the SAW/Cryptol pipeline.

## History: this model was vacuous, and was rebuilt

An audit of the submitted artifact found that the previous `property5.pv` proved nothing. `internalCb`
was private and no process ever wrote to it, so the only emitter of `SignedObserved` never ran and the
query held for any model body. The mutant file was falsified only because it adds a reachable emitter on
the host path, so the mutation check did not catch it. Recorded as OF-3 in `docs/ASSUMPTIONS.md`.

The rebuilt model (2026-08-22) has a signing key, two transcript shapes so the assertion type sits inside
the signed bytes, a host command handler, a profile-event source, and a separate assertion builder
reachable only over the private callback channel. The two events of the correspondence are emitted by
**different** processes, so the correspondence is decided by the channel structure rather than by two
adjacent statements.

## The four files

| file | what it is | expected |
|------|-----------|----------|
| `property5.pv` | the model, three queries | Q1 true, Q2 true, key secret |
| `property5_reachable.pv` | same model, reachability query only | event reachable (`not event(...)` is **false**) |
| `property5_mutant.pv` | host path drops the spec 8.4 guard | Q1 false, Q2 false |
| `property5_mutant_databind.pv` | builder signs a handset-supplied subject | Q1 **true**, Q2 false |

Q1 is the correspondence over applet events: every observed-action assertion follows an internal event
carrying the same data. Q2 states it over what the attacker can hold: any observed-typed signature it
obtains was preceded by such an event. Q2 exists because of the fourth row. A builder that is correctly
gated on the private channel but signs handset-supplied fields satisfies Q1 and violates Q2, so Q1 alone
would report a clean result for a broken applet.

`verify_reachability.sh` runs all four and gates on every cell of that table.

## What this model does not establish

- **Injectivity.** The injective form of Q1 cannot be proved once the two events are emitted by separate
  processes: ProVerif's abstraction allows one message on the private channel to be consumed more than
  once. The previous model proved injectivity only because both events came from the same process, which
  is not evidence about the design. Replay of one internal transition into several assertions is
  therefore **not** ruled out here.
- **Mutable profile state.** A version with a real state cell (the current profile state held on a
  private channel, read-modify-written under replication, so an event fires only on an actual state
  change) does not terminate: ProVerif was still generating rules after 10 minutes. The shipped model
  uses a fresh event id per transition instead, which means "a transition occurred" is an assumption of
  the model, not something it checks.
- **Any link to the C.** Unlike properties 1-4/6/7 there is no C == model result here. The guard the
  model needs (the host path must refuse type `0x04`) is separately enforced in the verified C by
  property 7's `qseal_validate_request`, with a mutant that allows it caught in `proof/validate.saw`.
  The two meet at that guard; nothing ties them together formally.

