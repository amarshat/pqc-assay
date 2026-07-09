# A machine-checked capability layer for agent delegation

*Amar Akshat &middot; [github.com/amarshat](https://github.com/amarshat)*

Agent frameworks delegate authority all day: an orchestrator hands a sub-agent the right to call a
tool, the sub-agent hands a narrower right to a worker, and somewhere a server has to decide whether
the credential in front of it is good. Today that credential is usually a bearer token whose
semantics live in prose, and the deciding code is whatever the framework shipped. The failure mode
this layer targets is not the signature math (verifiers have had those bugs too); it is the
verifier accepting something it should not: an escalated scope, a replayed presentation, a token
signed by the wrong key, a revoked grant that still works. These are old problems with names, the
[confused deputy](https://css.csail.mit.edu/6.858/2015/readings/confused-deputy.html) is from 1988
and bearer-token replay has its own section in [RFC 6750](https://www.rfc-editor.org/rfc/rfc6750#section-5),
and agent frameworks are re-encountering them at speed.

Cap-V1 is a small capability layer built for that decision point, with the verifier's rules
machine-checked. A capability is a fixed 191-byte token: issuer, subject, resource, an action
bitmask, a validity window, a delegation-depth budget, an audience, and a chain link to its parent.
Delegation chains only attenuate. The token is signed with a hybrid suite, ECDSA P-256 plus
ML-DSA-44, both required. The honest version of the post-quantum motivation, since
harvest-now-decrypt-later does not apply to signatures: a forgery has to land inside the token's
validity window, so short-lived leaves are not the exposure. Long-lived root grants and the
issuer keys behind them are, and a hybrid suite means the layer needs no re-issuing flag-day when
the classical half falls. The verifier is Rust, and its properties are proved with
[Kani](https://model-checking.github.io/kani/) (bounded model checking via CBMC) over the real
code, not a model of it. Everything below is in the
[repository](https://github.com/amarshat/pqc-assay) under `cap/`, runs in CI on every push that
touches the layer, and reproduces with `make cap-kani`, `make cap-hybrid`, and `make cap-demo`.

The trust boundary, before any claims: the verifier process is trusted, along with its single-use
and revocation stores and whatever feed tells it about revocations. Token holders, the network,
and intermediate delegates are not; the adversary can craft arbitrary tokens, replay and tamper
with presentations, and sign with any key it controls, but cannot forge signatures under keys it
does not hold. The goal is that nothing outside the root grant is ever accepted.

## What is proved

Fifty-five Kani harnesses verify, zero failures, in CI (Kani pinned at 0.67.0). The count
alone means little, and the spec (`docs/cap/CAP-V1.md`) tags every harness honestly: some are
independent theorems, many are definition checks (they assert one clause of a predicate they
assume), and some are `kani::cover!` witnesses that the properties are not vacuous. The ones that
carry the weight:

| Property | What it rules out |
|---|---|
| `serialize` is a bijection between tokens and well-formed 191-byte strings, and injective | token malleability: two tokens can never share bytes, and no byte flip yields a valid sibling |
| `chain_attenuates` (+ flags/type/constraints variant, re-checked at lengths 3 and 4) | escalation anywhere down a chain: an accepted leaf's authority never exceeds the root grant |
| `link_requires_delegation_flag` | a terminal capability spawning children: no delegation without the parent's delegation bit |
| `signed_message_covers_all_fields`, `signed_message_injective` | unsigned fields: the signature covers all 191 bytes, so nothing authorized can be swapped after signing |
| `chain_signing_key_is_delegate`, `confused_deputy_rejected` | key substitution: a valid signature under a key the chain never delegated to does not accept |
| `no_replay`, `full_no_replay` | re-presenting a consumed leaf: the composed gate accepts a presentation at most once |
| `revoked_any_link_kills_chain`, `revoke_root_then_chain_rejects` | zombie authority: revoking an ancestor rejects every chain presented through it, not just the leaf |

Several of these carry mutation-style witnesses, the same device used elsewhere in this repository:
a signer that omits the audience field is shown to collide two different tokens (the correct one
does not); a gate that forgets to consume the replay key is shown to accept the same presentation
twice; a gate that checks revocation only on the leaf is shown to accept a revoked root's chain.
The proof is demonstrated to depend on the clause it protects.

The deployment entry points are `accept_leaf_full` and `accept_chain_full`, which compose field
validation, key binding on every link, the chain rules, single-use, and per-link revocation in one
verified function. That composition is itself a theorem (`full_implies_all_conjuncts`), because an
adversarial review pass caught the docs telling deployers to stack the partial gates by hand,
which silently drops key binding on the chain path. Several of the disclosures below exist because
a review round found the gap.

## Real crypto through the verified gate

Kani cannot run ECDSA or ML-DSA (they are far too large for bounded model checking), so inside the
proofs the signature verdict is an abstract input: the theorems hold for any correct signature
verifier. Two artifacts close the loop with real crypto:

- `make cap-hybrid`: an integration test that generates real ECDSA P-256 and ML-DSA-44 keys, signs
  the canonical bytes, verifies both, and feeds the outcomes plus real key commitments (truncated
  domain-separated SHA-256 of the encoded hybrid key, the library's single definition, pinned by a
  known-answer test) into the same `accept_chain2_signed` the harnesses cover.
- `make cap-demo`: a runnable delegation story. An orchestrator grants read|write to an agent,
  re-delegable; the agent mints a read-only, terminal, narrower leaf for a worker; the worker
  presents the chain to a tool server. Every decision is made by the verified `accept_chain_full`.

The demo's eight cases, verbatim:

```
1. valid delegation chain      sigs=[true ,true ]  ->  ACCEPT
2. replay, same leaf           sigs unchanged     ->  REJECT
3. tampered leaf               sigs=[true ,false]  ->  REJECT
4. escalated leaf, valid sig   sigs=[true ,true ]  ->  REJECT
5. foreign signer, valid sig   sigs=[true ,true ]  ->  REJECT
6. downgrade (classical only)  sigs=[true ,false]  ->  REJECT
7. re-delegated terminal leaf  sigs=[true ,true ,true ]  ->  REJECT
8. fresh leaf, root revoked    sigs=[true ,true ]  ->  REJECT
```

Cases 4, 5, and 7 are the reason a capability layer exists: the signatures are genuinely valid, and
the rejection comes from the verified authorization rules. Case 6 is the hybrid point: an
accept-on-either verifier would return ACCEPT there, which is precisely the state of the world once
the classical scheme falls. The demo self-checks and exits nonzero on any wrong verdict, and CI
runs it.

## What is not proved

This section is the part most write-ups skip, so it is the longest.

- Signature unforgeability is assumed, not proved; no test or model checker can establish it. What
  is proved is the precondition the standard reduction needs: the signed message is the canonical,
  complete, injective encoding of the token. The ML-DSA-44 arithmetic itself is verified elsewhere
  in this repository (SAW/Isabelle, a separate track), but the `ml-dsa`/`p256` crates as used here
  are trusted.
- The key commitment's collision resistance is assumed. It is a 128-bit truncation of SHA-256:
  about 2^128 against substituting a key for a given id, but about 2^64 for a party colliding two
  of its own keys (issuer equivocation; disclosed, not defended). The `sha2` crate is unverified.
  Inside Kani the commitment stays abstract; the bridge from the deployed definition into the
  verified gates is machine-checked, the wiring that uses it is convention.
- Chain theorems are bounded: verified at lengths 2, 3, and 4. There is no machine-checked
  induction over all lengths; longer chains rest on the argument that the link check is local.
- The single-use and revocation stores are bounded at capacity 8, sequential, one per audience.
  The nonce store fails closed when full; the revocation list fails OPEN when full (a full list
  refuses new revocations and the capability stays live). Replicated verifier instances must share
  the store or a consumed presentation replays at a sibling. Distribution of revocations to
  verifiers is out of scope.
- Single-use is per-presentation anti-replay only. It does not bound how many distinct single-use
  leaves a delegate with remaining depth can mint; nothing here contains a compromised
  intermediate. Revocation cuts one `cap_id`, not an agent's key.
- `constraints_digest` is pinned down the chain by byte equality, and that is all: the verifier
  never resolves the digest to a policy or enforces it. Field semantics are v0.1-provisional, and
  the link rules were tightened in this revision (older chains may now reject).
- The gate takes the signature verdict and the key commitment as separate inputs, so a deployer
  must derive both from the same key object: verify the signature under the key whose encoding
  was hashed into the commitment. Wire the verdict from one key and the commitment from another
  and the gate is fooled; no harness can catch that, because both are abstract inside Kani. The
  integration test and demo show the correct wiring.
- Kani proves the Rust source; rustc, CBMC, and the underlying SAT solver are trusted, the usual
  base for this class of tool.

As a capability model, none of this is new. [SPKI/SDSI](https://www.rfc-editor.org/rfc/rfc2693)
did issuer/subject/delegation tuples with attenuating reduction in the 1990s;
[macaroons](https://research.google/pubs/pub41892/), [Biscuit](https://www.biscuitsec.org/),
[UCAN](https://github.com/ucan-wg/spec), and
[ZCAP-LD](https://w3c-ccg.github.io/zcap-spec/) are live systems in the same family;
[EverParse](https://www.microsoft.com/en-us/research/publication/everparse/) and Narcissus
(Delaware et al., ICFP 2019) produce verified parsers for much harder formats. The specific
combination here is a hybrid post-quantum-signed capability token whose verifier is machine-checked
Rust, with the accept path exercised end to end by real hybrid signatures. Even that claim is
scoped: the signature scheme runs against the verified gate, not inside it.

## Reproduce

```
git clone https://github.com/amarshat/pqc-assay && cd pqc-assay
make cap-kani     # 55 Kani harnesses, exits nonzero unless all verify
make cap-hybrid   # real ECDSA P-256 + ML-DSA-44 through the verified accept, plus the key-id KAT
make cap-demo     # the eight-case delegation story above, self-checking
```

Needs cargo; `cap-kani` additionally needs Kani (`cargo install --locked kani-verifier && cargo
kani setup`). The default and Kani builds of the library have zero dependencies; `sha2` compiles
into the library only under the deployment key-id feature, and the signature crates enter only the
tests and demo. CI (`.github/workflows/cap.yml`) runs all three legs on every push that touches
the layer.

The spec, the per-harness honesty tags, and the full scope-and-limitations list are in
[`docs/cap/CAP-V1.md`](../cap/CAP-V1.md). The sibling write-up on this repository's other track,
verifying the ML-DSA arithmetic that backs the post-quantum half, is
[here](verified-esim-attestation.md).
