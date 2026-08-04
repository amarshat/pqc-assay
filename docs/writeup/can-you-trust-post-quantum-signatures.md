# Can you trust your post-quantum signature code, or just its test suite?

*Amar Akshat &middot; [github.com/amarshat](https://github.com/amarshat)*

Post-quantum signatures are going into production now. ML-DSA (the NIST standard, formerly Dilithium) is
showing up in eSIMs, in TLS libraries, in the Linux kernel. All of it gets tested the normal way: run the
implementation against a set of known input/output pairs, check the outputs match.

Test vectors are not the same thing as correctness. They tell you the code is right on the inputs someone
thought to check. They don't tell you it's right on the inputs nobody thought to check, and the arithmetic
bugs that matter in this kind of code (an overflow, a missing reduction step, an off-by-one in a bound)
are exactly the kind that pass test vectors and fail somewhere else. This isn't hypothetical. A real
ML-DSA crate had a `<` that should have been `<=` in its signature verification, which let through
signatures it should have rejected. It passed every test vector. It got a CVE.

I spent the last couple months machine-checking two independent, real-world ML-DSA implementations
(the reference C code most deployments are built on, and a separate Rust crate) against the actual FIPS
204 mathematical specification, not against a test suite. Using the same formal-verification toolchain
Apple open-sourced in May for their own crypto library, SAW, Cryptol, and the Isabelle theorem prover.
The difference from Apple's work: they verified code they wrote and control. I verified code neither I nor
anyone I know wrote, exactly as any third party integrating it would have to.

## What "machine-checked" actually means here

Not "I read the code carefully." Not "I ran a lot of tests." A tool takes the compiled C or Rust, takes a
mathematical model of what FIPS 204 says it should compute, and produces a proof, checkable by anyone, that
the two agree for every possible input, not just the ones in a test file. If the tool can't produce that
proof, I don't get to say the code is verified. Some parts of this development are genuinely proven that
way. A couple of parts I state plainly as argued, not proven, because that's honestly where the tooling
gave out this round.

## What I found

The core arithmetic transform at the heart of both signing and verifying (the NTT, if you want the name)
checks out against the spec, both directions, on both implementations. Along the way I also found two
places where the reference code's own documentation comments describe the wrong output range at an edge
case. Neither is a real bug, the code itself is correct there, but it's the kind of thing that only turns
up when you actually try to prove the stated contract rather than trust the comment. I reported it upstream.

The more interesting result wasn't a bug at all. It was where the verification tools themselves stopped
working. One piece of arithmetic (a wide modular reduction used inside the transform) turned out to be
provably correct, but a certain class of automated solver simply could not finish checking it, no matter
how long I let it run. Restating the exact same mathematical fact in a different form let it check in a
fraction of a second. That gap, between what's true and what a given tool can actually verify in
reasonable time, is its own useful finding for anyone doing this kind of work: the honest answer to "is
this proven" is sometimes "yes, but not with the tool you reached for first."

## Why this matters beyond one library

Post-quantum crypto is moving from research into infrastructure fast, often faster than the implementations
have had time to settle. Machines are increasingly the ones relying on these signatures directly: an agent
verifying that another agent, or a piece of hardware, is who it claims to be, with no human in the loop to
notice something looks off. When the party checking a signature is code, not a person, the gap between
"passes the tests" and "is actually correct" stops being an academic distinction. Silicon-rooted device
identity, agentic commerce, anything that assumes a signature check is a hard guarantee rather than a
tested one, is exactly where this kind of independent, tool-checked verification earns its keep.

Full technical writeup, with the actual proof structure and the exact solver numbers, is here:
[Verifying third-party post-quantum C against its spec, with SAW + Cryptol +
Isabelle](verifying-third-party-pqc-with-saw-and-isabelle.html). Everything reproduces from one command;
the repo is at [github.com/amarshat/pqc-assay](https://github.com/amarshat/pqc-assay).
