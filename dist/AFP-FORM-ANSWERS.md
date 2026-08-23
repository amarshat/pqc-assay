# AFP submission form: exactly what to paste

Form: <https://isa-afp.org/webapp/submit/>. Upload `dist/MLDSA_Reduce.tar.gz`, which contains the
folder `MLDSA_Reduce/` with `ROOT`, both theory files and `document/`.

---

## Entry

**Title of article**

    The Modular-Reduction Layer of ML-DSA

**Short name** (must match the folder in the archive)

    MLDSA_Reduce

**Topics** (both from the AFP's controlled list)

    Computer science/Security/Cryptography
    Computer science/Algorithms/Mathematical

**License**

    BSD

(No per-file header needed. Only LGPL requires a `License: LGPL` line in each file.)

**Abstract** — the form takes HTML and MathJax, *not* LaTeX. Paste exactly this:

```html
<p>FIPS 204 fixes the prime modulus \(q = 8380417\) for ML-DSA. Deployed implementations reduce values
modulo \(q\) with a small layer of routines that the standard does not itself spell out: Montgomery
reduction, a Barrett-style <code>reduce32</code>, a conditional addition, and their composition. This
entry specifies what each routine must satisfy at the integer level, defines the fixed-width
implementations used by the reference implementation, and proves that those implementations meet the
specifications.</p>

<p>The arithmetic core is that if \(T \equiv A \cdot \mathit{QINV} \pmod{2^{32}}\), \(T\) lies in
the signed 32-bit range, and \(A\) lies in the half-open domain \(-2^{31}q \le A &lt; 2^{31}q\), then
\((A - Tq)/2^{32}\) is congruent to \(A \cdot 2^{-32}\) modulo \(q\) and lies strictly between
\(-q\) and \(q\). The bound on \(A\) is not optional: without it the conclusion fails.</p>

<p>Two specifications depart deliberately from what the reference implementation documents, because its
comments are off by one at an endpoint. Montgomery reduction is specified on a half-open input domain,
since the inclusive upper endpoint returns exactly \(q\) and so violates the documented strict output
bound; and <code>reduce32</code> is specified on its true reachable output window, which is asymmetric
rather than the symmetric one documented. Each departure is set out in the theory text where it
occurs.</p>

<p>The entry concerns the reduction layer only, and relates the definitions to the specifications and
nothing else. The definitions are written so that a reader can compare them with the reference
implementation, but the entry makes no claim that any compiled binary computes them.</p>
```

**Use of generative AI** — the form asks directly, and leaving it empty would be a false statement here.
Paste:

```
The theories were developed with substantial assistance from an AI coding assistant (Claude), which
produced initial versions of the definitions and proofs and carried an earlier version of this
development across from a machine-generated Cryptol lift to the standalone form submitted here. Every
theorem was checked by Isabelle, and the entry was additionally checked negatively: introducing a false
conjunct into the Montgomery theorem, and substituting the output window that the reference
implementation's own comment documents, each make the build fail. The entry was also refereed before submission by a
separate AI agent working from the AFP submission rules, which mutation-tested the theorems and
differentially tested the definitions against the vendored reference C, and whose findings were fixed.
The author reviewed the definitions against FIPS 204 and the reference implementation and is
responsible for the entry and its maintenance.
```

---

## Authors

New author, so register first under **New Authors**:

    Name:  Amar Akshat
    ORCID: (optional, leave empty unless you have one)

**New email**

    amar.akshat@gmail.com

Then add `Amar Akshat` as the author of the entry, and the same address under **Contact**.

---

## Related Publications

Leave empty for now, or add the FIPS 204 DOI as background literature:

    10.6028/NIST.FIPS.204

If the methods paper is published later, the editors can add it to the entry's history.

---

## Before you press submit

Run `scripts/afp-check.sh` one more time and confirm `afp-check OK`. The build it runs is the one AFP
uses:

    isabelle build -v -o browser_info -o "document=pdf" \
      -o "document_variants=document:outline=/proof,/ML" -d afp/MLDSA_Reduce -d <afp>/thys -c MLDSA_Reduce

Last verified 2026-08-23: exit 0, theories 6 s, document 2 s, on Isabelle2025-2 with AFP 2026-06-05.
