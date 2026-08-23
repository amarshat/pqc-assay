# AFP submission form: exactly what to paste

Form: <https://isa-afp.org/webapp/submit/>. Upload **either** `dist/MLDSA_Reduce.zip` **or**
`dist/MLDSA_Reduce.tar.gz`; both contain exactly the folder `MLDSA_Reduce/` with `ROOT`, both theory
files and `document/`, and nothing else.

AFP requires exactly one folder per entry, named the short name, with no hidden files or `__MACOSX`.
Both archives were checked against that and then extracted into a clean directory and built there, so
what a referee unpacks is known to build rather than assumed to:

| archive | sha256 | extracted build |
|---|---|---|
| `MLDSA_Reduce.zip` | `bc04807b…` | exit 0 with AFP's options |
| `MLDSA_Reduce.tar.gz` | `8d6e5137…` | exit 0 with AFP's options |

Regenerate both with `make afp-dist` and re-verify with `make afp-dist-verify`; the tar hash changes on
every rebuild because tar records timestamps, so treat the values above as identifying these files
rather than as fixed properties of the entry. They are built with `zip -X` and `COPYFILE_DISABLE=1 tar`
respectively, because macOS otherwise writes
`__MACOSX` and `._` entries from extended attributes, which the form rejects.

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
implementations used by PQClean's ML-DSA-44 clean code, which derives from the CRYSTALS-Dilithium
reference implementation, and proves that those implementations meet the specifications.</p>

<p>The arithmetic core is that if \(T \equiv A \cdot \mathit{QINV} \pmod{2^{32}}\), \(T\) lies in
the signed 32-bit range, and \(A\) lies in the half-open domain \(-2^{31}q \le A &lt; 2^{31}q\), then
\((A - Tq)/2^{32}\) is congruent to \(A \cdot 2^{-32}\) modulo \(q\) and lies strictly between
\(-q\) and \(q\). The bound on \(A\) is not optional: without it the conclusion fails.</p>

<p>Two specifications depart deliberately from what the implementation's comments document, because
those comments are off by one at an endpoint. Montgomery reduction is specified on a half-open input
domain, since the inclusive upper endpoint returns exactly \(q\) and so violates the documented strict
output bound; and <code>reduce32</code> is specified on its true reachable output window, which is
asymmetric rather than the symmetric one documented. That window is exact rather than a safe
over-approximation: both endpoints are attained, and the witnesses are proved, the lower one being the
value the documented window excludes.</p>

<p>The entry concerns the reduction layer only, and relates the definitions to the specifications and
nothing else. The definitions are written so that a reader can compare them with the implementation
being modelled, but the entry makes no claim that any compiled binary computes them.</p>
```

**Use of generative AI** , the form asks directly, and leaving it empty would be a false statement here.
Paste:

```
The theories were developed with substantial assistance from an AI coding assistant (Claude). It
produced initial versions of the definitions and proofs, and carried an earlier version of this
development from a machine-generated Cryptol lift into the standalone form submitted here. Every
theorem is checked by Isabelle, and the entry uses no oracles. The author reviewed the definitions
against FIPS 204 and against the PQClean implementation they model, and is responsible for the entry
and for maintaining it.
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

## If this is a resubmission

The first submission was **2026-08-23_16-48-34_388**. Everything below changed after it and before any
referee saw the entry. No proof became weaker; two claims that were prose are now theorems.

1. **`mldsa_reduce32_input_ok` is two-sided.** It recorded only the upper bound and relied on callers
   being 32-bit words for the lower one, so read as an integer-level predicate it did not characterise
   the domain: `reduce32(-10^10) = -10542936`, outside the specified window, and `-10^10` satisfied the
   old predicate.
2. **Provenance corrected.** The entry called PQClean's copy byte-identical to CRYSTALS-Dilithium apart
   from symbol prefixes. It is not: PQClean writes the Montgomery step as
   `(int32_t)((uint64_t)a * (uint64_t)QINV)`, upstream as `(int64_t)(int32_t)a*QINV`. They agree on the
   low 32 bits. The entry now cites PQClean at commit 202a8f9 as the code modelled and states the
   relationship.
3. **Both corrected contracts now rest on checked witnesses.** `reduce32`'s window endpoints are proved
   attained, and the Montgomery endpoint that motivates the half-open domain is proved to return
   exactly `q`, so the documented strict bound demonstrably fails there.
4. **The signed-shift assumption is stated.** C leaves `>>` on negative signed operands
   implementation-defined; the models take the arithmetic reading, and the entry now says so instead of
   leaving it implicit.
5. **Wording tightened.** The entry defines *models of* PQClean's routines rather than "the
   implementations used by" it, and no longer says anything about "deployed implementations" as a class.

## Before you press submit

Run `scripts/afp-check.sh` one more time and confirm `afp-check OK`. The build it runs is the one AFP
uses:

    isabelle build -v -o browser_info -o "document=pdf" \
      -o "document_variants=document:outline=/proof,/ML" -d afp/MLDSA_Reduce -d <afp>/thys -c MLDSA_Reduce

Last verified 2026-08-23: exit 0, theories 6 s, document 2 s, on Isabelle2025-2 with AFP 2026-06-05.
