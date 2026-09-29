# A patch offered to AFP `CRYSTALS-Kyber`

`Kyber_Psi_Derived.thy` shows that one of `kyber_ntt`'s assumptions is redundant.

`NTT_Scheme.thy:28` reads

```isabelle
and psi_properties: "\<psi>^2 = \<omega>" "\<psi>^n = -1"
```

and the second conjunct follows from the first together with `omega_properties` and
`n = 2^n'`, `n' > 0`.

**What dropping it actually costs, measured rather than assumed.** It is not a one-line deletion.
Removing the conjunct from the locale requires two further changes, which we found by doing it:

1. `NTT_Scheme.thy:56` is the single place inside the entry that cites `psi_properties(2)`. It must
   be redirected to the derived lemma. (`psi_properties` has 1 declaration and 9 references; the
   other eight are to conjunct 1 or unqualified.)
2. `Kyber_NTT_Values.thy` discharges the locale's obligations **by goal number** (`case 4`, `6`,
   `7`, `9`, `11`, `15`, `17`). Removing a conjunct shifts every later goal: `case 15`, which is
   `psi^n = -1` discharged by `powr256'`, disappears, and `case 17` becomes `16`. Left unchanged,
   the build fails with `powr256'` applied to `psi * psiinv = 1`.

We verified 1 and 2 individually against a patched copy. We did **not** get a fully building
CRYSTALS-Kyber with the conjunct removed end to end, so treat the integration as scoped rather than
done. The derivation itself is verified, standalone, below.

## How it is stated, and why that matters

The derivation is a **standalone lemma over an arbitrary field**, not a lemma inside `kyber_ntt`.
Proved inside the locale it would establish nothing, because the locale assumes the conclusion, and
a derivation permitted to use the fact it derives is not a derivation. The corollary
`psi_pow_n_recovered` then instantiates the standalone lemma at the locale's parameters, citing
only `psi_properties(1)`, `omega_properties(1)`, `omega_properties(3)`, `n_gt_1`, and evenness
of `n` (the last two both from `n_powr_2` with `n'_gr_0`).

Checked that the hypotheses are load-bearing. Evenness is not merely used but semantically
necessary: with `\<omega> = 684` (order 3 mod 7681) and `\<psi> = 684^2`, every other hypothesis
holds at m = 3 and `\<psi>^3 = 1`, not `-1`. No `sorry`, `oops` or `by eval`.

## Building

```
isabelle build -d <afp>/thys -d . KyberPatch
```

Exits 0 against AFP 2026-06-05 / Isabelle2025-2, in about one second on a warm `CRYSTALS-Kyber`
heap.

## Honest status

Verified: the derivation, standalone, with load-bearing hypotheses. Scoped and individually
checked: the two integration changes above. Not done: a complete patched entry that builds.

## Still to do

The second half of the offer, replacing `Powers3844.thy:13`'s 255-power `by eval` with the
two-fact order argument (the order divides `n` because `omega^n = 1`, and does not divide `n/2`
because `omega^(n div 2) = -1`), is **not** in this directory yet. We have that argument proven at
our own parameters in `spec/isabelle/tier2/inv/Mldsa_Instance.thy` as `w_order_minimal`, and it
needs restating for 7681 and 3329.
