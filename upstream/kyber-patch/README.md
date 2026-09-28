# A patch offered to AFP `CRYSTALS-Kyber`

`Kyber_Psi_Derived.thy` shows that one of `kyber_ntt`'s assumptions is redundant.

`NTT_Scheme.thy:28` reads

```isabelle
and psi_properties: "\<psi>^2 = \<omega>" "\<psi>^n = -1"
```

and the second conjunct follows from the first together with `omega_properties` and
`n = 2^n'`, `n' > 0`. So `kyber_ntt` can drop it, and every instantiation of the locale has one
fewer obligation to discharge.

## How it is stated, and why that matters

The derivation is a **standalone lemma over an arbitrary field**, not a lemma inside `kyber_ntt`.
Proved inside the locale it would establish nothing, because the locale assumes the conclusion, and
a derivation permitted to use the fact it derives is not a derivation. The corollary
`psi_pow_n_recovered` then instantiates the standalone lemma at the locale's parameters, citing
only `psi_properties(1)`, `omega_properties(1)`, `omega_properties(3)` and evenness of `n`.

Checked that the hypotheses are load-bearing: deleting the evenness hypothesis makes the build
fail. No `sorry`, `oops` or `by eval`.

## Building

```
isabelle build -d <afp>/thys -d . KyberPatch
```

Exits 0 against AFP 2026-06-05 / Isabelle2025-2, in about one second on a warm `CRYSTALS-Kyber`
heap.

## Still to do

The second half of the offer, replacing `Powers3844.thy:13`'s 255-power `by eval` with the
two-fact order argument (the order divides `n` because `omega^n = 1`, and does not divide `n/2`
because `omega^(n div 2) = -1`), is **not** in this directory yet. We have that argument proven at
our own parameters in `spec/isabelle/tier2/inv/Mldsa_Instance.thy` as `w_order_minimal`, and it
needs restating for 7681 and 3329.
