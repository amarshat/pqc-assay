# An AFP entry whose theorems cannot be delivered

`Number_Theoretic_Transform` (AFP) proves the number-theoretic transform correct and invertible:
`FNTT_correct`, `IFNTT_correct`, `FNTT_inv_IFNTT`, `IFNTT_inv_FNTT`. It is refereed, it builds, and
it has no proof holes.

**No consumer can instantiate it.** Every one of those theorems is stated in locale `ntt` (or a
descendant), and `interpretation` of `ntt` fails before any proof obligation is considered:

```
Duplicate fact declaration "q.omega_properties" vs. "q.omega_properties"
The above error(s) occurred while activating facts of locale instance
```

## Cause

- `Preliminary_Lemmas.thy:339,348` prove *lemmas* named `omega_properties` and `mu_properties`
  inside locale `preliminary`.
- `NTT.thy:16,17` name locale `ntt`'s *assumptions* `omega_properties` and `mu_properties`.

Inside the locale body the assumption shadows the inherited lemma harmlessly. On `interpretation`
both must be noted under one qualified name, and Isabelle refuses the duplicate. The fix is a
rename of the two assumptions, two lines.

## Reproducing

`Repro.thy` imports only the AFP entry and discharges the obligations with `sorry`, so the
assumptions cannot be the cause. It still fails.

```
isabelle build -d . -d <afp>/thys AfpNttRepro
```

## Why this is in external-corpus

This directory collects measurements of proofs we did not write. The point is not that the entry is
wrong; the mathematics is fine and the locale is satisfiable (we exhibit a model at the ML-DSA
parameters in `spec/isabelle/tier2/inv/Mldsa_Instance.thy`). The point is that a machine-checked,
refereed development can be simultaneously correct and **undeliverable**: its results cannot be
transported to any concrete object. Logical non-vacuity and usable non-vacuity are different
properties, and only the first is what a green build reports.

We hit this ourselves. `Mldsa_Instance.thy` states the model as the locale predicate rather than an
`interpretation`, and until a review pushed back we had recorded the wrong reason for that (a
locale diamond). The real reason is this bug.

Status: to be reported upstream to the entry's author and the AFP editors.
