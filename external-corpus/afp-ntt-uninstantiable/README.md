# AFP `Number_Theoretic_Transform`: global `interpretation` fails

**Scope corrected 2026-09-28.** An earlier version of this file claimed the entry's theorems
"cannot be delivered" to any concrete object. That was wrong. AFP `CRYSTALS-Kyber` interprets this
very locale at `NTT_Scheme.thy:176`, inside a locale context, and it works. What is actually broken
is one of four usage routes.

| usage | result |
|---|---|
| global `interpretation` in a fresh theory | **fails**, duplicate fact declaration |
| `interpretation` inside a locale context | works |
| proof-local `interpret` | works |
| `thm [OF locale_predicate]` | works |

## The failure

```
Duplicate fact declaration "q.omega_properties" vs. "q.omega_properties"
The above error(s) occurred while activating facts of locale instance
```

`Repro.thy` imports only the AFP entry and discharges the obligations with `sorry`, so the
assumptions cannot be the cause. It still fails.

```
isabelle build -d . -d <afp>/thys AfpNttRepro
```

## Cause

- `Preliminary_Lemmas.thy:339,348` prove *lemmas* `omega_properties` and `mu_properties` in locale
  `preliminary`.
- `NTT.thy:16,17` name locale `ntt`'s *assumptions* the same.

Harmless inside the locale, where the assumption shadows the inherited lemma. Fatal on a global
interpretation, where both must be recorded under one qualified name. Interpreting `preliminary`
alone succeeds; `ntt` and `butterfly` fail.

The fix is a rename of `ntt`'s two assumptions. Applied to a copy and measured: 2 declarations plus
37 internal references. With it, the same reproducer succeeds and the renamed entry still builds.
An earlier version of this file called it "two lines", which was a guess and understated it by an
order of magnitude.

## Why it is kept here

Not as a vacuity finding, which is what we first wrote. As a record of a claim of ours that was
wrong twice: first we blamed an inheritance diamond (refuted by interpreting a child with no
diamond), then we claimed undeliverability (refuted by a file in the same archive). The second
survived into a paper section, an abstract and a commit.

The check that would have caught it costs nothing: before asserting that something cannot be done,
grep the corpus for somebody doing it.

Reported upstream.
