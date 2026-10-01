# Merge-request-ready patch for the AFP `ntt` interpretation bug

`ntt-rename.patch` is the fix described in `~/Documents/assay-private/upstream/1-afp-ntt-bug.md`,
as a reviewable diff against AFP 2026-06-05.

```
patch -p1 < ntt-rename.patch
```

62 changed lines, nothing but the rename:

| file | lines |
|---|---|
| `Number_Theoretic_Transform/NTT.thy` | 48 |
| `Number_Theoretic_Transform/Butterfly.thy` | 12 |
| `CRYSTALS-Kyber/NTT_Scheme.thy` | 2 |

Renames locale `ntt`'s assumptions `omega_properties`/`mu_properties` to `omega_props`/`mu_props`,
so they no longer collide with the same-named lemmas `preliminary` proves, and updates every use.

Two things the patch gets right that a naive `sed` does not:

- `NTT.thy:20`'s `mu_properties'` is a **different lemma** and is left alone.
- `CRYSTALS-Kyber/NTT_Scheme.thy:972` cites `kyber_ntt.omega_properties(1)`. Without updating it the
  name still resolves, to the locale-predicate form rather than the assumption, and the `smt` call
  there fails on a goal that looks unrelated to the cause. Those are the 2 lines in the third file.

## Tested

Applied to a pristine AFP 2026-06-05 checkout with `patch -p1`, applies clean, then:

```
isabelle build Number_Theoretic_Transform   exit 0
isabelle build CRYSTALS-Kyber               exit 0
```

And the reproducer that motivated it (a global `interpretation` of `ntt` in a fresh theory,
obligations `sorry`-ed under `quick_and_dirty`) fails before the patch and succeeds after.

## Why file this as well as emailing

An email can be ignored; a merge request sits in a queue and is visible to all the editors. Needs a
Heptapod account at <https://foss.heptapod.net/isa-afp/>.
