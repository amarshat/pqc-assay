#!/usr/bin/awk -f
# Count fault-map verdicts by fault class for v5.1.0 (shipped) and v4.3 at hqc-1.
# Usage: awk -f scripts/hqc_decaps_classes.awk proof/hqc-decaps/logs/sites.tsv
# Classes are ranges of site numbers, read from the descriptions in sites.tsv (column 13).
# Output per class and variant: sites, P1 broken, P2K fails, P3 fails, out-of-bounds (ERROR).
BEGIN { FS = "\t" }
function cls(v, n) {
  if (v == "shipped") {
    if (n <= 4)  return "1 XOF, key regeneration, parse"
    if (n <= 7)  return "2 decryption (skip, return value, store)"
    if (n == 8)  return "3 H"
    if (n == 12) return "4 J"
    if (n <= 11) return "5 G, re-encryption, salt copy"
    if (n <= 38) return "6 comparisons and masks"
    if (n <= 40) return "7 selection loop exit"
    return "8 selection body"
  }
  if (n <= 4)   return "1 XOF, key regeneration, parse"
  if (n <= 14)  return "9 added: complement of u, v"
  if (n <= 17)  return "2 decryption (skip, return value, store)"
  if (n == 18)  return "3 H"
  if (n <= 20)  return "4 J"
  if (n <= 33)  return "9 added: OR of the two J, start of K_theta_prime"
  if (n <= 36)  return "5 G, re-encryption, salt copy"
  if (n <= 91)  return "6 comparisons and masks"
  if (n <= 100) return "9 added: output prefill"
  if (n <= 102) return "7 selection loop exit"
  return "8 selection body"
}
NR > 1 && ($1 == "shipped" || $1 == "v4.3") {
  c = cls($1, substr($2, 2) + 0); k = $1 SUBSEP c; seen[c] = 1
  n[k]++; if ($4 == "BROKEN") b[k]++; if ($9 == "LEAK") l[k]++; if ($6 == "VIOLATED") x[k]++; if ($4 == "ERROR") e[k]++
}
END {
  for (c in seen)
    printf "%-52s shipped %3d %3d %3d %3d %d   v4.3 %3d %3d %3d %3d %d\n", c,
      n["shipped", c], b["shipped", c], l["shipped", c], x["shipped", c], e["shipped", c],
      n["v4.3", c], b["v4.3", c], l["v4.3", c], x["v4.3", c], e["v4.3", c] | "sort"
}
