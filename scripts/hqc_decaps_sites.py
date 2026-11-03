#!/usr/bin/env python3
"""Join the per-site verdict files of the v5.1.0 hqc-1 fault maps into one table and check them.

Reads build/hqc-decaps51/faults_1<tag>/{MANIFEST,RESULTS,PRES,NI,NIK,NIT,FIRED,NIFIRED*}.tsv for the
shipped code and v4, v4.1, v4.2, v4.3 (written by scripts/hqc_decaps_faults.py and the runners), and
writes one row per site: variant, site, fault kind, description, and the verdict of every check run
on it. Then checks, per variant, that

  - every site in MANIFEST has a P1 verdict, and no verdict file names a site MANIFEST lacks;
  - P3 was run exactly on the P1 failures that are not memory errors or timeouts;
  - P2 was run on exactly the P1 failures, P2K and P2theta on exactly the sites where P2 fails or
    times out;
  - the P1 fired check was run on exactly the P1-resilient sites, and each says FIRES;
  - the two-run fired check for each property was run on exactly the sites where that property
    holds, and each says FIRES.

Any failed check is printed and the exit status is 1. Usage:
  scripts/hqc_decaps_sites.py [build/hqc-decaps51] > proof/hqc-decaps/logs/sites.tsv
The summary goes to stderr.
"""
import os
import sys

VARIANTS = [("shipped", ""), ("v4", "_v4"), ("v4.1", "_v41"), ("v4.2", "_v42"), ("v4.3", "_v43")]
# two-run property -> (verdict file, fired file)
TWO_RUN = [("P2", "NI", "NIFIRED2"), ("P2K", "NIK", "NIFIREDK"), ("P2T", "NIT", "NIFIREDT")]


def read(path, ncol=2):
    rows = {}
    if not os.path.exists(path):
        return rows
    with open(path) as f:
        for line in f:
            line = line.rstrip("\n")
            if not line:
                continue
            parts = line.split("\t")
            rows[parts[0]] = parts[1:] if ncol > 2 else parts[1]
    return rows


def main():
    base = sys.argv[1] if len(sys.argv) > 1 else "build/hqc-decaps51"
    bad = []
    cols = ["variant", "site", "kind", "P1", "P1fired", "P3", "P2", "P2fired", "P2K", "P2Kfired",
            "P2T", "P2Tfired", "description"]
    print("\t".join(cols))
    totals = {"fired": 0, "nifired_pairs": 0, "nifired_sites": 0}
    for name, tag in VARIANTS:
        d = os.path.join(base, "faults_1" + tag)
        man = read(os.path.join(d, "MANIFEST.tsv"), 3)
        res = read(os.path.join(d, "RESULTS.tsv"), 3)
        pres = read(os.path.join(d, "PRES.tsv"))
        fired = read(os.path.join(d, "FIRED.tsv"))
        two = {p: (read(os.path.join(d, v + ".tsv")), read(os.path.join(d, fz + ".tsv")))
               for p, v, fz in TWO_RUN}

        def check(cond, msg):
            if not cond:
                bad.append(f"{name}: {msg}")

        p1 = {s: r[0] for s, r in res.items()}
        sites = sorted(man)
        check(set(p1) == set(man), f"P1 verdicts {len(p1)} vs manifest {len(man)}")
        for fname, rows in [("PRES", pres), ("FIRED", fired)] + \
                [(v, two[p][0]) for p, v, _ in TWO_RUN] + [(fz, two[p][1]) for p, _, fz in TWO_RUN]:
            extra = set(rows) - set(man)
            check(not extra, f"{fname} names sites not in MANIFEST: {sorted(extra)}")
        resilient = {s for s, v in p1.items() if v == "RESILIENT"}
        broken = {s for s, v in p1.items() if v == "BROKEN"}
        check(set(pres) == broken, f"P3 run on {len(pres)} sites, P1 BROKEN at {len(broken)}")
        check(set(two["P2"][0]) == broken, f"P2 run on {len(two['P2'][0])}, P1 BROKEN at {len(broken)}")
        p2fail = {s for s, v in two["P2"][0].items() if v in ("LEAK", "TIMEOUT")}
        for p in ("P2K", "P2T"):
            check(set(two[p][0]) == p2fail, f"{p} run on {len(two[p][0])} sites, P2 fails at {len(p2fail)}")
        check(set(fired) == resilient, f"P1 fired on {len(fired)} sites, RESILIENT {len(resilient)}")
        check(all(v == "FIRES" for v in fired.values()), "a P1 fired check did not say FIRES")
        pairs, nsites = 0, set()
        for p, _, _ in TWO_RUN:
            holds = {s for s, v in two[p][0].items() if v == "NONINTERFERENT"}
            fz = two[p][1]
            check(set(fz) == holds, f"{p} fired on {sorted(fz)} but holds at {sorted(holds)}")
            check(all(v == "FIRES" for v in fz.values()), f"a {p} fired check did not say FIRES")
            pairs += len(fz)
            nsites |= set(fz)
        totals["fired"] += len(fired)
        totals["nifired_pairs"] += pairs
        totals["nifired_sites"] += len(nsites)

        for s in sites:
            raw, desc = man[s][0], man[s][1] if len(man[s]) > 1 else ""
            row = [name, s, desc.split(" ")[0], p1.get(s, "-"), fired.get(s, "-"), pres.get(s, "-")]
            for p, _, _ in TWO_RUN:
                row += [two[p][0].get(s, "-"), two[p][1].get(s, "-")]
            row.append(desc)
            print("\t".join(row))

        count = lambda m, v: sum(1 for x in m.values() if x == v)
        n2 = {p: count(two[p][0], "NONINTERFERENT") for p, _, _ in TWO_RUN}
        print(f"{name:8} sites {len(man):3}  P1 {len(resilient):3}  P1-fail {len(broken):3} "
              f"(P3 {count(pres, 'PRESERVED'):2} held, {count(pres, 'VIOLATED'):2} violated)  "
              f"error {count(p1, 'ERROR')}  timeout {count(p1, 'TIMEOUT')}  "
              f"P2 {n2['P2']:2} P2K {n2['P2K']} P2T {n2['P2T']:2} P2K-fail {count(two['P2K'][0], 'LEAK'):2}  "
              f"fired {len(fired):3}  two-run fired {pairs:2} checks at {len(nsites):2} sites",
              file=sys.stderr)
        errkinds = sorted({man[s][1].split(" ")[0] for s, v in p1.items() if v in ("ERROR", "TIMEOUT")})
        print(f"{'':8} ERROR/TIMEOUT sites are of kind {errkinds}", file=sys.stderr)
    print(f"total    P1 fired {totals['fired']}  two-run fired {totals['nifired_pairs']} checks at "
          f"{totals['nifired_sites']} sites", file=sys.stderr)
    for b in bad:
        print("CHECK FAILED: " + b, file=sys.stderr)
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
