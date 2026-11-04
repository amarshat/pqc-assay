#!/usr/bin/env python3
"""Judge the native replay runs (scripts/hqc_decaps51_replay.sh). Per build and skip:
  valid    the honest ciphertexts of both key pairs still yield the encapsulated key;
  P1       on how many of the 8 (key, ciphertext) cases that the unfaulted build rejects (each key's
           own ciphertext with one bit of v flipped, the other key's, the zero and a random
           ciphertext) the output equals the unfaulted rejection key;
  bytes    how many of the 32 output bytes equal the unfaulted rejection key (min over the two);
  pubJ     on how many of the 8 (key, rejected ciphertext) cases the output equals J(H(ek), 0, c),
           which needs no secret;
  samekey  on the zero and the random ciphertext, whether both key pairs give the same output,
           in which case the output does not depend on the key at all.
"""
import sys

runs, cur = {}, None
for line in open(sys.argv[1]):
    line = line.rstrip("\n")
    if line.startswith("== "):
        cur = tuple(line[3:].split()); runs[cur] = {}
    elif line.startswith("!!"):
        runs[cur]["exit"] = line
    elif cur and line:
        label, h = line.rsplit(" ", 1)
        runs[cur][" ".join(label.split())] = h

own = {0: "flip", 1: "flip2"}
print(f"{'build':8} {'skip':6} {'valid':6} {'P1':5} {'bytes':5} {'pubJ':5} samekey")
for (t, k), r in runs.items():
    if "exit" in r:
        print(f"{t:8} {k:6} {r['exit']}"); continue
    ref = runs[(t, "none")]
    valid = all(r[f"key{p} valid out"] == r[f"key{p} valid K"] for p in (0, 1))
    nb = min(sum(a == b for a, b in zip(bytes.fromhex(r[f"key{p} {own[p]} out"]),
                                       bytes.fromhex(ref[f"key{p} {own[p]} out"]))) for p in (0, 1))
    rej = [(p, c) for p in (0, 1) for c in ("flip", "zero", "rand", "flip2")
           if ref[f"key{p} {c} out"] != ref.get(f"key{p} valid K")]
    p1 = sum(r[f"key{p} {c} out"] == ref[f"key{p} {c} out"] for p, c in rej)
    pubj = sum(r[f"key{p} {c} out"] == r[f"key{p} {c} pubJ"] for p, c in rej)
    same = all(r[f"key0 {c} out"] == r[f"key1 {c} out"] for c in ("zero", "rand"))
    print(f"{t:8} {k:6} {str(valid):6} {f"{p1}/{len(rej)}":5} {nb:5} {pubj}/{len(rej):<3} {same}")
