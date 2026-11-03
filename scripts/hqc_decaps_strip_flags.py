"""hqc_kem_decaps_internal with nsw/nuw dropped in the fault region exactly as hqc_decaps_faults.py
drops them, and no fault injected (make hqc-decaps51-faultctl). Usage: <in.ll> <out.ll>."""
import re, sys
sys.path.insert(0, 'scripts')
import hqc_decaps_faults as F
src, out = sys.argv[1], sys.argv[2]
L = open(src).read().split('\n')
fstart = next(i for i,l in enumerate(L) if l.startswith('define') and '@hqc_kem_decaps_internal(' in l)
s, e = F.region(L, fstart, 'AFTER_INIT:@xof_init_dom_sep(')
n = 0
for j in range(s, e):
    if not L[j].lstrip().startswith(('call', 'store')) and 'getelementptr' not in L[j]:
        new = re.sub(r' (nsw|nuw)\b', '', L[j]); n += new != L[j]; L[j] = new
open(out, 'w').write('\n'.join(L)); print(out, n, 'lines changed')
