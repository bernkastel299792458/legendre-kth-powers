"""Derive zfr_local_coarse.csv from zfr_local.csv: merge consecutive bands into bands of width ~5 with Z2 = max.
Valid because a zero-free region with a larger Z2 is weaker (it is implied by the finer statement)."""
import csv, os
from fractions import Fraction
here = os.path.dirname(os.path.abspath(__file__))
rows = list(csv.DictReader(open(os.path.join(here, 'zfr_local.csv'))))
assert all(r['status'] == 'proved' for r in rows)
out, cur = [], None
for r in rows:
    lo, hi, Z = Fraction(r['logt_lo']), Fraction(r['logt_hi']), Fraction(r['Z2'])
    if cur is None:
        cur = [lo, hi, Z, r['Z2']]
    elif hi - cur[0] <= 5:
        assert lo == cur[1]
        cur[1] = hi
        if Z > cur[2]:
            cur[2], cur[3] = Z, r['Z2']
    else:
        out.append(cur); cur = [lo, hi, Z, r['Z2']]
out.append(cur)
with open(os.path.join(here, 'zfr_local_coarse.csv'), 'w', newline='') as f:
    f.write("logt_lo,logt_hi,Z2,status,notes\n")
    for lo, hi, Z, Zs in out:
        f.write(f"{lo},{hi},{Zs},proved,implied by zfr_local.csv (max of Z2 over the merged bands)\n")
print(len(out), "coarse bands")
for lo, hi, Z, Zs in out: print(f"{float(lo):6.0f} {float(hi):6.0f} {Zs}")
