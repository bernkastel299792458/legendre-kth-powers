"""
rza_thm11_ext.py -- exact (Arb) full sums S11(J), S12(J) for J = 2..JMAX (default 160), cached to
out/thm11_fullsums_ext.json; also prints the consistency check with Helfgott's limit
lim S_0(X) ~ 0.4407 (S_0(inf) = W (log 2 + S11(inf)), see REPORT).
Run: python -I rza_thm11_ext.py [JMAX]
"""
import os, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rza_common import *
from rza_thm11 import inner_full, w11, w12, r_q, t_q
HERE = os.path.dirname(os.path.abspath(__file__))
JMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 160
ctx.prec = 128
a11, a12 = arb(0), arb(0)
out = {}
for j in range(2, JMAX + 1):
    a11 += r_q(j) * (arb(j + 1) / j).log() * inner_full(j, w11)
    a12 += t_q(j) * (arb(j + 1).sqrt() + arb(j).sqrt()) * inner_full(j, w12)
    out[j] = [a11.mid().str(25, radius=False), a11.rad().str(3, radius=False),
              a12.mid().str(25, radius=False), a12.rad().str(3, radius=False)]
    if j in (22, 40, 61, 80, 100, 120, 140, 160, 200):
        print("J=%3d  S11=%s  S12=%s" % (j, a11.str(12), a12.str(10)), flush=True)
json.dump(out, open(os.path.join(HERE, "out", "thm11_fullsums_ext.json"), "w"), indent=0)
W = arb("0.42824950611918")
print("Helfgott: lim S0 in [0.4407 - 1e-4, 0.4408]  =>  S11(inf) = limS0/W - log 2 in",
      (arb("0.4406") / W - arb(2).log()).str(6), (arb("0.4408") / W - arb(2).log()).str(6))
print("with the paper's W = 0.40282372: S11(inf) would be",
      (arb("0.4407") / arb("0.40282372") - arb(2).log()).str(6))
