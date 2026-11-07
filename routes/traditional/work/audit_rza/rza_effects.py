"""
rza_effects.py -- effect of each correction, one at a time, on the 0.5936 row
(10^12 <= X < 10^16, eps <= 1/25) of RZA v3 Thm 1.2, inside the paper's own (flawed) chain.
Run: python -I rza_effects.py
"""
import os, sys, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rza_common import *
from rza_assembly import assemble, PAPER
from rza_audited import build, best_R
inp_aud, o_aud, th, status, Kc = build(False)
T, T0, S = "1e12", "1e16", 25
def val(inp, R=112):
    o = assemble(inp)
    v = o["Omega1"](R, T, T0).max(o["Omega2"](R, S, T, T0))
    Rb, vb = best_R(o, T, T0, S, lo=60, hi=400)
    return v, Rb, vb, o
base, _, baseb, ob = val(PAPER)
print("paper inputs: R=112 %s ; best R %s" % (show(base, 8), show(baseb, 8)))
cases = {
  "W (APROD) true, Theta(1e12) recomputed": dict(THETA={("1e12", "1e16"): th[("1e12", "1e16")][1]}, APROD=inp_aud["APROD"]),
  "c1 true (P0_LX)": dict(P0_LX=inp_aud["P0_LX"], P0_two_sided_tail=True),
  "log2mx/log2mm true": dict(log2mx=inp_aud["log2mx"], log2mm=inp_aud["log2mm"]),
  "logmx/logmm ours": dict(logmx=inp_aud["logmx"], logmm=inp_aud["logmm"]),
  "Euler products Arb (others)": {k: inp_aud[k] for k in ("P1_M","P1_delta2_M","P2","P2_delta","P3","P3_spec","P1x","P1x_delta","P1_LX","AP0_LX","AP1_LX","PPdelta","Sumx_p3","ASumx_p3")},
  "scans ours (Fmx*, mx*)": {k: inp_aud[k] for k in ("Fmx1","Fmx2","mx1","mx2","mx3","mxxx_aux11","mx_aux11")},
  "K_b in proof form": dict(Kb_proof_form=True),
}
for name, ch in cases.items():
    inp = dict(PAPER); inp.update(ch)
    v, Rb, vb, o = val(inp)
    print("  %-42s R=112: %s (%+.2e)   best R=%d: %s" % (name, show(v, 8), float((v - base).mid()), Rb, show(vb, 8)))
o = assemble(dict(PAPER, Kb_proof_form=True))
print("K_b: paper code %s, proof form %s" % (show(ob["K_b"], 8), show(o["K_b"], 8)))
