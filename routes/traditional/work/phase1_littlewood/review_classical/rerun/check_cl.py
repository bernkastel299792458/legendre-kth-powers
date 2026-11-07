"""Hypotheses and constants of the local classical region (REPORT.md §12): every lemma of BTY whose constants depend on
the parameters (eta0, sigma0, U_CUT) is re-checked here for OUR parameters, and the error constants of the per-cell
inequality are computed.  Writes cl_constants.json (read by cl_core.py).

Run:  python -I check_cl.py > check_cl_output.txt      (a few minutes)
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import json
from fractions import Fraction as Q
from flint import arb, acb, arb_series
import cl_core as C
import polyq as P

NF = 0


def check(name, ok, detail=""):
    global NF
    tag = {True: "OK", False: "FAIL", None: "INFO"}[ok]
    if ok is False:
        NF += 1
    print(f"[{tag:4}] {name}" + (f"  --  {detail}" if detail else ""), flush=True)


def ball(lo, hi):
    lo, hi = arb(lo), arb(hi)
    return arb(((lo + hi) / 2).mid(), ((hi - lo) / 2).upper())


def s(x, n=10):
    return x.str(n, radius=False)


W0, ETA0, SIG0, TWO = C.W0, C.ETA0, C.SIGMA0, C.TWO_S0
kap = [C.KAP[m] for m in range(C.M + 1)]
check("parameters", None, f"Z_MIN = {C.Z_MIN.str(6)}, eta0 = {s(ETA0)}, sigma0 = {s(SIG0)}, 2 sigma0 - 1 = {s(TWO)}, "
      f"U_CUT = {C.U_CUT}, theta = 1.1338")
check("w(0): definition = closed form = 5.67278759...", (C.w(arb(0)) - W0).contains(0) and abs(W0 - arb('5.6727875985')) < arb('1e-9'), s(W0, 12))
check("a kappa w(0)/2 = KC", None, s(C.KC, 12))

# ---------------------------------------------------------------- w: boundary conditions, w >= 0, w' <= 0
def wd(k, lo, hi):
    c = C.w(arb_series([ball(lo, hi), 1], prec=k + 1)).coeffs()
    f = 1
    for j in range(1, k + 1):
        f *= j
    return c[k] * f


s0c = C.w(arb_series([arb(0), 1], prec=4)).coeffs()
sdc = C.w(arb_series([C.D_SUPP, 1], prec=4)).coeffs()
check("w'(0) = w(d) = w'(d) = w''(d) = 0 (Kadiri Prop. 2.1 hypotheses)",
      s0c[1].contains(0) and sdc[0].contains(0) and sdc[1].contains(0) and sdc[2].contains(0))


def cover(pred, lo, hi, n):
    lo, hi = arb(lo), arb(hi)
    st = (hi - lo) / n
    return all(pred(lo + i * st, lo + (i + 1) * st) for i in range(n))


a_, b_ = arb('0.2'), C.D_SUPP - arb('0.2')
okw = (cover(lambda l, h: wd(2, l, h).upper() < 0, 0, a_, 400) and cover(lambda l, h: wd(1, l, h).upper() < 0, a_, b_, 2000)
       and cover(lambda l, h: wd(3, l, h).upper() < 0, b_, C.D_SUPP, 400))
check("w'' < 0 on [0,0.2], w' < 0 on [0.2,d-0.2], w''' < 0 on [d-0.2,d]  =>  w decreasing, 0 <= w <= w(0)", okw)

# ---------------------------------------------------------------- Lemma 3
p = list(C.KAPPA)
check("Lemma 3: sum kappa_m x^m > 0 on [0,1] (Sturm, exact)", P.count_roots(p, Q(0), Q(1)) == 0 and P.ev(p, Q(0)) > 0)

# ---------------------------------------------------------------- Lemma 5 (21) with our sigma0, eta0
r5 = TWO / ETA0
C5 = C.C_ford(r5, r5)
val5 = ETA0 ** 2 * C5 / (TWO ** 2 * W0)
eps0 = None
for e in [Q(1, 2000), Q(11, 20000), Q(3, 5000), Q(13, 20000), Q(7, 10000)]:
    if val5.upper() < arb(e.numerator) / e.denominator:
        eps0 = e
        break
check("Lemma 5: eta0^2 C(r,r)/((2 sigma0-1)^2 w(0)) < eps0, r = (2 sigma0-1)/eta0", eps0 is not None,
      f"value {s(val5, 6)}, r = {s(r5, 6)}, eps0 = {eps0}")
import math
c0q = Q(1)   # exact scaling: sum_m c_m/(d^2 m^2 + y^2) = d^-2 sum_m c_m/(m^2 + (y/d)^2), d = 2 sigma - 1
check("Lemma 5: with delta_m = d m for ONE d = 2 sigma - 1, B(y) = d^-2 Btilde(y/d); BTY's split c0 m <= delta_m <= m is "
      "not needed, so c0 = 1 below", None)
b = P.mul([Q(1), Q(1)], list(C.KAPPA))
dens, nums = [], []
for m in range(1, C.M + 2):
    if b[m] > 0:
        dens.append([Q(m * m), Q(1)])
        nums.append(b[m] * (m - eps0 / m))
    else:
        dens.append([c0q ** 2 * m * m, Q(1)])
        nums.append(b[m] * (m + eps0 / m))
N = []
for i in range(len(dens)):
    term = [nums[i]]
    for j in range(len(dens)):
        if j != i:
            term = P.mul(term, dens[j])
    N = P.add(N, term)
nr = P.count_roots(N, Q(0), "+inf")
check("Lemma 5: B(y) = N(y^2)/prod(...) with these eps0, c0 has N > 0 on [0, inf) (Sturm)  =>  (21)",
      nr == 0 and P.ev(N, Q(0)) > 0, f"#roots = {nr}, N(0) = {float(P.ev(N, Q(0))):.4e}")
sum_mb = sum(m * b[m] for m in range(len(b)))
check("Lemma 5, |Im z| -> inf: coefficient sum m b_m = 1/859 > 0 (corrected argument, audit I3)", sum_mb == Q(1, 859))
c57 = W0 + (C.C_ford(-1, C.T0 / ETA0) + C.C_ford(0, C.T0 / ETA0)) / C.T0 * ETA0 ** 2
check("Lemma 5 (22): w(0) + (C(-1,T0/eta0)+C(0,T0/eta0)) eta0^2/T0 < 5.7 and 2*5.7*sum|kappa| < 44",
      c57 < arb('5.7') and 2 * arb('5.7') * C.KAPA < 44, s(c57, 8))

# ---------------------------------------------------------------- Lemma 6 (far zeros), eta <= A0/log t with A0 = (1+2eps) A_MAX
A0p = (1 + 2 * C.EPS) * C.A_MAX
H, T0, Kq = C.H, C.T0, arb(C.K)
v6 = 88 * ETA0 * T0.log() / T0
excess = T0 / (Kq * H) + (Kq / (2 * C.PI)).log() + (((H + T0) / (2 * C.PI)).log() / (2 * H + T0) + (2 * H + T0).log() / H) * T0
B27 = lambda L: (L + excess) / T0
B28 = lambda L: (1 / T0 ** 2 + 1 / (2 * H + T0) ** 2) * (L + Kq.log() + T0 / (Kq * H))
B29 = 1 / (2 * T0 ** 2) + 1 / ((2 * H) ** 2 * T0)
L = C.LOGH
v6k = 44 * (A0p / L) * (B27(L) / (2 * C.PI) + 4 * B28(L) + 2 * B29)
check("Lemma 6: k = 0: 88 eta0 log T0/T0 < 1e-8; k != 0: 44 eta [B27/2pi + 4 B28 + 2 B29] < 1e-8 (worst t = H, "
      "eta (log t + c) decreasing); sum_k a_k 1e-8 < 1e-7", v6 < arb('1e-8') and v6k < arb('1e-8') and sum(C.A_K) * arb('1e-8') < arb('1e-7'),
      f"{s(v6, 4)}, {s(v6k, 4)}")

# ---------------------------------------------------------------- Lemma 13 (pole terms)
C13 = C.C_ford(-1, arb('1e10'))
v13 = W0 * C.M / H ** 2 + C13 / H ** 3
check("Lemma 13: H/eta0 > 1e10, C(-1,1e10) w(0)M/H^2 + C/H^3 < 1e-12, a sum|kappa| 1e-12 < 1e-10",
      H / ETA0 > arb('1e10') and v13 < arb('1e-12') and C.A_SUM * C.KAPA * arb('1e-12') < arb('1e-10'), s(C13, 6))

# ---------------------------------------------------------------- Lemma 12 (digamma)
x_hi = arb(C.M + 3) / 2
err36 = 1 / (2 * x_hi) * x_hi / (H / 2) ** 2 + 1 / (12 * (H / 2)) + x_hi ** 2 / (2 * (H / 2) ** 2)
check("Lemma 12 / Kadiri (24): |Re psi(x+iy) - log y| < 1e-10 for 1 <= x <= (M+3)/2, y >= H/2", err36 < arb('1e-10'), s(err36, 3))
s38 = arb(0)
for m in range(C.M + 1):
    if C.KAPPA[m] > 0:
        s38 += kap[m] * (arb(m + 3) / 2).digamma()
    else:
        s38 += kap[m] * ((SIG0 * (1 + 2 * m) - m) / 2 + 1).digamma()
s38 = s38 / 2
Dk0 = -C.KAPS / 2 * C.PI.log() + s38
klog = sum(C.A_K[k] * (arb(k) / (2 * C.PI)).log() for k in range(1, C.K + 1))
tinyD = C.A_SUM * C.KAPA / 2 * arb('1e-10')

# ---------------------------------------------------------------- Lemma 11' and Lemma 10'
dm = [(TWO * m if C.KAPPA[m] < 0 else arb(m)) for m in range(C.M + 1)]


def h_series(u, n=2):
    us = arb_series([u, 1], prec=n)
    S = sum(kap[m] * (-dm[m] * us).exp() for m in range(C.M + 1))
    return C.w(ETA0 * us) * S - C.KAPS * W0


h0 = h_series(arb(0)).coeffs()
u1 = arb('0.5')
okd = all(h_series(ball(u1 * i / 2000, u1 * (i + 1) / 2000)).coeffs()[1].lower() > 0 for i in range(2000))
n2 = 20000
st = (arb(C.U_CUT) - u1) / n2
hmin = min(h_series(ball(u1 + i * st, u1 + (i + 1) * st)).coeffs()[0].lower() for i in range(n2))
check(f"Lemma 11': h(u) = w(eta0 u) sum kappa_m e^(-d_m u) - kappa w(0) >= 0 on [0, {C.U_CUT}] "
      "(h(0) = 0, h' > 0 on [0,0.5], h > 0 on [0.5, U]) => f(u) >= kappa eta w(0)",
      h0[0].contains(0) and h0[1].lower() > 0 and okd and hmin > 0 and ETA0 * C.U_CUT < C.D_SUPP,
      f"h'(0) = {s(h0[1], 6)}, min h on [0.5,U] >= {float(hmin):.3e}")
MP = {2: '0.23416332', 3: '0.05006283', 5: '0.00735649', 7: '0.00205251', 11: '0.00039742', 13: '0.00022273',
      17: '0.00009071', 19: '0.00006314', 23: '0.00003427', 29: '0.00001656', 31: '0.00001346'}
sum_mp = sum(arb(q).log() * arb(v) for q, v in MP.items())
check("Lemma 10': primes p <= 31 only, m <= 15 (15 log 31 < U_CUT); m_p certified in proof/zfr_audit/bty_4.896 part 3 "
      "(m_5 replaced by 0.00735649); kappa * sum log p m_p > 0.1186",
      15 * arb(31).log() < C.U_CUT and C.KAPS * sum_mp > arb('0.1186'), f"sum = {s(sum_mp, 9)}, kappa*sum = {s(C.KAPS * sum_mp, 8)}")
C_UP = C.KAPS / 2 * klog + Dk0 + tinyD - arb('0.1186')
check("C_UP = kappa/2 sum_k a_k log(k/2pi) + [k=0 digamma] + tiny - 0.1186 (BTY's -1.568 - 0.1186 analogue)", None,
      f"C_UP = {s(C_UP, 10)};  BTY: -1.568 - 0.1186 = -1.6866;  s38 = {s(s38, 6)}")

# ---------------------------------------------------------------- error constants (Lemma 8/9, per (k, m))
xm = [arb((SIG0 * (1 + 2 * m) - m - arb(1) / 2).lower()) for m in range(C.M + 1)]
spm = [arb((SIG0 * (1 + 2 * m) - m).lower()) for m in range(C.M + 1)]
Cm = [arb(C.C_ford(xm[m] / ETA0, xm[m] / ETA0).upper()) for m in range(C.M + 1)]
check("x_m = sigma0(1+2m) - m - 1/2, C_m = C(x_m/eta0, x_m/eta0)", None,
      "; ".join(f"m={m}: x={s(xm[m], 6)} C={s(Cm[m], 6)}" for m in range(C.M + 1)))


# J(x) = int |Re psi((1/2+iy)/2)| (x^2+y^2)^(-3/2) dy, rigorous upper sum (Re psi(1/4+iy/2) increasing in y >= 0)
def repsi(y):
    return acb(arb(1) / 4, arb(y) / 2).digamma().real


grid = [arb(0)]
for (lo, hi, n) in [(0, 2, 8000), (2, 30, 6000), (30, 1000, 4000)]:
    stp = (arb(hi) - arb(lo)) / n
    grid += [arb(lo) + stp * (i + 1) for i in range(n)]
vals = [abs(repsi(g)).upper() for g in grid]
YT = arb(1000)
tail = (2 * YT.log() + 1) / (4 * YT ** 2) + arb(10) / (6 * YT ** 2)   # |Re psi| <= log y + 10/3 for y >= 8 (REPORT §4.5)


def J_of(x):
    tot = arb(0)
    for i in range(len(grid) - 1):
        mx = arb(max(vals[i], vals[i + 1]))
        tot += (mx / (x ** 2 + grid[i] ** 2) ** (arb(3) / 2)).upper() * (grid[i + 1] - grid[i])
    return arb((2 * (tot + tail)).upper())


Jm = [J_of(xm[m]) for m in range(C.M + 1)]
check("J(x_m) = int |Re psi((1/2+iy)/2)|/(x_m^2+y^2)^(3/2) dy (rigorous upper sums; audit: 23.600 at x = 0.4935)", None,
      "; ".join(f"m={m}: {s(Jm[m], 6)}" for m in range(C.M + 1)))
Y13 = H - 2
I13 = 2 * ((6 + arb(3).log()) / (2 * Y13 ** 2) + (2 * Y13.log() + 1) / (4 * Y13 ** 2))
check("I_1 + I_3 <= 2[(6+log 3)/(2Y^2) + (2 log Y + 1)/(4Y^2)], Y = H - 2, using U(x) <= 6 + log(1+|x|)", I13 < arb('1e-20'), s(I13, 3))
Sc = sum(abs(kap[m]) * Cm[m] / (C.PI * xm[m] ** 2) for m in range(C.M + 1))
Q_ERR = arb((Sc * C.A_SUM).upper())
k_ge1 = sum(C.A_K[k] * arb(k).log() for k in range(1, C.K + 1))
T2far = sum(abs(kap[m]) * C.C_ford(spm[m] / ETA0, H / ETA0) for m in range(C.M + 1)) / H ** 3
P_k1 = Sc * k_ge1 + C.A_SUM * (sum(abs(kap[m]) * Cm[m] / (2 * C.PI) for m in range(C.M + 1)) * I13 + T2far)
P_k0 = C.A_K[0] * sum(abs(kap[m]) * (Cm[m] / (2 * C.PI) * Jm[m] + C.C_ford(spm[m] / ETA0, spm[m] / ETA0) / spm[m] ** 3)
                      for m in range(C.M + 1))
P_ERR = arb((P_k1 + P_k0).upper())
check("Err = sum_k a_k sum_m |kappa_m| (T1 + T2) <= eta^3 (P_ERR + Q_ERR log t)", None,
      f"P_ERR = {s(P_ERR, 8)} (k=0 part {s(P_k0, 6)}), Q_ERR = {s(Q_ERR, 8)};  BTY corrected: 187 eta^2 + 8396 eta^3, "
      f"i.e. Q ~ 187/A0 = {s(arb(187) / C.A_MAX, 5)}")

# ---------------------------------------------------------------- monotonicity in eta (worst case eta = eta_max)
f3 = (1 - 3 * ETA0) ** 2
DL = W0 / f3 * (C.A1 * (1 + sum(abs(kap[m]) * (arb(1) / m + arb(1) / (m + 1)) for m in range(1, C.M + 1)))
                + C.A0 * sum(abs(kap[m]) / m for m in range(1, C.M + 1)))
dQ = DL + W0 * abs(C_UP) + arb('1e-10') - C.KC * C.LOGH
check("dQ/deta <= |dL14/deta| + w(0)|C_UP| + 1e-10 - KC log H < 0 (so Q is minimal at eta_max)", dQ < 0,
      f"|dL14/deta| <= {s(DL, 6)}, bound = {s(dQ, 6)}")

# ---------------------------------------------------------------- G increasing
C.GT.check_increasing()
check("G'(mu) > 0 on [0.879, 1] (121 ball evaluations)", C.GT.ok)

# ---------------------------------------------------------------- spot checks (consistency, not part of the proof)
def W_quad(z):
    return acb.integral(lambda u, an: (-acb(z) * u).exp() * C.w(u), 0, acb(C.D_SUPP)).real


okWb = all(W_quad(z).overlaps(C.W_big(z)) for z in [C.R_MIN, arb(200), arb(777), arb(5000)])
check("w''(0) and max|w'''| on [0, d]", None, f"{s(C.W2, 8)}, {s(C.M3, 6)}")
check("W_big(z) = w(0)/z + w''(0)/z^3 +- max|w'''|/z^4 contains the quadrature value of W(z) at 4 points", okWb,
      f"R_MIN = {s(C.R_MIN, 6)}")
okL = True
for eta_, mu_ in [(arb('0.0074'), arb('0.912')), (arb('0.006'), arb('0.95')), (arb('0.0045'), arb('0.99'))]:
    sig = 1 - mu_ * eta_
    dd = 2 * sig - 1
    Fq = lambda z: sum(kap[m] * W_quad((z + dd * m) / eta_) for m in range(C.M + 1))
    direct = C.A1 * Fq(sig - 1 + eta_) + C.A1 * Fq(sig - eta_) - C.A0 * Fq(sig - 1)
    ours = C.G_of_mu(mu_) + C.L14_rest(eta_, mu_)
    bty = (arb('0.8763706262060879961463361') + arb('0.1200272738497559075009453') * mu_ + arb('0.01017689758922835202429806') * mu_ ** 2
           - arb('0.0005028489366734115179272774') * mu_ ** 3 + arb('3.909752404944572702802208') * eta_
           + arb('20.15284561478752152132202') * eta_ ** 2 - arb('568.0617933784882980455313') * eta_ ** 3)
    okL &= direct.overlaps(ours)
    check(f"L14 at eta={eta_.str(3)}, mu={mu_.str(3)}: quadrature vs ours (G + Ford balls) vs BTY corrected Lemma 14", None,
          f"{s(direct, 10)} | {ours.str(10)} | {s(bty, 10)}")
check("L14 consistency (quadrature value inside our enclosure at 3 points)", okL)

json.dump(dict(Z_MIN=C.Z_MIN.str(20), U_CUT=C.U_CUT, eta0=ETA0.str(25), sigma0=SIG0.str(25), eps0=str(eps0), c0=str(c0q),
               C_UP=(C_UP.upper() + arb('1e-25')).str(30, radius=False), P_ERR=(P_ERR * (1 + arb('1e-20'))).str(30, radius=False),
               Q_ERR=(Q_ERR * (1 + arb('1e-20'))).str(30, radius=False),
               J=[j.str(15, radius=False) for j in Jm], C_m=[c.str(15, radius=False) for c in Cm]),
          open(os.path.join(C.HERE, 'cl_constants.json'), 'w'), indent=1)
print("FAILURES:", NF)
sys.exit(NF)
