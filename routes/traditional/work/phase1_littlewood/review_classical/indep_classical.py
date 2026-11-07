"""Independent re-implementation (mpmath) of the local classical zero-free-region inequality.

Written from the mathematics (BTY arXiv:2603.21490v1 + the derivation in the brief), NOT from cl_core.py.
Only at the very end is cl_core (the copy in ./rerun) imported, to compare numbers.

Run:  python -I indep_classical.py > indep_classical_output.txt
"""
import sys, os, csv, json, math
sys.dont_write_bytecode = True
import mpmath as mp
from mpmath import mpf, mpc

mp.mp.dps = 30
HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.dirname(HERE)

# ------------------------------------------------------------------ parameters (typed from the BTY LaTeX)
th = mpf('1.1338')
S = 1 / mp.cos(th) ** 2          # sec^2
tau = mp.tan(th)
D = th / tau                      # theta cot theta
d = 2 * D                         # support of w
kap = [mpf(1), mpf(-851) / 859, mpf(780) / 859, mpf(-525) / 859, mpf(171) / 859, mpf(28) / 859, mpf(-29) / 859]
M = 6
kappa = sum(kap)
kabs = sum(abs(k) for k in kap)
c = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
K = 16
ak = [mpf(sum(c[j] * c[j + k] for j in range(K + 1 - k)) * (1 if k == 0 else 2)) / 14912370 for k in range(K + 1)]
a0, a1 = ak[0], ak[1]
asum = sum(ak[1:])
H = mpf(3) * mpf(10) ** 12
T0 = mpf(10) ** 10
ZMTY = mpf('5.558691')
ZMIN = mpf('4.58')
AMAX = 1 / ZMIN
eta0 = AMAX / mp.log(H)                       # (1+2e-100) factor is irrelevant at this precision
sig0 = 1 - AMAX / mp.log(K * H + T0)
b = [kap[0]] + [kap[m] + kap[m - 1] for m in range(1, M + 1)] + [kap[M]]   # (1+x) sum kappa_m x^m


def w(u):
    return S * (S * (D - u / 2) * mp.cos(u * tau) + 2 * D - u + mp.sin(2 * th - u * tau) / mp.sin(2 * th)
                - 2 * (1 + mp.sin(th - u * tau) / mp.sin(th)))


w0 = w(mpf(0))
w2 = mp.diff(w, 0, 2)

# closed form of W(z) = int_0^d e^{-zu} w(u) du, w = sum (alpha + beta u) e^{lam u}
I = mpc(0, 1)
PIECES = [(I * tau, S * S * D / 2, -S * S / 4), (-I * tau, S * S * D / 2, -S * S / 4),
          (mpc(0), S * (2 * D - 2), -S),
          (-I * tau, S * mp.exp(2 * I * th) / (2 * I * mp.sin(2 * th)), 0),
          (I * tau, -S * mp.exp(-2 * I * th) / (2 * I * mp.sin(2 * th)), 0),
          (-I * tau, -2 * S * mp.exp(I * th) / (2 * I * mp.sin(th)), 0),
          (I * tau, 2 * S * mp.exp(-I * th) / (2 * I * mp.sin(th)), 0)]


def w_pieces(u):
    return sum((al + be * u) * mp.exp(la * u) for la, al, be in PIECES)


def W_cf(z):
    z = mpc(z)
    tot = mpc(0)
    for la, al, be in PIECES:
        cc = la - z
        if abs(cc) * d < mpf('1e-6'):          # series, avoids 0/0 at z = lam
            i0 = sum(cc ** n * d ** (n + 1) / mp.factorial(n + 1) for n in range(12))
            i1 = sum(cc ** n * d ** (n + 2) / (mp.factorial(n) * (n + 2)) for n in range(12))
            tot += al * i0 + be * i1
            continue
        e = mp.exp(cc * d)
        i0 = (e - 1) / cc
        i1 = d * e / cc - (e - 1) / cc ** 2
        tot += al * i0 + be * i1
    return tot


def W_quad(z):
    z = mpf(z)
    pts = [mpf(0)] + [p for p in (1 / abs(z), 5 / abs(z), 20 / abs(z), mpf('0.3')) if p < d] + [d]
    pts = sorted(set(pts))
    return mp.quad(lambda u: mp.exp(-z * u) * w(u), pts)


def F_direct(z, sig, eta):
    """F(z) = int_0^{d/eta} e^{-zu} eta w(eta u) sum kappa_m e^{-(2sig-1) m u} du  (substituted x = eta u)."""
    dd = 2 * sig - 1
    g = lambda x: mp.exp(-z * x / eta) * w(x) * sum(kap[m] * mp.exp(-dd * m * x / eta) for m in range(M + 1))
    pts = [mpf(0), eta * mpf('0.05'), eta * mpf('0.3'), eta, eta * 4, eta * 15, mpf('0.3'), d]
    pts = sorted(set(p for p in pts if p <= d))
    return mp.quad(g, pts)


def L14_direct(sig, eta):
    return a1 * F_direct(sig - 1 + eta, sig, eta) + a1 * F_direct(sig - eta, sig, eta) - a0 * F_direct(sig - 1, sig, eta)


def L14_split(sig, eta):
    """Same via F(z) = sum kappa_m W((z + delta_m)/eta), W by quadrature (cross-check)."""
    dd = 2 * sig - 1
    Fz = lambda z: sum(kap[m] * W_quad((z + dd * m) / eta) for m in range(M + 1))
    return a1 * Fz(sig - 1 + eta) + a1 * Fz(sig - eta) - a0 * Fz(sig - 1)


# ------------------------------------------------------------------ Ford's bound C(nu, r), c0 = 1/(sin th cos^3 th)
def C_ford(nu, r):
    s, co = mp.sin(th), mp.cos(th)
    c0 = 1 / (s * co ** 3)
    c1 = (th - s * co) * tau ** 4
    c2 = tau ** 3 * s ** 2
    c3 = (th - s * co) * tau ** 2
    return c0 * r * (c2 * (r + 1) ** 2 * (mp.exp(-2 * nu * D) + 1) + c1 * r + c3 * r ** 3) / (r ** 2 - tau ** 2) ** 2


out = []


def P(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)


def f(x, n=10):
    return mp.nstr(x, n)


P("=" * 100)
P("INDEPENDENT CHECK of the local classical region (mpmath, dps=30)")
P("=" * 100)
P("w(0) =", f(w0, 14), " closed form sec^2(th tan th + 3 th cot th - 3) =", f(S * (th * tau + 3 * D - 3), 14))
P("w''(0) =", f(w2, 12), " d =", f(d, 12))
P("w from exponential pieces vs formula, max diff on 50 pts:", f(max(abs(w_pieces(d * i / 49) - w(d * i / 49)) for i in range(50)), 3))
P("W closed form vs quadrature at z = -0.95, 0.05, 1, 128.6, 700:",
  [f(abs(W_cf(z).real - W_quad(z)), 3) for z in (mpf('-0.95'), mpf('0.05'), mpf(1), mpf('128.6'), mpf(700))])
P("kappa =", f(kappa, 12), "(433/859 =", f(mpf(433) / 859, 12), ")  sum|kappa| =", f(kabs, 12))
P("a0 =", f(a0), " a1 =", f(a1, 12), "(865534/497079 =", f(mpf(865534) / 497079, 12), ")  a =", f(asum, 12),
  "(2919857/828465 =", f(mpf(2919857) / 828465, 12), ")")
P("min_k a_k =", f(min(ak), 4), "  P(x) >= 0 check: min over 2001 pts in [0,pi] of sum a_k cos kx =",
  f(min(sum(ak[k] * mp.cos(k * x) for k in range(K + 1)) for x in mp.linspace(0, mp.pi, 2001)), 4))
KC = asum * kappa * w0 / 2
P("eta0 =", f(eta0, 12), " sigma0 =", f(sig0, 12), " KC = a kappa w(0)/2 =", f(KC, 12))

# ------------------------------------------------------------------ Lemma 3, Lemma 5 B-tilde, eps0
P("\n--- Lemma 3 / Lemma 5")
pk = lambda x: sum(kap[m] * x ** m for m in range(M + 1))
P("min_{x in [0,1]} sum kappa_m x^m (4001 pts) =", f(min(pk(x) for x in mp.linspace(0, 1, 4001)), 6))
r5 = (2 * sig0 - 1) / eta0
val5 = eta0 ** 2 * C_ford(r5, r5) / ((2 * sig0 - 1) ** 2 * w0)
P("r = (2sig0-1)/eta0 =", f(r5, 8), " C(r,r) =", f(C_ford(r5, r5), 8), " eta0^2 C/((2sig0-1)^2 w0) =", f(val5, 8),
  " < 11/20000 = 0.00055:", val5 < mpf(11) / 20000)
eps0 = mpf(11) / 20000
Bt = lambda Y: sum((b[m] * m - abs(b[m]) * eps0 / m) / (m * m + Y * Y) for m in range(1, M + 2))
ys = [mpf(i) / 1000 for i in range(0, 20001)] + [mp.mpf(10) ** (mpf(i) / 50) for i in range(65, 400)]
vals = [(Bt(Y) * (1 + Y * Y), Y) for Y in ys]
mn = min(vals)
P("B-tilde(Y)(1+Y^2) min over Y in [0,20] (step 1e-3) and log grid to 1e8:", f(mn[0], 6), "at Y =", f(mn[1], 6),
  "; limit Y->inf of Y^2 Btilde = sum m b_m - eps0 sum|b_m|/m =", f(sum(m * b[m] for m in range(M + 2)) - eps0 * sum(abs(b[m]) / m for m in range(1, M + 2)), 6),
  "; sum m b_m =", f(sum(m * b[m] for m in range(M + 2)) * 859, 6), "/859")
# check also with BTY's c0 = 151/153 split -- for comparison only
c0b = mpf(151) / 153
BtB = lambda y: sum(((b[m] * (m - eps0 / m)) / (m * m + y * y)) if b[m] > 0 else ((b[m] * (m + eps0 / m)) / (c0b ** 2 * m * m + y * y)) for m in range(1, M + 2))
P("(for reference) BTY's split with c0 = 151/153, same eps0: min B(y)(1+y^2) on [0,20] =",
  f(min(BtB(y) * (1 + y * y) for y in [mpf(i) / 200 for i in range(4001)]), 6))


# Direct test of Re F(iy) + Re F(2 sigma - 1 - iy) >= 0 via the closed form of W
def R5(y, sig, eta):
    dd = 2 * sig - 1
    return sum(b[m] * W_cf((dd * m + I * y) / eta) for m in range(M + 2)).real


def R5b(y, sig, eta):     # same from F directly
    dd = 2 * sig - 1
    Fz = lambda z: sum(kap[m] * W_cf((z + dd * m) / eta) for m in range(M + 1))
    return (Fz(I * y) + Fz(2 * sig - 1 - I * y)).real


mp.mp.dps = 40
P("closed-form consistency R5 vs F(iy)+F(2s-1-iy) at y = 0.37, sig0, eta0:", f(R5(mpf('0.37'), sig0, eta0), 12), f(R5b(mpf('0.37'), sig0, eta0), 12))
cases = [(sig0, eta0), (sig0, eta0 / 2), (sig0, mpf('0.001')), (mpf('0.9999'), eta0), (mpf('0.99965'), mpf('0.0034')),
         (1 - mpf('0.006831'), mpf('0.007538')), (1 - mpf('0.00294'), mpf('0.00326'))]
ygrid = [mpf(i) / 100 for i in range(0, 1001)] + [mpf(10) * mp.mpf(10) ** (mpf(i) / 40) for i in range(1, 241)]
for sig, eta in cases:
    dd = 2 * sig - 1
    worst = None
    for y in ygrid:
        r = R5(y, sig, eta) / (eta * w0 * dd) * (1 + (y / dd) ** 2)
        if worst is None or r < worst[0]:
            worst = (r, y)
    P(f"  sigma={f(sig, 8)} eta={f(eta, 6)}: min over {len(ygrid)} y in [0,1e7] of [ReF(iy)+ReF(2s-1-iy)](1+(y/d)^2)/(eta w0 d) =",
      f(worst[0], 6), "at y =", f(worst[1], 6))
# interior points of the strip 0 <= Re z <= 2 sigma - 1 (minimum principle sanity check)
sig, eta = sig0, eta0
dd = 2 * sig - 1
Fz = lambda z: sum(kap[m] * W_cf((z + dd * m) / eta) for m in range(M + 1))
mins = min((Fz(x + I * y) + Fz(dd - (x - I * y))).real * (1 + y * y) for x in [dd * q / 8 for q in range(9)] for y in [mpf(j) / 20 for j in range(0, 400)])
P("  interior of strip (sig0, eta0): min of Re[F(z)+F(2s-1-conj z)](1+y^2) over a 9 x 400 grid =", f(mins, 6))
mp.mp.dps = 30

# ------------------------------------------------------------------ Ford's bound sanity: sup |xi^3 W0(xi)| on Re xi = nu
P("\n--- Ford's bound C(nu,nu) vs sup_y |xi^3 W_0(xi)|, xi = nu + iy (closed form W, dps 40)")
mp.mp.dps = 40
for nu in [(sig0 - mpf('0.5')) / eta0, (3 * sig0 - 1 - mpf('0.5')) / eta0, (2 * sig0 - 1) / eta0, sig0 / eta0, mpf(1) / eta0 - 3]:
    sup = mpf(0)
    for y in [mpf(0)] + [mp.mpf(10) ** (mpf(i) / 30) for i in range(-60, 241)]:
        xi = nu + I * y
        v = abs(xi ** 3 * (W_cf(xi) - w0 / xi))
        sup = max(sup, v)
    P(f"  nu = {f(nu, 8)}: sup|xi^3 W0| = {f(sup, 8)}   C(nu,nu) = {f(C_ford(nu, nu), 8)}   |w''(0)| = {f(abs(w2), 8)}")
mp.mp.dps = 30

# ------------------------------------------------------------------ Lemma 11 (U = 54) and Lemma 10
P("\n--- Lemma 11 / Lemma 10")
dm = [((2 * sig0 - 1) * m if kap[m] < 0 else mpf(m)) for m in range(M + 1)]
h = lambda u: w(eta0 * u) * sum(kap[m] * mp.exp(-dm[m] * u) for m in range(M + 1)) - kappa * w0
hv = [(h(u), u) for u in [mpf(i) / 100 for i in range(1, 5401)]]
P("min h(u) on (0, 54] (step 0.01):", f(min(hv)[0], 6), "at u =", f(min(hv)[1], 5), "; h(54) =", f(h(mpf(54)), 6),
  "; first u > 54 with h < 0 ~", next((f(mpf(u) / 10, 4) for u in range(540, 700) if h(mpf(u) / 10) < 0), None))
MP = {2: '0.23416332', 3: '0.05006283', 5: '0.00735649', 7: '0.00205251', 11: '0.00039742', 13: '0.00022273',
      17: '0.00009071', 19: '0.00006314', 23: '0.00003427', 29: '0.00001656', 31: '0.00001346'}
smp = sum(mp.log(p) * mpf(v) for p, v in MP.items())
P("sum_{p<=31} log p m_p =", f(smp, 10), " kappa * sum =", f(kappa * smp, 10), " > 0.1186:", kappa * smp > mpf('0.1186'),
  "; 15 log 31 =", f(15 * mp.log(31), 6))


# spot-check: G_p(1,x) >= m_p (float grid; certification is in the audit part 3)
def Gp(p, x):
    return sum(mpf(p) ** (-m) * sum(ak[k] * mp.cos(m * k * x) for k in range(K + 1)) for m in range(1, 16))


mp.mp.dps = 20
for p in (2, 3, 5, 31):
    mn = min(Gp(p, x) for x in mp.linspace(0, mp.pi, 2001))
    P(f"  p={p}: min over 2001-pt grid of G_p(1,x) = {f(mn, 10)}  (m_p = {MP[p]})")
mp.mp.dps = 30

# ------------------------------------------------------------------ digamma constant C_UP
P("\n--- Lemma 12 constant")
klog = sum(ak[k] * mp.log(mpf(k) / (2 * mp.pi)) for k in range(1, K + 1))
k0 = -kappa / 2 * mp.log(mp.pi) + sum(kap[m] * (mp.digamma(mpf(m + 3) / 2) if kap[m] > 0 else mp.digamma((sig0 * (1 + 2 * m) - m) / 2 + 1))
                                      for m in range(M + 1)) / 2
tiny = asum * kabs / 2 * mpf('1e-10')
CUP = kappa / 2 * klog + k0 + tiny - mpf('0.1186')
P("kappa/2 sum a_k log(k/2pi) =", f(kappa / 2 * klog, 12), "; k=0 part (monotone bound) =", f(k0, 12), "; C_UP =", f(CUP, 12))
# the k=0 part at actual sigma values (information: how much the monotone bound loses)
for sg in (sig0, 1 - mpf('0.00683'), 1 - mpf('0.0033')):
    act = -kappa / 2 * mp.log(mp.pi) + sum(kap[m] * mp.digamma((sg + (2 * sg - 1) * m) / 2 + 1) for m in range(M + 1)) / 2
    P(f"   k=0 part at sigma = {f(sg, 8)} exactly: {f(act, 10)}")
# check Kadiri (24)-based approximation for k >= 1 directly at t = H
t = H
dev = max(abs(sum(kap[m] * (-mp.log(mp.pi) / 2 + mp.digamma((sig0 + (2 * sig0 - 1) * m) / 2 + 1 + I * k * t / 2).real / 2) for m in range(M + 1))
              - kappa / 2 * mp.log(k * t / (2 * mp.pi))) for k in range(1, K + 1))
P("max_k |sum_m kappa_m(-log pi/2 + Re psi/2) - kappa/2 log(kt/2pi)| at t = H, sigma = sigma0:", f(dev, 4))

# ------------------------------------------------------------------ error constants P_ERR, Q_ERR
P("\n--- error constants")
xm = [sig0 * (1 + 2 * m) - m - mpf(1) / 2 for m in range(M + 1)]
spm = [sig0 * (1 + 2 * m) - m for m in range(M + 1)]
Cm = [C_ford(x / eta0, x / eta0) for x in xm]
rp = lambda y: mp.digamma(mpf(1) / 4 + I * y / 2).real
y0 = mp.findroot(rp, 1.0)
P("Re psi(1/4 + iy/2) = 0 at y =", f(y0, 10))


def J(x):
    g = lambda y: abs(rp(y)) / (x * x + y * y) ** mpf(1.5)
    return 2 * mp.quad(g, [0, y0, 2, 10, 100, 1000, mp.inf])


Jm = [J(x) for x in xm]
for m in range(M + 1):
    P(f"  m={m}: x_m={f(xm[m], 8)}  C_m={f(Cm[m], 9)}  J(x_m)={f(Jm[m], 9)}  sp_m={f(spm[m], 8)}  C(sp/eta0,sp/eta0)={f(C_ford(spm[m] / eta0, spm[m] / eta0), 8)}")
# |Re psi(1/4+iy/2)| <= log y for y >= 2
worst = min((mp.log(y) - abs(rp(y)), y) for y in [mpf(2) + mpf(i) / 100 for i in range(0, 2000)] + [mp.mpf(10) ** (mpf(i) / 20) for i in range(27, 200)])
P("min over y in [2, 1e10] of log y - |Re psi(1/4+iy/2)| =", f(worst[0], 6), "at y =", f(worst[1], 6))
Sc = sum(abs(kap[m]) * Cm[m] / (mp.pi * xm[m] ** 2) for m in range(M + 1))
QERR = asum * Sc
Pk0 = a0 * sum(abs(kap[m]) * (Cm[m] * Jm[m] / (2 * mp.pi) + C_ford(spm[m] / eta0, spm[m] / eta0) / spm[m] ** 3) for m in range(M + 1))
Pk1 = Sc * sum(ak[k] * mp.log(k) for k in range(1, K + 1))
PERR = Pk0 + Pk1
P("Q_ERR =", f(QERR, 10), " P_ERR =", f(PERR, 10), "(k=0:", f(Pk0, 8), ", k>=1 log k:", f(Pk1, 8), ") [neglecting the ~1e-20 terms]")
P("BTY-style (one x0 for all m) for comparison: Q =", f(asum * kabs * Cm[0] / (mp.pi * xm[0] ** 2), 8))

# ------------------------------------------------------------------ monotonicity in eta: direct numerical derivative
P("\n--- dL14/deta at fixed mu (finite differences of the direct quadrature)")
for eta_, mu_ in [(eta0, mpf('0.88')), (eta0, mpf(1)), (mpf('0.0045'), mpf('0.95')), (mpf('0.0033'), mpf('0.88'))]:
    hh = mpf('1e-7')
    L = lambda e: L14_direct(1 - mu_ * e, e)
    der = (L(eta_ + hh) - L(eta_ - hh)) / (2 * hh)
    P(f"  eta={f(eta_, 6)} mu={f(mu_, 4)}: dL14/deta = {f(der, 8)}   (claimed bound 48.55; KC log H - w0|C_UP| = {f(KC * mp.log(H) - w0 * abs(CUP), 6)})")

json.dump(dict(C_UP=str(CUP), P_ERR=str(PERR), Q_ERR=str(QERR), J=[str(x) for x in Jm], C_m=[str(x) for x in Cm], KC=str(KC)),
          open(os.path.join(HERE, 'indep_constants.json'), 'w'), indent=1)

# ------------------------------------------------------------------ profile, window, margin at test heights
P("\n--- profile")
rows = list(csv.DictReader(open(os.path.join(WORK, 'zfr_classical_local.csv'))))
prof = [(float(r['logt_lo']), float(r['logt_hi']), r['Z1']) for r in rows]
pj = json.load(open(os.path.join(WORK, 'profile_classical.json')))
same = [(float(a), float(b_), str(z)) for a, b_, z in pj['bands']] == prof
contig = all(prof[i][1] == prof[i + 1][0] for i in range(len(prof) - 1))
P(f"{len(prof)} bands, CSV == profile json: {same}, contiguous: {contig}, range ({prof[0][0]}, {prof[-1][1]}], "
  f"all status proved: {all(r['status'] == 'proved' for r in rows)}")
Zs = [mpf(z) for _, _, z in prof]
P("min Z =", min(Zs), " max Z =", max(Zs), " all < 5.558691:", all(z < ZMTY for z in Zs), " all >= 4.58:", all(z >= ZMIN for z in Zs),
  " log H =", f(mp.log(H), 10), " V_LO < log H:", mpf(prof[0][0]) < mp.log(H))
nonmono = [(prof[i][0], prof[i][2], prof[i + 1][2]) for i in range(len(prof) - 1) if mpf(prof[i + 1][2]) < mpf(prof[i][2])]
P("bands where Z decreases with height:", nonmono)


def window(v, Zi):
    """y <= min over gamma in [H, T] of zero-free width, T = 16 e^v + T0; capped at A_i/v."""
    logT = mp.log(16 * mp.exp(v) + T0)
    cands = []
    for (a, bb, z) in prof:
        if a < logT:
            cands.append(1 / (mpf(z) * min(mpf(bb), logT)))
    if logT > 60:
        cands.append(1 / (ZMTY * logT))
    y = min(cands)
    return min(y, 1 / (Zi * v)), logT


def band_of(v):
    for (a, bb, z) in prof:
        if a < v <= bb:
            return z
    raise ValueError


def margin(v, eps_rel=0):
    v = mpf(v)
    Zi = mpf(band_of(v))
    A = 1 / Zi
    y, logT = window(v, Zi)
    eta = A / v
    sig = 1 - y
    mu = y / eta
    L = L14_direct(sig, eta)
    lin = -eta * w0 * CUP
    err = eta ** 3 * (PERR + QERR * v)
    main = KC * A
    Qv = L + lin - mpf('1e-10') * eta - mpf('1e-7') - err - main
    return dict(v=v, Z=Zi, y=y, logT=logT, eta=eta, mu=mu, sig=sig, L14=L, lin=lin, err=err, main=main, Q=Qv)


P("\n--- margin at test heights (s = 1, eta = A/v, sigma = 1 - y(v)); independent vs cl_core.cell_margin([v, v+1e-7])")
sys.path.insert(0, os.path.join(HERE, 'rerun'))
import cl_core as CC
from flint import arb
CC.GT.check_increasing()
tests = [28.73, 29.0, 30.0, 31.5, 31.85, 31.899, 32.0, 35.0, 40.0, 45.0, 49.9, 54.5, 57.5, 59.99]
results = []
for v in tests:
    r = margin(v)
    yc, _ = CC.window_y([[a, bb, z] for a, bb, z in prof], v + 1e-7, 60.0)
    Qc, det = CC.cell_margin(v, v + 1e-7, band_of(v), yc, detail=True)
    L_code = det['G'] + det['rest']
    # code's G evaluated at exact mu (not the grid point) for a like-for-like L14 comparison
    Gex = CC.G_of_mu(arb(str(r['mu'])))
    Lex = Gex + CC.L14_rest(arb(str(r['eta'])), arb(str(r['mu'])))
    Lsplit = L14_split(r['sig'], r['eta'])
    P(f"v={v:7.3f} Z={r['Z']}: y={f(r['y'], 8)} mu={f(r['mu'], 7)} eta={f(r['eta'], 7)} logT={f(r['logT'], 6)}")
    P(f"    L14 direct quad = {f(r['L14'], 12)}; via W-split quad = {f(Lsplit, 12)}; cl_core G(mu)+rest at same point = {Lex.str(12)}")
    P(f"    terms: L14 {f(r['L14'], 9)} | -eta w0 C_UP {f(r['lin'], 9)} | -err {f(-r['err'], 6)} | -main {f(-r['main'], 9)}")
    P(f"    margin indep = {f(r['Q'], 8)} (rel {f(r['Q'] / r['main'], 4)});  cl_core cell = {f(mpf(Qc.str(15, radius=False)), 8)} "
      f"(rel {f(mpf(Qc.str(15, radius=False)) / r['main'], 4)});  code cell L14 lower = {L_code.lower().str(10)}, code err = {det['err'].str(8)}")
    results.append((v, float(r['Q']), float(Qc.str(15, radius=False))))

P("\nSummary (v, indep margin, cl_core cell margin):")
for v, a_, b_ in results:
    P(f"  {v:8.3f}  {a_: .4e}  {b_: .4e}")
