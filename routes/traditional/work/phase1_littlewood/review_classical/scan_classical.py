"""Dense point scan of the independent margin (mpmath quadrature of L14 from the definition of F), s = 1.

For every v on a grid over (28.7296, 60] (step 0.02, plus points 1e-9 inside every band edge), with the
band's own Z from zfr_classical_local.csv:
    eta = A/v, y = window(v) (min over gamma in [H, 16 e^v + 1e10] of the zero-free width, capped at A/v),
    sigma = 1 - y, mu = y/eta,
    Q = L14 - eta w0 C_UP - 1e-10 eta - 1e-7 - eta^3 (P_ERR + Q_ERR v) - (a kappa w0/2) A
with C_UP, P_ERR, Q_ERR from indep_constants.json (computed independently by indep_classical.py).
Also reports the eta-monotonicity spot check (Q at eta = A/(2v) vs A/v, i.e. s = 1/2 vs s = 1).

Run:  python -I scan_classical.py > scan_classical_output.txt
"""
import sys, os, csv, json
sys.dont_write_bytecode = True
import mpmath as mp
from mpmath import mpf

mp.mp.dps = 20
HERE = os.path.dirname(os.path.abspath(__file__))
WORK = os.path.dirname(HERE)
th = mpf('1.1338')
S = 1 / mp.cos(th) ** 2
tau = mp.tan(th)
D = th / tau
d = 2 * D
kap = [mpf(1), mpf(-851) / 859, mpf(780) / 859, mpf(-525) / 859, mpf(171) / 859, mpf(28) / 859, mpf(-29) / 859]
M = 6
kappa = sum(kap)
c = [4, -8, 2, 20, -9, -34, 27, 91, -27, -201, 32, 895, 1949, 2389, 1896, 949, 239]
ak = [mpf(sum(c[j] * c[j + k] for j in range(17 - k)) * (1 if k == 0 else 2)) / 14912370 for k in range(17)]
a0, a1, asum = ak[0], ak[1], sum(ak[1:])
H = 3 * mpf(10) ** 12
T0 = mpf(10) ** 10
ZMTY = mpf('5.558691')


def w(u):
    return S * (S * (D - u / 2) * mp.cos(u * tau) + 2 * D - u + mp.sin(2 * th - u * tau) / mp.sin(2 * th)
                - 2 * (1 + mp.sin(th - u * tau) / mp.sin(th)))


w0 = w(mpf(0))
KC = asum * kappa * w0 / 2
cst = json.load(open(os.path.join(HERE, 'indep_constants.json')))
CUP, PERR, QERR = mpf(cst['C_UP']), mpf(cst['P_ERR']), mpf(cst['Q_ERR'])


def F(z, sig, eta):
    dd = 2 * sig - 1
    g = lambda x: mp.exp(-z * x / eta) * w(x) * sum(kap[m] * mp.exp(-dd * m * x / eta) for m in range(M + 1))
    pts = sorted(set(p for p in [mpf(0), eta * mpf('0.05'), eta * mpf('0.3'), eta, eta * 4, eta * 15, mpf('0.3'), d] if p <= d))
    return mp.quad(g, pts)


def L14(sig, eta):
    return a1 * F(sig - 1 + eta, sig, eta) + a1 * F(sig - eta, sig, eta) - a0 * F(sig - 1, sig, eta)


rows = list(csv.DictReader(open(os.path.join(WORK, 'zfr_classical_local.csv'))))
prof = [(mpf(r['logt_lo']), mpf(r['logt_hi']), mpf(r['Z1'])) for r in rows]


def band(v):
    for a, b, z in prof:
        if a < v <= b:
            return z
    raise ValueError(v)


def window(v, Z):
    logT = mp.log(16 * mp.exp(v) + T0)
    cands = [1 / (z * min(b, logT)) for a, b, z in prof if a < logT]
    if logT > 60:
        cands.append(1 / (ZMTY * logT))
    return min(min(cands), 1 / (Z * v))


def Q(v, s=1):
    Z = band(v)
    A = 1 / Z
    y = window(v, Z)
    eta = s * A / v
    sig = 1 - s * y
    return (L14(sig, eta) - eta * w0 * CUP - mpf('1e-10') * eta - mpf('1e-7') - eta ** 3 * (PERR + QERR * v) - KC * eta * v), KC * A, y * v * Z


pts = set()
x = mpf('28.73')
while x <= 60:
    pts.add(mp.nstr(x, 8))
    x += mpf('0.02')
for a, b, z in prof:
    pts.add(mp.nstr(a + mpf('1e-9'), 15))
    pts.add(mp.nstr(b - mpf('1e-9'), 15))
    pts.add(mp.nstr(b, 15))
pts = sorted(mpf(p) for p in pts if mpf(p) > prof[0][0] and mpf(p) <= 60)
worst = []
neg = []
for v in pts:
    q, main, mu = Q(v)
    rel = q / main
    worst.append((rel, v, mu))
    if q <= 0:
        neg.append((v, q))
worst.sort()
print(f"{len(pts)} points scanned on ({prof[0][0]}, 60]; number with margin <= 0: {len(neg)}")
for v, q in neg[:20]:
    print("   NEG", mp.nstr(v, 12), mp.nstr(q, 6))
print("10 smallest relative margins (rel, v, mu):")
for rel, v, mu in worst[:10]:
    print("  ", mp.nstr(rel, 4), mp.nstr(v, 12), mp.nstr(mu, 7))
# per-band minimum
print("per-band min relative point margin:")
for a, b, z in prof:
    mm = min((r for r in worst if a < r[1] <= b), default=None)
    print(f"   ({mp.nstr(a, 7)}, {mp.nstr(b, 7)}] Z={mp.nstr(z, 5)}: {mp.nstr(mm[0], 4)} at v={mp.nstr(mm[1], 10)}")
# monotonicity in s (eta): Q at s = 0.5, 0.75, 1 at a few heights
print("Q(s) at s = 0.5, 0.75, 0.9, 1 (eta = sA/v, sigma = 1 - s y):")
for v in [mpf('28.75'), mpf('31.899'), mpf('45'), mpf('59.9')]:
    print("  v =", v, [mp.nstr(Q(v, mpf(s))[0], 6) for s in ('0.5', '0.75', '0.9', '1')])
