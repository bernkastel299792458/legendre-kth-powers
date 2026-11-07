# Rigorous (Arb, python-flint) verification of the sign table of RZA Lemma 3.1 (= RZ23 Thm 1.7).
#
# D_q(X,e) := Delta_q(X,e)/X^e = sum_{l<=N,(l,q)=1} c_l G_l(e) - P_q(e) Z(e),   N = [X],
#   c_l = mu(l)/l,  G_l(e) = int_{log l}^{log X} exp(-e u) du  (decreasing in e, G' increasing),
#   P_q(e) = prod_{p|q} (1-p^{-1-e})^{-1} (decreasing),  Z(e) = 1/(e zeta(1+e)) = 1/(1+e zd(1+e)),
#   zd(s) = zeta(s) - 1/(s-1) (deflated zeta).  At e=0: G=log(X/l), Z=1, so D(X,0)=F_1(X)-q/phi(q).
# For X in [N,N+1) D is monotone in X (coefficient of X^-e is -m_q(N)/e), so the sup over the cell is
# at X*=N if m_q(N)<=0 and X*->(N+1)^- (or 10.9) if m_q(N)>0.  Primes of q that are > X only enter P_q
# and make D smaller, so the worst q in a class is the one listed below (see REPORT.md).
#
# Over an e-cell [lo,hi]:  if a certified enclosure of D' on the cell has a sign, sup D = D(endpoint);
# otherwise sup D <= D(mid) + (hi-lo)/2 * sup|D'|.  Cells are bisected until sup D <= threshold.
# Enclosure of D' on a cell: sum c_l G_l' via monotonicity of G_l' (G_l''>0) at the endpoints;
#   (P Z)' by ball arithmetic, where zd and zd' on the cell are enclosed by their values at the
#   midpoint (Arb, exact point) +- h*sup|zd'|/2, +- h*sup|zd''|/2 with the ELEMENTARY bounds
#   |zd'(s)| <= 2/s, |zd''(s)| <= 4/s^2 (s>=1), from zd(s) = 1 - s J(s), J(s)=int_1^oo {t} t^{-s-1} dt,
#   |J^{(k)}(s)| <= k!/s^{k+1}.   (Arb's deflated zeta on *wide* balls is too pessimistic, so we do
#   not evaluate it on balls; only at exact points.)
import sys, os, itertools, time
from fractions import Fraction as Fr
from flint import arb, arb_series, fmpq, ctx

PREC = 192
ctx.prec = PREC
PR = [p for p in range(2, 60) if all(p % d for d in range(2, int(p**.5) + 1))]
def mobius(n):
    r, m = 1, n
    for p in PR:
        if p * p > m: break
        if m % p == 0:
            m //= p
            if m % p == 0: return 0
            r = -r
    if m > 1: r = -r
    return r
MU = {n: mobius(n) for n in range(1, 60)}
ZD1 = arb(2)   # sup_{s>=1} |zd'(s)|  (elementary, see header)
ZD2 = arb(4)   # sup_{s>=1} |zd''(s)|

def A(x):
    return arb(fmpq(x.numerator, x.denominator)) if isinstance(x, Fr) else arb(x)

def check_zd_points():
    """sanity: zd(1)=gamma, zd(1+e) = zeta(1+e)-1/e at e=1/10, Arb deflated series at exact points"""
    z0 = arb_series([arb(1)], 1).zeta(deflate=True).coeffs()[0]
    e = A(Fr(1, 10)); z1 = arb_series([1 + e], 1).zeta(deflate=True).coeffs()[0]
    return z0, arb.const_euler(), z1, (1 + e).zeta() - 1 / e

# ---------------- per-process caches ----------------
_Z = {}; _G = {}; _P = {}
def Zpt(e):           # (Z(e), zd(1+e), zd'(1+e)) at exact point e (Fraction)
    if e not in _Z:
        ea = A(e)
        co = arb_series([1 + ea, 1], 2).zeta(deflate=True).coeffs()
        zd, zdp = co[0], co[1]
        _Z[e] = (1 / (1 + ea * zd), zd, zdp)
    return _Z[e]
def Gpt(a, b, e):      # (G, G') at point e; a=log l, b=log X (arb); key by ids outside
    if e == 0:
        return b - a, -(b * b - a * a) / 2
    ea = A(e)
    G = (-ea * a).exp() * (-(-ea * (b - a)).expm1()) / ea
    Gd = -((-ea * a).exp() * (ea * a + 1) - (-ea * b).exp() * (ea * b + 1)) / (ea * ea)
    return G, Gd
def Ppt(p, e):         # (factor (1-p^{-1-e})^{-1}, log p/(p^{1+e}-1))
    k = (p, e)
    if k not in _P:
        ea = A(e)
        t = arb(p) ** (1 + ea)
        _P[k] = (t / (t - 1), arb(p).log() / (t - 1))
    return _P[k]

class Case:
    def __init__(self, N, Xstar, rprimes, extra):
        self.N = N; self.Xstar = Xstar
        self.ls = [l for l in range(1, N + 1) if MU[l] and all(l % p for p in rprimes)]
        self.c = [arb(MU[l]) / l for l in self.ls]
        self.sgn = [MU[l] for l in self.ls]
        self.b = A(Xstar).log()
        self.a = [arb(l).log() for l in self.ls]
        self.qp = list(rprimes) + list(extra)
        self.key = (N, Xstar)
    def G(self, i, e):
        k = (self.key, self.ls[i], e)
        if k not in _G: _G[k] = Gpt(self.a[i], self.b, e)
        return _G[k]
    def P(self, e):
        P = arb(1); S = arb(0)
        for p in self.qp:
            f, s = Ppt(p, e); P *= f; S += s
        return P, S
    def D(self, e):
        Z = Zpt(e)[0]; P, _ = self.P(e)
        s = arb(0)
        for i in range(len(self.ls)): s += self.c[i] * self.G(i, e)[0]
        return s - P * Z
    def Dprime_bounds(self, lo, hi):
        lo_s = arb(0); up_s = arb(0)
        for i in range(len(self.ls)):
            gl, gh = self.G(i, lo)[1], self.G(i, hi)[1]   # G' increasing: G'(lo) <= G' <= G'(hi) <= 0
            if self.sgn[i] > 0:
                lo_s += self.c[i] * gl; up_s += self.c[i] * gh
            else:
                lo_s += self.c[i] * gh; up_s += self.c[i] * gl
        sumGp = lo_s.union(up_s)
        m = (lo + hi) / 2; hh = A((hi - lo) / 2)
        _, zdm, zdpm = Zpt(m)
        eb = A(lo).union(A(hi))
        zd_b = (zdm - hh * ZD1).union(zdm + hh * ZD1)
        zdp_b = (zdpm - hh * ZD2).union(zdpm + hh * ZD2)
        Z_b = 1 / (1 + eb * zd_b)
        Zp_b = -(zd_b + eb * zdp_b) * Z_b * Z_b
        P_b = arb(1); S_b = arb(0)
        for p in self.qp:
            t = arb(p) ** (1 + eb)
            P_b *= t / (t - 1); S_b += arb(p).log() / (t - 1)
        PZp_b = -P_b * S_b * Z_b + P_b * Zp_b
        Dp = sumGp - PZp_b
        return Dp.lower(), Dp.upper()

def sup_on(case, lo, hi, thr, depth_min=Fr(1, 2**36)):
    """returns (certified_sup_upper_bound_or_None, max_point_lower, ncells, fails)"""
    stack = [(lo, hi)]; ncell = 0; best_cert = None; best_pt = None; fails = []
    thr_a = A(thr)
    while stack:
        l, h = stack.pop()
        dl, dh = case.D(l), case.D(h)
        for v in (dl, dh):
            best_pt = v.lower() if best_pt is None else max(best_pt, v.lower())
        dpl, dpu = case.Dprime_bounds(l, h)
        if dpl >= 0:
            up = dh.upper()
        elif dpu <= 0:
            up = dl.upper()
        else:
            m = (l + h) / 2
            dm = case.D(m)
            up = (dm + A((h - l) / 2) * arb(max(abs(dpl), abs(dpu)))).upper()
        if up <= thr_a:
            ncell += 1
            best_cert = up if best_cert is None else max(best_cert, up)
        elif h - l < depth_min:
            fails.append((float(l), float(h), float(dl.mid()), float(dh.mid())))
            ncell += 1
        else:
            m = (l + h) / 2
            stack.append((m, h)); stack.append((l, m))
    return best_cert, best_pt, ncell, fails

def m_exact(N, rprimes):
    return sum((Fr(MU[l], l) for l in range(1, N + 1) if MU[l] and all(l % p for p in rprimes)), Fr(0))

def worker(task):
    claim, N, Xlo_hi, items, Emin, Emax, thr = task
    out = []
    for rprimes, extra in items:
        m = m_exact(N, rprimes)
        Xstar = Xlo_hi[1] if m > 0 else Xlo_hi[0]
        case = Case(N, Xstar, rprimes, extra)
        # initial cells: width <= 1/32
        K = max(1, int((Emax - Emin) * 32))
        cert = None; pt = None; nc = 0; fails = []
        for k in range(K):
            l = Emin + (Emax - Emin) * Fr(k, K); h = Emin + (Emax - Emin) * Fr(k + 1, K)
            c_, p_, n_, f_ = sup_on(case, l, h, thr)
            if c_ is not None: cert = c_ if cert is None else max(cert, c_)
            pt = p_ if pt is None else max(pt, p_)
            nc += n_; fails += f_
        q = 1
        for p in list(rprimes) + list(extra): q *= p
        out.append((claim, N, q, str(Xstar), float(m), None if cert is None else (float(cert), cert.str(12, radius=False)),
                    (float(pt), pt.str(12, radius=False)), nc, fails))
    return out

def subsets(ps):
    for k in range(len(ps) + 1):
        for s in itertools.combinations(ps, k):
            yield s

def build_tasks():
    EXC = {1, 11, 13, 17}
    T = []
    def chunked(claim, N, Xs, items, Emin, Emax, thr, size=256):
        for i in range(0, len(items), size):
            T.append((claim, N, Xs, items[i:i + size], Emin, Emax, thr))
    # (a) X<10.9, e<=4/25, all q
    for N in range(1, 11):
        ps = [p for p in PR if p <= N]
        Xs = (Fr(N), Fr(N + 1)) if N < 10 else (Fr(10), Fr(109, 10))
        chunked('a', N, Xs, [(s, ()) for s in subsets(ps)], Fr(0), Fr(4, 25), Fr(0))
    # (b) X<47, (q,P43) not in EXC; split e in [0,1/10] and [1/10,1]
    for N in range(1, 47):
        ps = [p for p in PR if p <= N]
        items = []
        for s in subsets(ps):
            r = 1
            for p in s: r *= p
            if r not in EXC: items.append((s, ()))
            elif N < 43: items.append((s, (43,)))
        Xs = (Fr(N), Fr(N + 1))
        chunked('b1', N, Xs, items, Fr(0), Fr(1, 10), Fr(0))
        chunked('b2', N, Xs, items, Fr(1, 10), Fr(1), Fr(0))
    # (c) X<=47, (q,P43)=1: worst q=1; threshold 0.014
    for N in range(1, 48):
        Xs = (Fr(N), Fr(N + 1)) if N < 47 else (Fr(47), Fr(47))
        T.append(('c', N, Xs, [((), ())], Fr(0), Fr(1), Fr(14, 1000)))
        T.append(('c_tight', N, Xs, [((), ())], Fr(0), Fr(1), Fr(31, 10000)))
    # (d) X<47, (q,P43) in {11,13,17}: worst q=Q; test the stronger threshold 0 (implies 0.00005)
    for N in range(1, 47):
        Xs = (Fr(N), Fr(N + 1))
        for Q in (11, 13, 17):
            it = [((Q,), ())] if Q <= N else [((), (Q,))]
            T.append(('d0', N, Xs, it, Fr(0), Fr(1), Fr(0)))
    return T

if __name__ == '__main__':
    import multiprocessing as mp
    t0 = time.time()
    z0, g, z1, z1b = check_zd_points()
    print('sanity: zd(1) =', z0.str(15), ' gamma =', g.str(15), ' zd(1.1) =', z1.str(15), ' zeta(1.1)-10 =', z1b.str(15), flush=True)
    tasks = build_tasks()
    if len(sys.argv) > 1:
        tasks = [t for t in tasks if t[0] in sys.argv[1].split(',')]
    print('tasks:', len(tasks), 'cases:', sum(len(t[3]) for t in tasks), flush=True)
    res = []
    with mp.Pool(15) as pool:
        for i, r in enumerate(pool.imap_unordered(worker, tasks, chunksize=1)):
            res.extend(r)
            if i % 50 == 0: print('  progress %d/%d  %.0fs' % (i, len(tasks), time.time() - t0), flush=True)
    summary = {}
    for claim, N, q, Xs, m, cert, pt, nc, fails in res:
        s = summary.setdefault(claim, dict(n=0, cells=0, fails=[], maxcert=None, maxpt=None, argcert=None, argpt=None, uncert=0))
        s['n'] += 1; s['cells'] += nc
        if fails: s['fails'].append((N, q, Xs, fails[:3]))
        if cert is None: s['uncert'] += 1
        elif s['maxcert'] is None or cert[0] > s['maxcert'][0]: s['maxcert'] = cert; s['argcert'] = (N, q, Xs)
        if s['maxpt'] is None or pt[0] > s['maxpt'][0]: s['maxpt'] = pt; s['argpt'] = (N, q, Xs)
    desc = {'a': 'X<10.9, e in [0,4/25], all q: Delta/X^e <= 0',
            'b1': 'X<47, (q,P43) not in {1,11,13,17}, e in [0,1/10]: Delta/X^e <= 0',
            'b2': 'X<47, (q,P43) not in {1,11,13,17}, e in [1/10,1]: Delta/X^e <= 0',
            'c': 'X<=47, (q,P43)=1, e in [0,1]: Delta/X^e <= 0.014',
            'c_tight': 'X<=47, (q,P43)=1, e in [0,1]: Delta/X^e <= 0.0031',
            'd0': 'X<47, (q,P43) in {11,13,17}, e in [0,1]: Delta/X^e <= 0 (stronger than 0.00005)'}
    for k in ['a', 'b1', 'b2', 'c', 'c_tight', 'd0']:
        if k not in summary: continue
        s = summary[k]
        status = 'CERTIFIED' if not s['fails'] and s['uncert'] == 0 else 'NOT CERTIFIED'
        print('[%s] %s' % (k, desc[k]))
        print('    %s : %d cases, %d cells; max certified upper bound %s at (N,q,X*)=%s; max point value (lower bd) %s at %s' % (
            status, s['n'], s['cells'], None if s['maxcert'] is None else s['maxcert'][1],
            s['argcert'], None if s['maxpt'] is None else s['maxpt'][1], s['argpt']))
        for f in s['fails'][:10]: print('    FAIL', f)
    print('total time %.0fs' % (time.time() - t0))
