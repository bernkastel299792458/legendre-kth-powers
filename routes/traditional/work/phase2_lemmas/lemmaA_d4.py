"""
Lemma A (rigorous, Arb): a new upper bound for Bellotti's d4,

    d4 >= S := sum_{n>=1} Psi(n)^2/n * (e^{-n/X} - e^{-n L^2/U}),

where Psi(n) = sum_{d|n} psi_d with the Barban-Vehov weights
psi_d = mu(d) * min(1, log^+(V/d)/log(V/U)),  U = T^u, V = T^v, X = T^x, L = log T.

Proof outline (see REPORT.md, Lemma A, for the full proof):
 (1) n = 1 contributes w(1) = e^{-1/X} - e^{-L^2/U} <= L^2/U ; Psi(n)=0 for 1<n<=U.
 (2) Rankin: for n>U, e^{-n/X} <= (eps X/e)^eps n^{-eps}; so
        S <= L^2/U + (eps X/e)^eps (zeta(1+eps) Q(eps) - 1),
     Q(eps) = sum_{d,e} psi_d psi_e [d,e]^{-1-eps}  (and zeta(s)Q = sum_n Psi(n)^2 n^{-s}).
 (3) NEW: Selberg diagonalisation + mu*1_{(.,delta)=1} = mu * 1_{delta^infty} + Cauchy-Schwarz
     + the bijection n <-> (rad n, n/rad n) give
        Q(eps) <= Delta^{-2} sum_{n<=V} n^{-1-eps} H(n)^2,
        H(n) = M1(V/n) - M1(U/n),  M1(y) = sum_{m<=y} mu(m) m^{-1-eps} log(y/m) (0 if y<1),
     Delta = log(V/U).
 (4) M1(y) = A + B log y + R(y),  B = 1/zeta(s), A = -zeta'(s)/zeta(s)^2, with
     |R(y)| <= rbar(y) for y >= 15 from Ramare & Zuniga-Alterman, "Moebius function (and primes):
     an identity factory with applications", arXiv:2312.05138v3, Thm 1.8 (label mcheckqeps), q = 1:
        |R(y)| <= 2^eps y^{-eps} [0.0336 * 1_{y>=1e12}/log y + (4.86+2.93+2.83 eps log y + 5.17 eps)/sqrt(y)],
     valid for sigma = 1+eps in [1, 11/10] and y >= 15;
     and M1(y) computed exactly (Arb) for 1 <= y <= Y0 (piecewise monotone between integers).
 (5) The sum over n is bounded blockwise (n^{-s} decreasing => sum <= integral over [a-1,b]).

Everything below is Arb (python-flint) except: table values are stored as IEEE doubles that are
outward-rounded certified bounds (lower bounds rounded down, upper bounds rounded up), and range
minima/maxima of such doubles are exact.

Validity of the inputs used: eps in (0, 0.1]; Y0 >= 15; U/N1 >= Y0 (checked); Delta >= log Y0 (checked).
"""
import math, os, time
import numpy as np
from flint import arb, arb_series, ctx

ctx.prec = 110
HERE = os.path.dirname(os.path.abspath(__file__))

def f_down(x):
    """rigorous double lower bound of arb x"""
    f = float(x.lower())
    return math.nextafter(f, -math.inf)

def f_up(x):
    f = float(x.upper())
    return math.nextafter(f, math.inf)

def mobius_sieve(N):
    mu = np.ones(N + 1, dtype=np.int8)
    isp = np.ones(N + 1, dtype=bool); isp[:2] = False
    for p in range(2, int(N ** 0.5) + 1):
        if isp[p]:
            isp[p * p::p] = False
    primes = np.nonzero(isp)[0]
    for p in primes:
        mu[p::p] *= -1
        pp = int(p) * int(p)
        if pp <= N:
            mu[pp::pp] = 0
    mu[0] = 0
    return mu

_MU = {}
def get_mu(N):
    if N not in _MU:
        _MU[N] = mobius_sieve(N)
    return _MU[N]


class M1Data:
    """Certified data for M1(y; eps) = sum_{m<=y} mu(m) m^{-1-eps} log(y/m)."""

    def __init__(self, eps_str, Y0=1_000_000, verbose=False):
        self.eps_str = eps_str
        self.eps = arb(eps_str)
        assert 0 < float(self.eps) <= 0.1
        self.sigma = 1 + self.eps
        self.Y0 = Y0
        assert Y0 >= 15
        zc = arb_series([self.sigma, 1], prec=2).zeta().coeffs()
        self.zeta = zc[0]
        self.zetap = zc[1]
        self.B = 1 / self.zeta
        self.A = -self.zetap / self.zeta ** 2
        self.logY0 = arb(Y0).log()
        self.log1e12 = arb(10) ** 12
        self.log1e12 = self.log1e12.log()
        self._table(verbose)
        # r_big at the 1e12 threshold (used in the monotone majorant below 1e12)
        self.rb12 = self._r_big(self.log1e12)

    def _table(self, verbose):
        t0 = time.time()
        Y0 = self.Y0
        mu = get_mu(Y0)
        lo = np.zeros(Y0 + 1); hi = np.zeros(Y0 + 1)
        Plo = np.zeros(Y0 + 1); Phi = np.zeros(Y0 + 1); Qlo = np.zeros(Y0 + 1); Qhi = np.zeros(Y0 + 1)
        P = arb(0); Q = arb(0); s = self.sigma
        for k in range(1, Y0 + 1):
            lk = arb(k).log()
            m = mu[k]
            if m != 0:
                t = (-s * lk).exp()
                if m > 0:
                    P += t; Q += t * lk
                else:
                    P -= t; Q -= t * lk
            v = P * lk - Q          # = M1(k)
            lo[k] = f_down(v); hi[k] = f_up(v)
            Plo[k] = f_down(P); Phi[k] = f_up(P); Qlo[k] = f_down(Q); Qhi[k] = f_up(Q)
        # M1 is continuous and, on [k,k+1], monotone (linear in log y with slope P_k), so its
        # range on [k,k+1] is [min(v_k,v_{k+1}), max(v_k,v_{k+1})].
        self.vlo, self.vhi = lo, hi
        self.Plo, self.Phi, self.Qlo, self.Qhi = Plo, Phi, Qlo, Qhi
        if verbose:
            print(f"  table eps={self.eps_str} Y0={Y0} built in {time.time()-t0:.1f}s")

    # ---- analytic error term  (Ramare--Zuniga-Alterman, identity factory, Thm mcheckqeps, q=1)
    def _r_small(self, ly):
        e = self.eps
        return arb(2) ** e * (-(e + arb(1) / 2) * ly).exp() * (arb("7.79") + arb("2.83") * e * ly + arb("5.17") * e)

    def _r_big(self, ly):
        e = self.eps
        return arb(2) ** e * (-e * ly).exp() * (arb("0.0336") / ly) + self._r_small(ly)

    def rbar(self, ly_lo):
        """upper bound of |R(y)| valid for ALL y with log y >= ly_lo (requires ly_lo >= log 15).
        monotone majorant of the paper's bound."""
        ly = arb(f_down(arb(ly_lo)))
        assert float(ly) >= math.log(15)
        if ly.upper() < self.log1e12.lower():
            a = self._r_small(ly); b = self.rb12
            return arb(max(f_up(a), f_up(b)))
        else:
            return self._r_big(arb(min(f_down(ly), f_down(ly))))

    # ---- certified range of M1(y) for log y in [l_lo, l_hi]
    def range_log(self, l_lo, l_hi):
        """returns (lo, hi) arb such that lo <= M1(y) <= hi for all y with log y in [l_lo, l_hi]."""
        a = f_down(arb(l_lo)); b = f_up(arb(l_hi))
        lo = math.inf; hi = -math.inf
        if a < 0:                     # y < 1 possible: M1 = 0
            lo = min(lo, 0.0); hi = max(hi, 0.0)
        lY0 = math.log(self.Y0)
        if b >= 0 and a <= f_up(self.logY0):   # table part, y in [max(1,e^a), min(Y0,e^b)]
            ya = math.exp(max(a, 0.0)) * (1 - 1e-12)
            yb = math.exp(min(b, lY0)) * (1 + 1e-12)
            ya = max(ya, 1.0); yb = min(yb, float(self.Y0))
            ia = int(math.floor(ya)); ib = int(math.floor(yb))
            # interior integer points m with ia < m <= ib : M1(m) = v_m
            if ib > ia:
                lo = min(lo, float(self.vlo[ia + 1:ib + 1].min()))
                hi = max(hi, float(self.vhi[ia + 1:ib + 1].max()))
            # end points: on [k,k+1), M1(y) = P_k log y - Q_k (monotone), so the range over the
            # partial end pieces lies between the value at ya (resp. yb) and the integer points.
            for yy in (ya, yb):
                k = min(int(math.floor(yy)), self.Y0)
                Pk = arb(self.Plo[k]).union(arb(self.Phi[k]))
                Qk = arb(self.Qlo[k]).union(arb(self.Qhi[k]))
                val = Pk * arb(yy).log() - Qk
                lo = min(lo, f_down(val)); hi = max(hi, f_up(val))
        lo_a = arb(lo) if lo != math.inf else None
        hi_a = arb(hi) if hi != -math.inf else None
        if b > lY0 * (1 - 1e-14):          # analytic part, log y in [max(a, logY0), b]
            ll = max(a, f_down(self.logY0))
            ll = arb(ll)
            r = self.rbar(ll)
            alo = self.A + self.B * ll - r
            ahi = self.A + self.B * arb(b) + r
            lo_a = alo if lo_a is None else arb(min(f_down(lo_a), f_down(alo)))
            hi_a = ahi if hi_a is None else arb(max(f_up(hi_a), f_up(ahi)))
        return lo_a, hi_a


def grid(a, b, h_fine, b_fine, h_coarse):
    """list of block endpoints covering [a, b]: step h_fine up to b_fine, then h_coarse (floats, exact as arb)."""
    pts = [a]
    x = a
    while x < b:
        h = h_fine if x < b_fine else h_coarse
        x = min(b, x + h)
        pts.append(x)
    return pts


def T_bound(D, u, v, La, Lb, N1=100_000, h_fine=0.01, h_coarse=0.25):
    """Upper bound, valid for all L in [La, Lb], of
         Delta^{-2} * sum_{n<=V} n^{-sigma} H(n)^2    (>= Q(eps) by step (3)).
    u, v, La, Lb : arb.   D : M1Data."""
    e = D.eps; s = D.sigma
    Da = (v - u) * La; Db = (v - u) * Lb
    lN1 = arb(N1).log()
    assert f_down(u * La - lN1) >= math.log(D.Y0), "need U/N1 >= Y0"
    assert f_down(Da) >= math.log(D.Y0), "need V/U >= Y0"
    B = D.B; A = D.A
    lY0 = float(D.logY0)
    # --- region 0 : n <= N1
    r0 = D.rbar(v * La - lN1) + D.rbar(u * La - lN1)
    eta0 = (B + r0 / Da) ** 2
    sum0 = 1 + (1 - (-e * lN1).exp()) / e
    tot0 = sum0 * eta0
    # --- region I : N1 < n <= U, w = log(U/n) in [0, wmax]
    wmax = f_up(u * Lb - lN1)
    pts = grid(0.0, wmax, h_fine, lY0 + 1.0, h_coarse)
    SI = arb(0); etaI_max = arb(0); sum_ew = arb(0)
    for wa, wb in zip(pts[:-1], pts[1:]):
        wa_ = arb(wa); wb_ = arb(wb)
        c = ((e * wb_).exp() - (e * wa_).exp()) / e
        if wa >= lY0:
            rr = D.rbar(Da + wa_) + D.rbar(wa_)
            eta = (B + rr / Da) ** 2
        else:
            # H = A + B(Delta + w) + R(V/n) - M1(U/n), so H/Delta = B + K/Delta with
            # K in [A + B wa - r - uhi, A + B wb + r - ulo], r = rbar(Da + wa) >= |R(V/n)|.
            ulo, uhi = D.range_log(wa_, wb_)                # M1(U/n)
            r = D.rbar(Da + wa_)
            Klo = f_down(A + B * wa_ - r - uhi); Khi = f_up(A + B * wb_ + r - ulo)
            qa = [arb(Klo) / Da, arb(Klo) / Db, arb(Khi) / Da, arb(Khi) / Db]
            qlo = min(f_down(q) for q in qa); qhi = max(f_up(q) for q in qa)
            m = max(abs(f_down(B + arb(qlo))), abs(f_up(B + arb(qhi))))
            eta = arb(m) ** 2
        SI += c * eta
        etaI_max = arb(max(f_up(etaI_max), f_up(eta)))
        sum_ew += wb_.exp()
    UmE = (-e * u * La).exp()          # U^{-eps} <= this
    # correction  sum_j (a_j - 1)^{-s} eta_j <= eta_max * sum_j 2/a_j ,  a_j = U e^{-w_{j+1}} >= 2
    # (a_j - 1)^{-s} <= 2/a_j needs a_j >= 2 (reviewer nit): a_j >= U e^{-wmax} = N1 e^{u(L - Lb)}
    assert f_down(lN1 - u * (Lb - La)) >= math.log(2)
    corrI = etaI_max * 2 * sum_ew / (u * La).exp()
    totI = UmE * SI + corrI
    # --- region II : U < n <= V, w' = log(V/n) in [0, Db]
    pts2 = grid(0.0, f_up(Db), h_fine, lY0 + 1.0, h_coarse / 5)
    SII = arb(0); etaII_max = arb(0); sum_ew2 = arb(0)
    for wa, wb in zip(pts2[:-1], pts2[1:]):
        wa_ = arb(wa); wb_ = arb(wb)
        c = ((e * wb_).exp() - (e * wa_).exp()) / e
        vlo, vhi = D.range_log(wa_, wb_)                    # M1(V/n)
        ulo, uhi = D.range_log(wa_ - Db, wb_ - Da)          # M1(U/n)
        Hlo = vlo - uhi; Hhi = vhi - ulo
        m = max(abs(f_down(Hlo)), abs(f_up(Hlo)), abs(f_down(Hhi)), abs(f_up(Hhi)))
        eta = arb(m) ** 2 / Da ** 2
        SII += c * eta
        etaII_max = arb(max(f_up(etaII_max), f_up(eta)))
        sum_ew2 += wb_.exp()
    VmE = (-e * v * La).exp()
    corrII = etaII_max * 2 * sum_ew2 / (v * La).exp()
    totII = VmE * SII + corrII
    tot = tot0 + totI + totII
    return tot, dict(tot0=tot0, totI=totI, totII=totII)


def d4_bound_piece(D, u, v, x, La, Lb, **kw):
    """Rigorous upper bound for S (Bellotti's d4 quantity) valid for all log T in [La, Lb]."""
    e = D.eps
    T, parts = T_bound(D, u, v, La, Lb, **kw)
    zQ = D.zeta * T
    w1 = Lb ** 2 / (u * La).exp()
    rank = (e / arb(1).exp()) ** e * (e * x * Lb).exp()
    val = w1 + rank * (zQ - 1)
    return val, dict(zQ=zQ, rank=rank, **parts)


def d4_upper(u, v, x, logT_lo, logT_hi, eps_list=None, piece=0.25, Y0=1_000_000, verbose=False):
    """Rigorous Arb upper bound for d4 valid uniformly for log T in [logT_lo, logT_hi].
    u, v, x : decimal strings (or numbers);  returns (arb_upper_bound, details)."""
    u = arb(str(u)); v = arb(str(v)); x = arb(str(x))
    lo = float(logT_lo); hi = float(logT_hi)
    npieces = max(1, int(math.ceil((hi - lo) / piece - 1e-9)))
    edges = [lo + (hi - lo) * i / npieces for i in range(npieces + 1)]
    if eps_list is None:
        # eps ~ a / log X with a ~ 2 (near-optimal in the model); a few candidates
        lX = float(x) * 0.5 * (lo + hi)
        eps_list = sorted(set(f"{a / lX:.5f}" for a in (1.8, 2.05, 2.3)))
    # choose (Y0, N1) so that the hypotheses U/N1 >= Y0 and V/U >= Y0 of T_bound hold on the range
    uL = float(u) * lo; dL = (float(v) - float(u)) * lo
    N1 = None
    for Y0c in (Y0, 100_000, 10_000, 1_000):
        if Y0c > Y0 or math.log(Y0c) > dL - 1e-6:
            continue
        N1c = min(100_000, int(math.exp(uL - math.log(Y0c) - 1e-3)))
        if N1c >= 100:
            Y0, N1 = Y0c, N1c
            break
    if N1 is None:
        raise ValueError("Lemma A implementation needs u*logT >= log(100*Y0) and (v-u)*logT >= log(Y0) with Y0>=1000")
    Ds = [M1Data(es, Y0=Y0, verbose=verbose) for es in eps_list]
    worst = None; det = []
    for La_, Lb_ in zip(edges[:-1], edges[1:]):
        La = arb(La_); Lb = arb(Lb_)
        best = None
        for D in Ds:
            val, info = d4_bound_piece(D, u, v, x, La, Lb, N1=N1)
            ub = f_up(val)
            if best is None or ub < best[0]:
                best = (ub, D.eps_str, info)
        det.append((La_, Lb_, best[0], best[1], f_up(best[2]["zQ"])))
        if verbose:
            print(f"  L in [{La_:.3f},{Lb_:.3f}]: d4 <= {best[0]:.4f} (eps={best[1]}, zeta*Q <= {f_up(best[2]['zQ']):.5f})")
        worst = best[0] if worst is None else max(worst, best[0])
    return arb(worst), det


if __name__ == "__main__":
    import sys
    rows = [  # L0, L1, u, x, v  (Bellotti Table 4)
        (math.log(3e12), 29, "2.1781287", "7.0798370", "4.4744028"),
    ]
    for (L0, L1, uu, xx, vv) in rows:
        t0 = time.time()
        b, det = d4_upper(uu, vv, xx, L0, L1, verbose=True)
        print(f"rows [{L0:.3f},{L1}] : d4 <= {b}   ({time.time()-t0:.1f}s)")
