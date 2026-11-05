"""
Harness: run the k = 67 certificate machinery (proof/code/rigorous_smooth.py, rigorous_hyb.py)
under a *modified* zero-free region (ZFR), without touching the original files.

How the ZFR enters the proof
----------------------------
Both Prop. S (rigorous_smooth.Phi_upper -> eta_low_at(vb)) and Prop. H
(rigorous_hyb.rig_delta -> eta_lower(U)) use ONE number per evaluation: a rigorous lower
bound eta for the zero-free width that holds *uniformly* for all zeros with
H_R < |gamma| <= e^V (V = top of the v-cell, resp. top of the u-range).
With the original constants this is eta_base(V) = max(1/(Z1 V), log V/(Z2 V),
1/(Z3 V^{2/3} (log V)^{1/3})), valid because each branch decreases for V > e.

A modified ZFR is described here by
  * the constants (Z1, Z2, Z3); a constant set to None drops that branch;
  * optionally one band (v_lo, v_hi, s), 0 < s <= 1: the pointwise width is s * eta_base(v)
    for v in (v_lo, v_hi] and eta_base(v) elsewhere.
The quantity the proof needs is the uniform width up to height e^V:
  eta_unif(V) = inf_{log H_R <= v <= V} eta_mod(v)
              = eta_base(V)                                  if V <= v_lo,
              = s * eta_base(V)                              if v_lo < V <= v_hi,
              = min(eta_base(V), s * eta_base(v_hi))         if V > v_hi
(eta_base is decreasing on v >= log H_R).  We return a rigorous arb lower bound of it.

Everything else (density estimates, explicit formula, cells, Abel summation) is the
unchanged certified code, so every delta returned here is a rigorous upper bound under the
stated hypothetical ZFR.

Usage: import this module; call install(model) in every process (see worker_init).
"""
import os
import sys
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
CODE = os.path.normpath(os.path.join(HERE, '..', '..', 'code'))
CERT = os.path.normpath(os.path.join(HERE, '..', '..', 'certificates'))
if CODE not in sys.path:
    sys.path.insert(0, CODE)

from flint import arb, ctx  # noqa: E402
import rigorous_hyb as RH  # noqa: E402
import rigorous_smooth as RS  # noqa: E402

LOG_HR = RH.LOG_HR
K67 = 67
L1 = Fraction(2089605, 1024)      # top of Lemma 6 (CHL) range
L2 = Fraction(14315405, 2048)     # current S/H junction
L3 = Fraction(10 ** 8)            # start of Lemma T


def af(fr):
    fr = Fraction(fr)
    return arb(fr.numerator) / fr.denominator


class ZModel:
    """Picklable description of a (hypothetical) zero-free region."""

    def __init__(self, Z1="4.896", Z2="19.62", Z3="54.004", band=None, z2prof=None):
        self.Z1, self.Z2, self.Z3 = Z1, Z2, Z3
        self.band = None if band is None else tuple(Fraction(x) for x in band)  # (v_lo, v_hi, s)
        # optional height-dependent Littlewood constant: ((v_0, "Z2_0"), (v_1, "Z2_1"), ...), v_0 = 0;
        # Z2(v) = Z2_j on [v_j, v_{j+1}).  Overrides Z2 and band.
        self.z2prof = None if z2prof is None else tuple((Fraction(v), str(z)) for v, z in z2prof)

    def key(self):
        return (self.Z1, self.Z2, self.Z3, self.band, self.z2prof)

    def __repr__(self):
        b = '' if self.band is None else f", band=({float(self.band[0])}, {float(self.band[1])}, s={float(self.band[2])})"
        if self.z2prof is not None:
            b += ", Z2 profile=" + ", ".join(f"[{float(v):g},..):{z}" for v, z in self.z2prof)
            return f"ZModel(Z1={self.Z1}, Z3={self.Z3}{b})"
        return f"ZModel(Z1={self.Z1}, Z2={self.Z2}, Z3={self.Z3}{b})"

    # ---- rigorous pieces ----
    def _consts(self):
        c = getattr(self, '_c', None)
        if c is None:
            c = tuple(None if z is None else arb(z) for z in (self.Z1, self.Z2, self.Z3))
            self._c = c
        return c

    def eta_base(self, V):
        """arb ball containing eta_base(V) is not needed; we return the max of the branch
        lower endpoints (a rigorous lower bound, as in the original code)."""
        z1, z2, z3 = self._consts()
        lv = V.log()
        cands = []
        if z1 is not None:
            cands.append((1 / (z1 * V)).lower())
        if z2 is not None:
            cands.append((lv / (z2 * V)).lower())
        if z3 is not None:
            cands.append((1 / (z3 * V ** (arb(2) / 3) * lv ** (arb(1) / 3))).lower())
        return max(cands, key=float)

    def _eta_piece(self, V, z2):
        z1, _, z3 = self._consts()
        lv = V.log()
        cands = [(lv / (arb(z2) * V)).lower()]
        if z1 is not None:
            cands.append((1 / (z1 * V)).lower())
        if z3 is not None:
            cands.append((1 / (z3 * V ** (arb(2) / 3) * lv ** (arb(1) / 3))).lower())
        return max(cands, key=float)

    def _affects_prof(self, Vlo, Vhi):
        """Conservative float test for profile models: eta_unif can differ from eta_base(Z2 = self.Z2) only
        above the first piece whose constant differs, and only until eta_base drops below the smallest
        right-end value of the modified pieces."""
        cache = getattr(self, '_aff', None)
        if cache is None:
            pr = self.z2prof
            mods = [j for j, (v, z) in enumerate(pr) if z != self.Z2]
            if not mods:
                cache = (float('inf'), float('inf'))
            else:
                vfirst = float(pr[mods[0]][0])
                if any(j + 1 >= len(pr) for j in mods):
                    vstar = float('inf')
                else:
                    target = min(float(self._eta_piece(af(pr[j + 1][0]), pr[j][1])) for j in mods)
                    vstar = max(float(pr[j + 1][0]) for j in mods)
                    while float(self.eta_base(arb(vstar))) > target * (1 - 1e-12) and vstar < 1e8:
                        vstar *= 1.01
                cache = (vfirst, vstar * 1.01)
            self._aff = cache
        vfirst, vstar = cache
        return Vhi > vfirst and Vlo <= vstar

    def eta_unif_prof(self, V):
        """Profile model: on each piece [v_j, v_{j+1}) the width max(classical, log v/(Z2_j v), VK) is
        decreasing, so inf over [log H_R, V] = min over pieces meeting [log H_R, V] of the value at
        min(V, v_{j+1}) (right limit of the piece)."""
        best = None
        pr = self.z2prof
        for j, (vj, zj) in enumerate(pr):
            vnext = pr[j + 1][0] if j + 1 < len(pr) else None
            if vnext is not None and vnext <= Fraction(28):    # piece entirely below log H_R: irrelevant
                continue
            if af(vj) >= V and j > 0:
                break
            end = V if (vnext is None or af(vnext) >= V) else af(vnext)
            e = self._eta_piece(end, zj)
            if best is None or float(e) < float(best):
                best = e
        return best

    def eta_unif(self, V):
        """Rigorous lower bound for inf_{log H_R <= v <= V} eta_mod(v). V: exact arb point."""
        if self.z2prof is not None:
            return self.eta_unif_prof(V)
        base = self.eta_base(V)
        if self.band is None:
            return base
        vlo, vhi, s = self.band
        if s >= 1:
            return base
        A_lo, A_hi, A_s = af(vlo), af(vhi), af(s)
        if V <= A_lo:            # exact points: comparison is decisive
            return base
        if V <= A_hi:
            return (A_s * base).lower()
        other = (A_s * self.eta_base(A_hi)).lower()
        return base if float(base) <= float(other) else other   # both are valid lower bounds; take min

    def affects(self, Vlo, Vhi):
        """Conservative float test: can eta_unif differ from eta_base somewhere on [Vlo, Vhi]?"""
        if self.z2prof is not None:
            return self._affects_prof(Vlo, Vhi)
        if self.band is None:
            return True
        vlo, vhi, s = (float(x) for x in self.band)
        if s >= 1 or Vhi <= vlo:
            return False
        # above v_hi the band matters until eta_base(V) <= s * eta_base(v_hi)
        vstar = getattr(self, '_vstar', None)
        if vstar is None:
            target = float(self.eta_base(af(self.band[1]))) * s
            vstar = vhi
            while float(self.eta_base(arb(vstar))) > target * (1 - 1e-12) and vstar < 1e8:
                vstar *= 1.01
            self._vstar = vstar
        return Vlo <= vstar * 1.01


_MODEL = {'m': None}


def install(model):
    """Patch the two eta functions of the certified code to use `model`."""
    RS.CFG['zfr'] = 'lw'
    RS.CFG['full_table'] = True
    RH.HYB_CFG['zfr'] = 'lw'
    _MODEL['m'] = model
    RS.eta_low_at = lambda Vb: model.eta_unif(Vb)
    RH.eta_lower = lambda U, z_hyp=None: model.eta_unif(U)


_WC = {}


def wconsts(M):
    if M not in _WC:
        _WC[M] = RS.weight_constants(M)
    return _WC[M]


def smooth_delta(a, b, M):
    """Rigorous (pure-arb) upper bound for Prop. S delta on L in [a, b] (Fractions)."""
    d, det = RS.rig_delta_smooth_pure(K67, Fraction(a), Fraction(b), M, wconsts(M))
    if d is None:
        return float('inf')
    return d   # arb (exact upper endpoint)


def smooth_vrange(a, b, M):
    """Float estimate of the v-range [vstart, Vf] scanned by Prop. S on [a, b] (for `affects`)."""
    from math import log
    R_up, _ = wconsts(M)
    Lb, La = float(b), float(a)
    v0 = La / K67 - log(K67)
    v0b = Lb / K67 - log(K67)
    logA = [log(float(R_up[j])) + j * v0 for j in range(M + 1)]
    vstart = max(float(LOG_HR), min(logA[j] / j for j in range(1, M + 1)) - 0.5)
    Vf = max(max((logA[M] - logA[j]) / (M - j) for j in range(M)) + 1.0, v0b + 30, (logA[M] + 60) / (M - 1))
    return vstart, Vf + 1


def hyb_delta(a, b, c, sstar):
    d, det = RH.rig_delta(K67, Fraction(a), Fraction(b), Fraction(c), Fraction(sstar))
    return float('inf') if d is None else d


def worker_init(model_key):
    Z1, Z2, Z3, band = model_key[:4]
    z2prof = model_key[4] if len(model_key) > 4 else None
    install(ZModel(Z1, Z2, Z3, band, z2prof))
    # precision: rigorous_smooth sets ctx.prec = 128 on import (rigorous_hyb alone would use 160);
    # both are rigorous, 128 is what the Prop. S certificate check uses.
