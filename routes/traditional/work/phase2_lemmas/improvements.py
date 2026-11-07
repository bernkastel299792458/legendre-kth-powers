"""
Phase-2 interface: rigorous replacements for three ingredients of Bellotti's log-free density
estimate (arXiv:2405.12545v2).  All functions marked RIGOROUS return python-flint `arb` upper bounds
computed with Arb (python-flint 0.9.0).  See REPORT.md for statements, proofs and input status.

Status tags (see REPORT.md):
  Lemma A (d4)        : our own lemma; inputs: Ramare--Zuniga-Alterman "identity factory"
                        (arXiv:2312.05138v3, Thm mcheckqeps, published Math. Comp. 2026) -- only for the
                        tiny error term R(y), y >= 1e6.
  Lemma B (box count) : our own lemma; inputs: Heath-Brown PLMS 1992 Lemma 3.2; Thorner--Zaman
                        Forum Math. 2024, bound for -J inside the proof of Prop. 2.11; Delange 1987.
  Lemma C (factor 2)  : our own lemma; elementary (+ zero-free region nu).
  Lemma D (round 2)   : our own lemma; the mollifier of the zero detector on Re s = 1/2 (c1, Lemma 3.4).
                        Inputs: none beyond elementary counting (constants certified in Arb).
  Lemma B-W (round 2) : our own lemma; Weyl-exponent version of TZ's -J bound. Inputs: Rademacher's
                        Phragmen-Lindelof lemma (Math. Z. 1959), Hiary-Patel-Yang 0.618 t^{1/6} log t and
                        Patel-Yang 66.7 t^{27/164} (as quoted in Bellotti Lemma 2.5), TZ's arcs J1,J2,J4,J5.

----------------------------------------------------------------------------------------------
RIGOROUS functions
  d4_upper(u, v, x, logT_lo, logT_hi, piece=0.25) -> arb
      Upper bound for  sum_n Psi(n)^2/n (e^{-n/X} - e^{-n L^2/U})  (Bellotti Lemma 4.2's d4),
      U=T^u, V=T^v, X=T^x, uniformly for log T in [logT_lo, logT_hi].
      Validity: 0 < u < v, x > 0 arbitrary;  needs u*logT_lo >= log(1e11) (=25.33) and
      (v-u)*logT_lo >= log(1e6); the Rankin exponent eps = a/(x log T) must be <= 0.1 (automatic).
      Cost: ~1 s per piece of width 0.25 in log T plus ~4 s per eps table.
  cf_upper(alpha0, nu, logT_lo, logT_hi, hfac=1) -> arb
      Upper bound for sup_{delta in [nu(T), 1-alpha0]} #Box(delta)/(delta log T) over log T in the
      range, Box = [1-delta,1] x [t0 - hfac*delta/2, t0 + hfac*delta/2] (hfac=1: Bellotti's (4.1)
      boxes).  Replaces Bellotti's  b1 + b2/(nu(T0) log T0)  in  C = (c2+c3+c4)(b1+b2 Z)/(c1^2-c5).
      nu: "classical" (Z1=5.558691), "ford" (Bellotti (2.2)), "littlewood" (21.233), or a callable
      arb->arb giving nu(L) (must be a valid zero-free region width at height e^L, decreasing in L).
      Validity: 3e12 <= t0 - hfac*delta/2, t0 + hfac*delta/2 <= T; uses r = rho*delta < 1/2.
  count_upper(alpha0, nu, logT_lo, logT_hi, hfac=1) -> (b1, b2)
      Affine form: #Box(delta) <= b1*delta*log T + b2 for all delta in [nu(T), 1-alpha0].
  residue_factors(u, x, alpha0, nu, logT_lo, logT_hi) -> (f2, f34, kappa)
      Multiply Bellotti's c2 by f2 and c3, c4 by f34 (replaces the factor 2 in (4.6)).
      kappa = sup (U/(L^2 X))^{2 nu(T)} over the row.
  pair_residue_bound(...)   documented per-pair inequality (Lemma C (i),(ii)) for re-use.

NON-RIGOROUS helper (for parameter search only)
  d4_model(u, v, x, L, a=2.05) -> float   closed-form model of the Lemma-A bound (typically within
      +-5% of d4_upper; never use it in a claimed bound).
----------------------------------------------------------------------------------------------
"""
import math
from flint import arb
import lemmaA_d4 as _A
import lemmaB_count as _B
import lemmaC_residue as _C


def d4_upper(u, v, x, logT_lo, logT_hi, piece=0.25, eps_list=None, verbose=False):
    """RIGOROUS (Lemma A).  See module docstring."""
    b, _ = _A.d4_upper(u, v, x, logT_lo, logT_hi, eps_list=eps_list, piece=piece, verbose=verbose)
    return b


def cf_upper(alpha0, nu, logT_lo, logT_hi, hfac=1, weyl=False):
    """RIGOROUS (Lemma B; with weyl=True also Lemma B-W, the Weyl-exponent bound for -J)."""
    cf, _ = _B.cf_upper(alpha0, nu, logT_lo, logT_hi, hfac=hfac, weyl=weyl)
    return cf


def count_upper(alpha0, nu, logT_lo, logT_hi, hfac=1):
    """RIGOROUS (Lemma B, affine form, TZ's J-bound)  -> (b1, b2)."""
    b1, b2, cf, det = _B.b1b2_upper(alpha0, nu, logT_lo, logT_hi, hfac=hfac)
    return b1, b2


def mollifier_half_line_KD(u, v, w, logT_lo, logT_hi=None):
    """RIGOROUS (Lemma D, round 2): for all real t and all log T in [logT_lo, logT_hi],
         |M(1/2+it)| <= sum_{v,w} |psi_v||theta_w| [v,w]^{-1/2} <= K_D (VW)^{1/2},
    with K_D <= 4 c^2 P* / ((v-u) w logT_lo^2),  c = Q(7)/sqrt 7, P* = prod_p (1+p^{-3/2}-p^{-2}).
    Plug-in: in Bellotti (3.11)/(3.17) and Phase 0's c1 (belarb.piece_v2: SU and the E312/E313 terms),
    replace the factor D2VW = sum_{n<=VW} d(n)^2/n (which multiplies (VW)^{1/2}) by this K_D.
    Validity: 0 < u < v, w > 0 (U = T^u >= 1, W = T^w > 1)."""
    import lemmaD_mollifier as _D
    return _D.KD_upper(u, v, w, logT_lo, logT_hi)


def residue_factors(u, x, alpha0, nu, logT_lo, logT_hi):
    """RIGOROUS (Lemma C) -> (f2, f34, kappa)."""
    return _C.residue_factors(u, x, alpha0, nu, logT_lo, logT_hi)


def pair_residue_bound(X_log, Y_log, y_lo, y_hi, absz_lo):
    """RIGOROUS per-pair bound (Lemma C) for z = y - i a with y in [y_lo, y_hi] (0 < y_lo, y_hi <= 1),
    |z| >= absz_lo, 0 < log Y < log X:
        |Gamma(z)(X^z - Y^z)| <= min( 1.0067 X^{y_hi} (1 + (Y/X)^{y_lo}) / |z| ,  (X^{y_hi} - Y^{y_hi}) / y_hi ).
    (the constant 1.0067 is Bellotti's (4.8), valid for 0 < y <= 2 - 2*alpha0 <= 0.03.)
    Arguments arb; returns arb."""
    X_log = arb(X_log); Y_log = arb(Y_log)
    b1 = arb("1.0067") * (y_hi * X_log).exp() * (1 + (y_lo * (Y_log - X_log)).exp()) / absz_lo
    b2 = ((y_hi * X_log).exp() - (y_hi * Y_log).exp()) / y_hi
    return arb(min(_A.f_up(b1), _A.f_up(b2)))


def d4_model(u, v, x, L, a=2.05):
    """NOT RIGOROUS.  Model of the Lemma-A bound:
       (eps X/e)^eps * exp(-eps*Lu) (1 - exp(-eps*D)) / (eps*D)^2 * 1.04,  eps = a/(x L)."""
    Lu = u * L; D = (v - u) * L; lX = x * L; e = a / lX
    rank = math.exp(e * lX) * (e / math.e) ** e
    return 1.04 * rank * math.exp(-e * Lu) * (1 - math.exp(-e * D)) / (e * D) ** 2


if __name__ == "__main__":
    # smoke test on Bellotti's first row
    import math
    u, v, x = "2.1781287", "4.4744028", "7.0798370"
    print("d4_upper  :", d4_upper(u, v, x, math.log(3e12), 29))
    print("d4_model  :", d4_model(2.1781287, 4.4744028, 7.0798370, 29))
    print("cf_upper  :", cf_upper(0.9927, "classical", math.log(3e12), 29))
    print("count_up  :", count_upper(0.9927, "classical", math.log(3e12), 29))
    print("residue   :", residue_factors(2.1781287, 7.0798370, 0.9927, "classical", math.log(3e12), 29))
