"""What constant does the thesis's Chapter-3 argument actually give once the
main-term estimate (Lemma 3.8) is computed correctly?

INDICATIVE ONLY.  We keep every other step of the thesis (with the small
corrections found in check_constants.py / check_error_terms.py) and replace the
claimed 3.4431 by the coefficient c(t) that Lemmas 3.6/3.7 + (3.19)/(3.20)
really give.  Suprema over t and the per-t optimum over lambda are taken on
grids (float), so the output is an estimate, not a proof.

The final inequality (p. 78) reads
    A + eps < (I(mu0) - a1*loss_351 - C3max(A)) / (c_main(A) * w(0)),
I(mu0) = a1 W(1-mu0) - a0 W(-mu0) (exact integral, 0.938124),
loss_351 = corrected (3.51) loss, C3max(A) = max_t of (3.49)'s C3 with the
corrected Lemma 3.19 error term.

Run:  python -I check_corrected_constant.py > check_corrected_constant_output.txt
"""
import os, sys, math
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from common import *

ak = [float(x.mid()) for x in A_K]
a_sum = sum(ak[1:])
w0f = float(w0().mid())
g = float(GAMMA.mid())
I_MU0 = 0.938123515402          # check_constants.py
LOSS = 1.432e-5                 # a1 * 8.22e-6, check_constants.py ((3.51) corrected)
_x0 = SIGMA1 - arb('0.5')        # Lemma 2.7 redone with sigma >= sigma1, eta <= eta1, theta = 1.1272
COEF_T1 = float((C_ford(_x0 / ETA1, _x0 / ETA1) / PI / _x0 ** 2).mid())       # times (A+eps) L2
CB_ETA1 = float((C_ford(SIGMA1 / ETA1, SIGMA1 / ETA1) / _x0 ** 3 * ETA1).mid())
LK = [math.log(k) if k else 0.0 for k in range(K + 1)]


def sig(L, A):
    LL = L + math.log(K + 1e10 * math.exp(-L))
    return 1 - A * math.log(LL) / LL


def C3f(s): return 0.0728 * 2.50214 ** (14 * s / 3)


def coef(L, lam, A):
    """main-term coefficient c(t); returns None if sigma*-lambda outside [1/2, 5/6]."""
    s = sig(L, A); sl = s - lam
    if sl < 0.5 or lam >= 0.5 or s + lam - 1 <= 0:
        return None
    if sl <= 5 / 7: n = 3
    elif sl <= 5 / 6: n = 4
    else:
        n = 5
        while not (1 - n / (2 ** n - 2) <= sl <= 1 - (n + 1) / (2 ** (n + 1) - 2)): n += 1
    dn = 1 / ((n - 1) * 2 ** n + 2); mu = dn * (2 ** n * (1 - sl) - 1)
    lc = math.log(C3f(sl)) if n == 3 else math.log(1.549)
    tot = sum(ak[k] * (mu * (L + LK[k]) + math.log(L + LK[k]) + lc) for k in range(1, K + 1))
    x = s + lam - 1
    tot += ak[0] * (g * x - math.log(x))
    return tot / (2 * lam) * math.log(L) / L


def lam_thesis(L):
    L2 = math.log(L)
    if L < 216: return 1 / (8 - 24.2 / L2)
    if L < 225.4: return 1 / (16 - 67.19 / L2)
    return 2.248 * L2 ** 2 / L


def c_thesis(L, A): return coef(L, lam_thesis(L), A) if coef(L, lam_thesis(L), A) is not None else \
    coef(L, sig(L, A) - 0.5 - 1e-9, A)        # on [H1, e^57] use lambda = sigma* - 1/2 (Lemma 3.6 domain)


def c_opt(L, A):
    if L >= 225.4:
        return coef(L, lam_thesis(L), A)
    best = None
    lo, hi = 0.27790, 0.49999
    for i in range(0, 1101):
        lam = lo + (hi - lo) * i / 1100
        v = coef(L, lam, A)
        if v is not None and (best is None or v < best): best = v
    return best


GRID = [56.5 + 0.5 * i for i in range(int((225.4 - 56.5) / 0.5) + 1)] + [225.4 * 1.01 ** i for i in range(1, 900)]


def c_main(A, which):
    f = c_thesis if which == 'thesis' else c_opt
    best = (0, None)
    for L in GRID:
        if which == 'opt' and L > 400:     # beyond, c(t) < 3.33 (check_main_term.py)
            break
        v = f(L, A)
        if v > best[0]: best = (v, L)
    return best


def C3max(A):
    best = -1
    L = 56.5
    while L < 1e5:
        L2 = math.log(L)
        cE = a_sum * (COEF_T1 * (A + 1e-100) * L2 + CB_ETA1) * (A + 1e-100)
        v = (0.75 * L / L2 ** 2 + cE * L2 / L - 2.9) * (A + 1e-100) * L2 / L
        best = max(best, v)
        L *= 1.002
    return best


def solve(which):
    A = 1 / 19.62
    for it in range(30):
        cm, Lm = c_main(A, which)
        A_new = (I_MU0 - LOSS - C3max(A)) / (cm * w0f)
        if abs(A_new - A) < 1e-9: break
        A = A_new
    return A, cm, Lm


print("C3max(A1) with corrected Lemma 3.19 term =", round(C3max(1 / 19.62), 7), "(thesis 0.00452)")
for which in ['thesis', 'opt']:
    A, cm, Lm = solve(which)
    print(f"lambda = {which:6s}: sup_t c(t) = {cm:.5f} (at log t = {Lm:.1f});  largest A = {A:.6f}  ->  1/A = {1/A:.3f}")
print("(for comparison: with c = 3.4431 the same final step gives 1/A =",
      round(3.4431 * w0f / (I_MU0 - LOSS - C3max(1 / 19.62)), 3), ")")

print("\nPer-height 'local' constant 1/A(t) = c(t) w(0)/(I(mu0) - loss - C3max)  [sensitivity guide only;")
print(" a height-dependent constant is NOT what the thesis proves -- its induction uses one A for all t >= H1]")
den = I_MU0 - LOSS - C3max(1 / 20.1)
print(" log t   c_thesis  1/A(thesis lambda)   c_opt   1/A(opt lambda)")
for L in [56.5, 60, 65, 70, 76.5, 80, 90, 95.5, 100, 110, 120, 129, 140, 150, 160, 170, 190, 216, 225.4, 300, 1000, 1e4, 1e5, 4.8e5]:
    ct = c_thesis(L, 1 / 20.1)
    co = c_opt(L, 1 / 20.1) if L < 225.4 else ct
    print(f" {L:8.1f}  {ct:.4f}   {ct * w0f / den:7.3f}           {co:.4f}   {co * w0f / den:7.3f}")
