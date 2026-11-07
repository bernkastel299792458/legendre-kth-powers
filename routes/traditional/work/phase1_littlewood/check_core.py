"""Independent sanity checks of the analytic ingredients used by zl_core.py (REPORT.md §4, §6).

These are NUMERICAL CHECKS of lemmas whose proofs are written out in REPORT.md (or cited); they are not themselves the
certificate.  Items marked [rigorous] are arb-rigorous statements used in the proof.

Run:  python -I check_core.py > check_core_output.txt
"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from zl_core import *
import mpmath as mp

mp.mp.dps = 15
NF = 0


def check(name, ok, detail=""):
    global NF
    if not ok:
        NF += 1
    print(f"[{'OK' if ok else 'FAIL'}] {name}  {detail}", flush=True)


# 1. w(0) closed form; G(0) = c0 of the thesis; a_k
w0_direct = w_acb(acb(0)).real
check("[rigorous] w(0) closed form = w_acb(0)", abs(w0_direct - W0) < arb('1e-30'), f"w(0) = {W0.str(15)}")
check("[rigorous] a_0 = 1, a = sum_{k>=1} a_k = 2919857/828465", A_FRAC[0] == 1 and sum(A_FRAC[1:]) == Fraction(2919857, 828465))
check("[rigorous] a_1 = 865534/497079", A_FRAC[1] == Fraction(865534, 497079))
G0 = G_of_mu(arb(0))
check("[rigorous] G(0) = int (a1 e^-u - a0) w = thesis c0 = 0.8219901343...", abs(G0 - arb('0.8219901343')) < arb('1e-10'),
      G0.str(12))
check("w(u) >= 0 on [0, d] (grid of 2001 points)",
      all(w_acb(acb(D_SUPP * j / 2000)).real > -arb('1e-25') for j in range(2001)))

# 2. Ford's W0 bound vs numerical W0 (sample points)
def W0_num(z):
    """W0(z) = int_0^d e^{-zu} w(u) du - w(0)/z, by acb.integral (z: complex python number)."""
    zz = acb(z.real, z.imag) if isinstance(z, complex) else acb(mp.re(z), mp.im(z))
    W = acb.integral(lambda u, an: (-zz * u).exp() * w_acb(u), 0, acb(D_SUPP))
    return complex(W - W0 / zz)


worst = 0
for nu, r in [(-1, 20), (-1, 50), (-1, 140), (0, 140), (150, 150)]:
    C = float(C_ford(arb(nu), arb(r)).mid())
    for ang in [0.0, 0.3, 0.7, 1.0, 1.3, 1.5]:
        for R in [r, 1.5 * r, 3 * r]:
            z = mp.mpc(max(nu, R * mp.cos(ang)), R * mp.sin(ang))
            if abs(z) < r:
                z = z * r / abs(z) * 1.0001
            val = abs(W0_num(complex(z))) * float(abs(z)) ** 3
            worst = max(worst, val / C)
check("Ford W0 bound |W0(z)||z|^3 <= C(nu, r) on sample points", worst < 1, f"max ratio = {worst:.4f}")

# 3. Fourier identity behind (3.19): int cos(w u)/cosh^2 u du = pi w / sinh(pi w / 2) in (0, 2]
mp.mp.dps = 40
for om in [0.1, 1.0, 5.0, 20.0]:
    lhs = mp.quad(lambda u: mp.cos(om * u) / mp.cosh(u) ** 2, mp.linspace(-60, 60, 1201))
    rhs = mp.pi * om / mp.sinh(mp.pi * om / 2)
    check(f"int cos({om} u) sech^2 u du = pi w/sinh(pi w/2) = {mp.nstr(rhs, 8)}", abs(lhs - rhs) < 1e-25 and 0 < rhs <= 2,
          f"|diff| = {mp.nstr(abs(lhs - rhs), 3)}")
mp.mp.dps = 15

# 4. digamma bound |Re psi(1/4 + i y/2)| <= log(|y|/2 + 4) + 10/3
ok4 = True
for y in [0, 0.1, 0.5, 1, 2, 5, 10, 100, 1e3, 1e5, 1e8, 1e20]:
    p = acb(arb(1) / 4, arb(y) / 2).digamma().real
    b = (arb(y) / 2 + 4).log() + PSI_EXTRA
    ok4 &= bool(abs(p) < b)
check("|Re psi(1/4+iy/2)| <= log(|y|/2+4) + 10/3 (sample points; proof via Binet, REPORT §4.5)", ok4)
# phi(t) = 1/(e^t-1) - 1/t + 1/2 in [0, t/12]
mp.mp.dps = 60
ok5 = all(0 <= (1 / (mp.e ** t - 1) - 1 / t + mp.mpf(1) / 2) <= t / 12 for t in [mp.mpf(10) ** (-k) for k in range(1, 8)] + [mp.mpf(x) for x in (0.5, 1, 2, 5, 10, 50)])
mp.mp.dps = 15
check("Binet: 0 <= 1/(e^t-1) - 1/t + 1/2 <= t/12 (sample points; classical)", ok5)

# 5. 1/u - cot u <= 0.36 u on (0, 1]: (1/u - cot u)/u has positive Taylor coefficients, value at 1 is 1 - cot 1
v1 = 1 - 1 / arb(1).tan()
check("[rigorous] 1/u - cot u <= 0.36u on (0,1]: value of (1/u-cot u)/u at u=1 is 1 - cot 1 =", v1 < arb('0.36'), v1.str(8))

# 6. Re W(iy) >= 0 (w is an autocorrelation g*g), sample points; boundary conditions of w (needed by Kadiri's Prop 2.1)
okW = True
for y in [0.5, 1, 2, 3, 5, 8, 13, 21, 50, 100]:
    Wiy = acb.integral(lambda u, an: (-acb(0, y) * u).exp() * w_acb(u), 0, acb(D_SUPP))
    okW &= bool(Wiy.real > 0)
check("Re W(iy) > 0 on sample points (Heath-Brown weight is an autocorrelation)", okW)
th = mp.mpf('1.1272'); dd = 2 * th / mp.tan(th)
def wf(u):
    tn = mp.tan(th); ct = 1 / tn; s2 = 1 / mp.cos(th) ** 2
    return s2 * (s2 * (th * ct - u / 2) * mp.cos(u * tn) + 2 * th * ct - u
                 + mp.sin(2 * th - u * tn) / mp.sin(2 * th) - 2 * (1 + mp.sin(th - u * tn) / mp.sin(th)))
mp.mp.dps = 60
th = mp.mpf('1.1272'); dd = 2 * th / mp.tan(th)
bc = [mp.diff(wf, 0, 1), wf(dd), mp.diff(wf, dd, 1), mp.diff(wf, dd, 2)]
mp.mp.dps = 15
check("w'(0) = w(d) = w'(d) = w''(d) = 0 (Kadiri Prop 2.1 hypotheses)", all(abs(x) < 1e-20 for x in bc),
      str([mp.nstr(x, 3) for x in bc]))

# 6b. Ford 2002 Lemma 4.4 as used in Lemma 3.16: Re(cot w - 1/w + 4w/pi^2) >= 0 on |w| = pi/2, Re w >= 0 (sample)
mn4 = min(float(mp.re(mp.cot(w) - 1 / w + 4 * w / mp.pi ** 2)) for w in
          [mp.pi / 2 * mp.exp(1j * mp.pi * (j / 400 - 0.5)) for j in range(401)])
check("Ford Lemma 4.4: Re(cot w - 1/w + 4w/pi^2) >= 0 on |w| = pi/2, Re w >= 0 (401 points)", mn4 >= -1e-12, f"min = {mn4:.3e}")

# 7. Lemma 3.7 on the line 1/2 at a moderate height (numerical): (1/2) int log|zeta(1/2+i(T+u d))| sech^2 u du
for T in [1000, 5000]:
    dl = 2 * 0.4965 / mp.pi
    val = mp.quad(lambda u: mp.log(abs(mp.zeta(mp.mpc(0.5, T + u * dl)))) / mp.cosh(u) ** 2, mp.linspace(-12, 12, 121)) / 2
    bound = mp.log(0.618) + mp.log(T) / 6 + mp.log(mp.log(T))
    check(f"Lemma 3.7 numerically at T = {T}: (1/2) int log|zeta| sech^2 = {mp.nstr(val, 6)} <= {mp.nstr(bound, 6)}", val <= bound)

# 8. comparison with fork A's main-term coefficient at log t = 60 (n = 3 line vs their optimised-lambda 3.3839)
r = cell_terms(arb(60), arb(60) + arb('1e-9'), arb('19.05'), arb('19.05'), 3, detail=True)
c60 = r[2]['B'] * ell(arb(60))
check("main-term coefficient c = B l(t) at log t = 60 with the n=3 line", abs(c60 - arb('3.3846')) < arb('0.001'),
      f"c = {c60.str(8)} (proof/zfr_audit/thesis_19.62: optimised lambda + Lemma 3.6 gives 3.3839)")

print("FAILURES:", NF)
sys.exit(NF)
