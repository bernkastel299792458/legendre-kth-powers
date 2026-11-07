"""
Lemma C (rigorous, Arb): the factor 2 in Bellotti (4.6).

For zeros rho_r, rho_s with alpha <= beta_r, beta_s <= 1 - nu, put z = 2 - rho_r - conj(rho_s) = y - i a,
y = 2 - beta_r - beta_s in [2 nu, 2 delta] (delta = 1 - alpha), a = gamma_r - gamma_s, and Y = U/L^2 < X.
Then
 (i)  |X^z - Y^z| <= X^y (1 + (Y/X)^y) <= X^{2 delta} (1 + kappa),     kappa := (Y/X)^{2 nu};
 (ii) |Gamma(z) (X^z - Y^z)| <= Gamma(1+y) (X^y - Y^y)/y <= X^{2 delta} (1 - (Y/X)^{2 delta}) / (2 delta).
Bellotti uses |X^z - Y^z| <= 2 X^{2 - 2 alpha}. Consequences (relative factors):
  c3, c4  ->  c3 (1+kappa)/2, c4 (1+kappa)/2
  c2      ->  c2 * (1 - (Y/X)^{2(1-alpha0)}) / (2 * 1.0067)      [reviewer fix: no (1+kappa)/2 branch]
with kappa, (Y/X)^{2(1-alpha0)} maximised over log T in the row (rigorous below).
"""
import math
from flint import arb, ctx
from lemmaB_count import nu_of, f_up, f_down

ctx.prec = 100


def log_X_over_Y(u, x, L):
    """log(X/Y) = (x-u) L + 2 log L   (X = T^x, Y = U/L^2 = T^u/L^2)."""
    return (x - u) * L + 2 * L.log()


def kappa_upper(u, x, nu_name, L0, L1, steps=400):
    """rigorous sup_{L in [L0,L1]} exp(-2 nu(L) log(X/Y))."""
    u = arb(str(u)); x = arb(str(x))
    worst = 0.0
    for i in range(steps):
        a = L0 + (L1 - L0) * i / steps; b = L0 + (L1 - L0) * (i + 1) / steps
        L = arb(0.5 * (a + b), 0.5 * (b - a) * (1 + 1e-12))
        val = (-2 * nu_of(nu_name, L) * log_X_over_Y(u, x, L)).exp()
        worst = max(worst, f_up(val))
    return arb(worst)


def diag_factor_upper(u, x, alpha0, L0, L1, steps=50):
    """rigorous sup over the row of (1 - (Y/X)^{2(1-alpha0)}) / (2 * 1.0067)."""
    u = arb(str(u)); x = arb(str(x)); d = 1 - arb(str(alpha0))
    worst = 0.0
    for i in range(steps):
        a = L0 + (L1 - L0) * i / steps; b = L0 + (L1 - L0) * (i + 1) / steps
        L = arb(0.5 * (a + b), 0.5 * (b - a) * (1 + 1e-12))
        val = (1 - (-2 * d * log_X_over_Y(u, x, L)).exp()) / (2 * arb("1.0067"))
        worst = max(worst, f_up(val))
    return arb(worst)


def residue_factors(u, x, alpha0, nu_name, L0, L1):
    """returns (f2, f34): multiply Bellotti's c2 by f2 and c3, c4 by f34."""
    if nu_name == "ford":
        assert float(L1) <= 172, "monotonicity of nu_ford certified only on [28,172]"
    k = kappa_upper(u, x, nu_name, L0, L1)
    f34 = (1 + k) / 2
    # reviewer fix: the (1+kappa)/2 option for c2 needs Bellotti's monotonicity step (2 nu log X >= 1),
    # which can fail; only the Lemma C (ii) factor is used for c2.
    f2 = diag_factor_upper(u, x, alpha0, L0, L1)
    return f2, f34, k


if __name__ == "__main__":
    from bellotti_rows import rows
    for r in rows:
        if r["L1"] > 170.3:
            break
        nm = "classical" if r["L1"] <= 46.2 + 1e-9 else "ford"
        f2, f34, k = residue_factors(r["u"], r["x"], r["alpha0"], nm, r["L0"], r["L1"])
        c2, c3, c4 = r["c2"], r["c3"], r["c4"]
        tot = (c2 * f_up(f2) + (c3 + c4) * f_up(f34)) / (c2 + c3 + c4)
        print(f"[{r['L0']:7.2f},{r['L1']:6.1f}] {nm:9s} kappa<={f_up(k):.4f}  f34<={f_up(f34):.4f}  f2<={f_up(f2):.4f}  => factor on (c2+c3+c4): {tot:.4f}")
