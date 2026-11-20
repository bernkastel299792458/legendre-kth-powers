"""BV right boundary with the pole of zeta separated explicitly.

Write V=log(T)>=U, e=2*delta/V, Y=T*exp(logh), X=Y*exp(W). The
hypotheses and the finite Möbius estimates are those of right/fine/PROOF.md.
The elementary bounds used here, for s=1+e>1, are

    1/e+1/2 <= zeta(1+e) <= 1/e+1/2+(1+e)/12.

Indeed, for t>0, 1/(1-exp(-t))=1/2+coth(t/2)/2 lies between 1/t+1/2
and 1/t+1/2+t/12. This follows from the partial fractions of coth, bounding
each 1/(t^2+4*pi^2*n^2) by 1/(4*pi^2*n^2). Multiply by
t^(s-1)*exp(-t)/Gamma(s) and integrate from zero to infinity.
"""

from pathlib import Path
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "right" / "fine"))
from verify_fine import A, check, finite_data, signed_high_norm, signed_low_norm


def sharp_right(U, delta, kap, W, logh):
    """Return the uniform K3 bound for V >= U and 0 < 2*delta/U <= 0.1."""
    check(U > 0 and delta > 0 and kap > 0 and W > 0 and logh < 0, "BV parameters")
    e_max = 2 * delta / U
    h = logh.exp()
    y_min = (U + logh).exp()
    check(e_max <= A(".1") and y_min > 2048, "verified BV domain")

    S, heads, mids, far_energy, signed_table = finite_data(W, y_min, True)
    shape = 1 / (1 + S) + 1 / (1 + y_min.log())**2 + 32 / y_min
    mobius_error = A(".011")
    local_error = mobius_error / (1 + arb(10**14).log())
    log_sum_cap = A("1.00303")
    high_base = signed_high_norm(h, W, y_min, e_max)

    pi = arb.pi()
    half = A("1/2")
    hilbert = pi * (1 + A("2/3") * A("6/5").sqrt()).sqrt()
    diagonal = pi.sqrt() / (2 * (2 * kap).sqrt()) + hilbert / (2 * U.exp())
    k3 = arb(0)
    for i in range(64):
        lower = e_max * i / 64
        upper = e_max * (i + 1) / 64
        pole_constant = half + (1 + upper) / 12
        reciprocal_min = lower / (1 + pole_constant * lower)
        reciprocal_max = upper / (1 + half * upper)

        signed_head, signed_mid = signed_low_norm(signed_table, lower, upper, W, y_min)
        head = sum(mass * (value + 2 * upper * tail + local_error)**2
                   for mass, value, tail in heads)
        head = head.min(signed_head)
        head += ((1 + upper * W) * far_energy.sqrt() / W
                 + 2 * mobius_error * shape.sqrt())**2

        # In the transition, b=1/zeta(1+e)-G_e(t)/W. Enclose these two
        # terms separately and retain the alternative signed estimate.
        mid = arb(0)
        for t, g0_min, g0_max, mass in mids:
            factor = (-upper * t).exp()
            g_min = factor * g0_min
            g_max = log_sum_cap * (1 + upper * t) - factor * (log_sum_cap - g0_max)
            absolute = (reciprocal_max - g_min / W).max(g_max / W - reciprocal_min)
            mid += mass * (-lower * (W - t)).exp() * absolute.max(arb(0))**2
        mid = mid.min(signed_mid)

        # zeta(1+e)/V <= (1+upper*pole_constant)/(2*delta).
        # Beyond X, one factor 1/zeta remains after the Selberg prefactor.
        # Integral plus endpoint gives sum_{j>X} j^(-1-e) <= X^(-e)(1/e+1/X).
        # Since 1/V=e/(2*delta), the coefficient is at most
        # reciprocal_max*(1+upper/y_min)/(2*delta) after extracting X^(-e).
        discount = (-2 * delta - upper * logh).exp()
        tail = (-lower * W).exp() * reciprocal_max * (1 + upper / y_min)
        low = discount * ((1 + pole_constant * upper) * (head + mid) + tail) / (2 * delta)

        # signed_high_norm bounded the sole zeta(2+e) prefactor by zeta(2).
        # Its coefficient bounds remain uniform on the entire e interval.
        high = discount * high_base * (2 + lower).zeta() / arb(2).zeta()
        k3 = k3.max(hilbert * low + diagonal * high * upper / (2 * delta))
    return k3


if __name__ == "__main__":
    from verify_fine import right_endpoint

    ctx.prec = 192
    ybar = A("1.01") * 2048 / 2047
    kappa = arb.pi() / (8 * ybar**2)
    args = (A("55.98"), A(".9"), kappa, A("10.7"), A("-4.85"))
    original = right_endpoint(*args, signed_high=True, signed_low=True)[0]
    result = sharp_right(*args)
    print("original K3", original.str(18))
    print("pole bound K3", result.str(18))
    check(result < original, "improved right endpoint")
