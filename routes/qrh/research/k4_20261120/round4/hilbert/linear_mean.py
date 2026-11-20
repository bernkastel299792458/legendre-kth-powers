"""Short log windows and the exact folded interval for local linear frequencies."""

from fractions import Fraction
from functools import lru_cache
from math import prod

from flint import arb, ctx


# Entries are (coefficient of interval length, defect in units of pi/q).
BOUNDS = {
    2: {"unit": ("1", "1")},
    6: {"unit": ("1", "2")},
    30: {"unit": ("1", "8.405125"), "middle": ("1.05", "8.155125"),
         "density": ("1.082", "8")},
    210: {"unit": ("1", "54.691271"), "middle": ("1.15", "49.946683"),
          "density": ("1.274", "48")},
}


def as_arb(rational):
    return arb(rational.numerator) / rational.denominator


@lru_cache(maxsize=None)
def certify_fold(modulus, mode):
    """Check all partial-period Gram matrices. A successful check is precision independent."""
    slope, defect = map(Fraction, BOUNDS[modulus][mode])
    primes = [p for p in (2, 3, 5, 7) if modulus % p == 0]
    if prod(primes) != modulus or 2 not in primes or slope < 1:
        raise ValueError("expected an even squarefree modulus and slope >= 1")
    units = prod(p-1 for p in primes)
    period = modulus//2
    ramanujan = [prod(p-1 if h % p == 0 else -1 for p in primes)
                 for h in range(period)]
    for length in range(1, period+1):
        ceiling = slope*(length-1) + defect
        if min(length*units, period) <= ceiling:
            continue
        # The Fourier slice and its Gram transpose have equal nonzero spectra.
        rows = [[arb(-ramanujan[i-j]) for j in range(i)] + [as_arb(ceiling)-units]
                for i in range(length)]
        for k in range(length):
            pivot = rows[k][k]
            if not pivot > 0:
                raise ArithmeticError(f"no positive Schur pivot for q={modulus}, k={length}, i={k}")
            for i in range(k+1, length):
                factor = rows[i][k] / pivot
                for j in range(k+1, i+1):
                    rows[i][j] -= factor * rows[j][k]
    return slope, defect


def linear_mean_coefficients(modulus, min_height, ybar, mode="unit"):
    """Return diagonal, Hilbert coefficients for V>=min_height, with mean V=ybar*T."""
    slope, defect = certify_fold(modulus, mode)
    eps = arb(min_height)**(-arb(1)/5)
    mass = 1 - 4*eps/arb.pi()
    if not mass > 0:
        raise ValueError("sliding-window convolution needs positive mass")
    correction = ((1+eps)*eps*(2*eps**3).exp()).exp() / mass
    return (correction*(1+eps)*as_arb(slope)*ybar,
            correction*arb.pi()*as_arb(defect)/modulus)


if __name__ == "__main__":
    ctx.prec = 192
    for q, options in BOUNDS.items():
        for mode in options:
            slope, defect = certify_fold(q, mode)
            hilbert = arb.pi()*as_arb(defect)/q
            d, h = linear_mean_coefficients(q, arb(42).exp(), arb("1.01")*2048/2047, mode)
            print(q, mode, str(slope), hilbert.str(12), d.str(12), h.str(12), flush=True)
