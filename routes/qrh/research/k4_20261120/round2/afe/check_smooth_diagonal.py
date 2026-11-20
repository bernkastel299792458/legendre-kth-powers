"""Arb upper sums for the uniform smooth-diagonal bound in README.md."""

from math import isqrt

from flint import acb, arb, ctx


def primes_through(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def arithmetic_majorant(r_min, delta, limit):
    product = arb(1)
    for prime in primes_through(limit):
        p = arb(prime)
        product *= 1 + (p ** (-1 - r_min) + p ** (-2 + 2 * delta)) / (1 - 1 / p.sqrt()) ** 2
    n = arb(limit)
    tail = (n ** (-r_min) / r_min + n ** (-1 + 2 * delta) / (1 - 2 * delta))
    tail /= (1 - 1 / n.sqrt()) ** 2
    return product * tail.exp()


def integral_majorant(r_min, r_max, delta, cells_per_unit):
    eta = arb(1) / 2 - delta
    total = arb(0)
    for k in range(10 * cells_per_unit):
        lo = arb(k) / cells_per_unit
        hi = arb(k + 1) / cells_per_unit
        imag = arb((hi + lo) / 2, (hi - lo) / 2)
        sigma = arb(1 - (r_min + r_max) / 2 - 2 * delta, (r_max - r_min) / 2)
        zeta_bound = abs(acb(sigma, 2 * imag).zeta()).upper()
        direct = ((r_max + delta) ** 2).exp() / ((r_min + delta) ** 2 + lo ** 2).sqrt()
        reflected = (delta ** 2).exp() / (delta ** 2 + lo ** 2).sqrt()
        moebius = arb(1).max((delta ** 2 + hi ** 2) / eta ** 2)
        total += (direct + reflected) * moebius * zeta_bound * (-(lo ** 2)).exp()
    return total / cells_per_unit


def main():
    ctx.prec = 160
    delta = arb(7) / 20
    minimum_height = arb(3) * 10**12
    u_min = minimum_height / (2 * arb.pi())
    worst = arb(0)
    upper_strip = arb(0)
    for i in range(80, 150):
        r_min, r_max = arb(i) / 200, arb(i + 1) / 200
        e_bound = arithmetic_majorant(r_min, delta, 100000)
        integral = integral_majorant(r_min, r_max, delta, 128)
        # The polynomial correction is at most 1.001 for |Im z| <= 10.
        # The central gamma quotient is at most 5/4 times U^(-r-delta).
        coefficient = 2 * e_bound / arb.pi() * (arb(5) / 4) * (arb(1001) / 1000)
        coefficient = coefficient * integral + arb("1e-14")
        assert e_bound < 232
        worst = worst.max(coefficient)
        if i >= 140:
            upper_strip = upper_strip.max(coefficient)
    print("Coefficient of U^(-r-delta)", worst)
    print("Coefficient of U^(-r) at minimum height", worst / u_min ** delta)
    print("Upper-strip coefficient of U^(-r-delta)", upper_strip)
    print("Upper-strip coefficient of U^(-r) at minimum height", upper_strip / u_min ** delta)
    assert worst < 6490
    assert worst / u_min ** delta < arb(531) / 1000
    assert upper_strip < 3274
    assert upper_strip / u_min ** delta < arb(268) / 1000


if __name__ == "__main__":
    main()
