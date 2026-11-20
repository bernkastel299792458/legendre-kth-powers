"""Check the example bounding the omitted sharp residue tails in README.md."""

from math import isqrt

from flint import acb, arb, ctx


def primes_through(limit):
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            sieve[p * p :: p] = bytes((limit - p * p) // p + 1)
    return [p for p in range(2, limit + 1) if sieve[p]]


def product_majorants(s, r, primes, limit):
    c_prod = arb(1)
    e_prod = arb(1)
    for prime in primes:
        p = arb(prime)
        f = 1 / (1 - p ** (s - 1))
        c_prod *= 1 + (f - 1) / p
        e_prod *= 1 + f / p ** (1 + r)
    n = arb(limit)
    inflation = 1 / (1 - n ** (s - 1))
    c_log_tail = inflation * n ** (s - 1) / (1 - s)
    e_log_tail = inflation * n ** (-r) / r
    return c_prod * c_log_tail.exp(), e_prod * e_log_tail.exp()


def main():
    ctx.prec = 160
    limit = 10000
    r = arb(3) / 4
    t = arb(3) * 10**12
    u = t / (2 * arb.pi())
    s = arb(1) / 2
    c, e = product_majorants(s, r, primes_through(limit), limit)
    # For X <= 10^14, Helfgott gives A=sqrt(2), B=0.
    common = 4 * arb(2).sqrt() * c * e / u ** (s / 2)
    direct = common * (2 + 1 / (2 * r + s))
    reflected = common * (2 + 1 / s)
    sigma = (1 + r) / 2

    def completed_gamma_product(real_part):
        gamma_value = (acb(real_part, t) / 2).gamma()
        return arb.pi() ** (-real_part) * abs(gamma_value) ** 2

    reflected_multiplier = completed_gamma_product(1 - sigma) / completed_gamma_product(sigma)
    gamma_scale = u ** r * reflected_multiplier
    joint = (1 + r).zeta() * direct + gamma_scale * abs((1 - r).zeta()) * reflected
    for label, val in (("C_1/2 majorant", c), ("E_1/2 majorant", e),
                       ("U^r abs(H_r) majorant", direct), ("abs(H_0) majorant", reflected),
                       ("normalized reflected gamma factor", gamma_scale),
                       ("combined normalized sharp tail majorant", joint)):
        print(f"{label}: {val}")
    assert joint < arb(968) / 1000

    b = 2 - 2 * sigma
    ratio = arb(2) ** (-b)
    a = 1 + arb(8).log()
    c_log = 2 * arb(2).log()
    series = (a * a / (1 - ratio) + 2 * a * c_log * ratio / (1 - ratio) ** 2
              + c_log ** 2 * ratio * (1 + ratio) / (1 - ratio) ** 3)
    near_factor = (1 + 2 * arb(3).zeta()) * 4 ** (2 * sigma) * 2 ** (b / 2) * series
    print(f"Lemma 3 near-term upper coefficient: {near_factor}")
    assert near_factor < 45438


if __name__ == "__main__":
    main()
