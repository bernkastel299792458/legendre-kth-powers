"""Pointwise bounds for (1+z)(1-z/2)^2(1+z^2/10)."""
from functools import lru_cache
from flint import arb, ctx


@lru_cache(maxsize=2)
def radial_caps(precision):
    assert precision == ctx.prec
    # For a fixed rectangle in |z| and cos(arg z), evaluate the polynomial
    # on the center radius; include the radial error on |P| using |P'|.
    c = arb(1)/10
    powers = [arb(k)/100 for k in (170,172,174,176,178)]
    r_min, r_max = arb(1)/8, arb(8)
    upper = [arb(0) for _ in powers]
    for j, nu in enumerate(powers):
        small = (arb(3)/4-c+r_min/4+3*c*r_min**2/4+c*r_min**3/4)*r_min**(2-nu)
        major = (1+r_max)*(1+r_max/2)**2*(1+c*r_max**2)
        assert nu*major.log()>5
        upper[j] = small.max(major.log()/r_max**nu)

    # Center-to-center radius ratio 1.003 and 512 equal cosine intervals.
    count = 512
    xs = [arb(2*i-count+1)/count for i in range(count)]
    dx = arb(1)/count
    lo = r_min
    while lo < r_max:
        hi = lo*arb(1003)/1000
        mid = (lo+hi)/2
        radial_error = (hi-lo)/2*((arb(3)/2-2*c)*hi+3*hi**2/4+3*c*hi**3+5*c*hi**4/4)
        top = arb(0)
        for x in xs:
            # At fixed radius all three factors of |P|^2 are nonnegative.
            first = 1+2*mid*(x+dx)+mid**2
            second = 1-mid*(x-dx)+mid**2/4
            third = 1+2*c*mid**2*(2*(abs(x)+dx)**2-1)+c**2*mid**4
            top = top.max(first*second**2*third)
        log_cap = ((top.upper().sqrt()+radial_error).log()).max(arb(0))
        for j, nu in enumerate(powers):
            upper[j] = upper[j].max(log_cap/lo**nu)
        lo = hi
    assert lo >= r_max
    return upper


def bound(lo, hi):
    ends = [arb(k)/100 for k in (170,172,174,176,178)]
    if not (lo>ends[0] and hi<ends[-1]):
        return None
    caps = radial_caps(ctx.prec)
    first = max(i for i, e in enumerate(ends) if e<lo)
    last = min(i for i, e in enumerate(ends) if e>hi)
    return caps[first].max(caps[last])


if __name__ == "__main__":
    ctx.prec = 192
    print([v.str(14) for v in radial_caps(ctx.prec)])
