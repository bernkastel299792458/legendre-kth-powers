"""Interval capacities for a periodic angular density with an empty gap."""
from flint import arb, ctx


def bounds(lo, hi, eta, log_min, local_jacobian=False):
    H, R = arb(3000175332800), arb("0.0001")
    pi = arb.pi()

    def d(L):
        return (4*(-L/4).exp()).log1p()/2

    short = 2*pi-2*H*d(lo)
    long = 2*pi-2*H*d(hi)
    assert 0 < short and long < 2*pi
    cmax = hi+d(lo)
    jacobian = (3*R/2).exp()/(lo-R)
    primary_jacobian = (R/2+2*pi/H).exp()/(lo-R) if local_jacobian else jacobian
    primary = primary_jacobian*(2*pi/short)*(cmax+R-H.log()+long.log()+eta)
    repeated = jacobian*(4*pi/(2*pi+short))*(cmax+R+(2*R).log()+eta)
    short_lengths = (R/2).exp()/(lo-R)*(2*pi/short)*(log_min+eta)
    return primary.max(repeated).max(short_lengths)


def verify():
    ctx.prec = 192
    old, new = arb("1.090"), arb("1.1328")
    cells = [bounds(arb(i)/1000, arb(i+1)/1000, old, 50) for i in range(115050,116000)]
    upper = max(cells)
    at116 = bounds(arb(116), arb(116), old, 50)
    assert upper < arb("1.9992") and at116 < arb("1.50137")
    assert arb(3)*(50+arb("1.09"))*(-arb(50)).exp() < arb(".000001")
    print("local continuous sieve numerator", upper.str(17), "at L=116", at116.str(17))

    H = arb(3000175332800)
    d = (4*(-arb(116)/4).exp()).log1p()/2
    s = 2*arb.pi()-2*H*d
    critical = 2*arb.pi()/s*(116-H.log()+s.log()+arb("1.090"))/116
    mode = 2*(H*d).sin()/s
    print("straight-coordinate critical numerator at 116", critical.str(17),
          "fundamental Fourier coefficient modulus", mode.str(16))

    cells = [bounds(arb(i)/1000, arb(i+1)/1000, new, 70, True)
             for i in range(115050,116000)]
    upper = max(cells)
    at116 = bounds(arb(116), arb(116), new, 70, True)
    assert upper < arb("1.999954") and at116 < arb("1.501934")
    assert 3*(70+new)*(-arb(70)).exp() < arb("1e-20")
    print("new denominator, localized Jacobian", upper.str(17), "at 116", at116.str(17))

    L = arb("115.049")
    d = (4*(-L/4).exp()).log1p()/2
    c = L+d
    b = H*d
    s = 2*arb.pi()-2*b
    v1 = (b+s)/H
    u = c+b/H+s.log()-H.log()
    lower = (2*arb.pi()/s)*(-v1/2).exp()/(c+v1)*(u+new)
    assert u > 70 and lower > arb("2.0006057") and v1 < arb("0.0001")
    assert 8*(u+new)*(-u).exp() < arb("1e-20")
    print("preceding grid point, actual arc numerator at least", lower.str(17))


if __name__ == "__main__":
    verify()
