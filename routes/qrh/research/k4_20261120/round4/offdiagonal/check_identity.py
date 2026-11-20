"""Independent Arb checks on the archimedean identity and arithmetic factor."""
from math import gcd
from flint import arb, acb, ctx, fmpz


def arch(t, u):
    sigma = arb(7)/8
    w = acb(sigma+arb(7)/20,u)
    s = 2*w-1
    it = acb(0,t)
    pi = arb.pi()

    def log_h(a):
        return -a*pi.log()+((a+it)/2).lgamma()+((a-it)/2).lgamma()

    first = ((1-w-it).lgamma()-(w-it).lgamma()).exp()
    second = ((1-w+it).lgamma()-(w+it).lgamma()).exp()
    left = (log_h(w)-log_h(1-w)).exp()*s.zeta()*s.gamma()*(first+second)
    j = (pi*t).cosh()/((pi*t).cosh()-(pi*w).cos())
    right = (1-s).zeta()*j
    assert (left-right).contains(0)
    assert abs(left-right)<arb("1e-40")
    print("t", t.str(8), "u", u.str(5), "|J-1|", abs(j-1).str(13))


def arithmetic():
    sigma, z = arb(7)/8, acb(arb(7)/20,arb(9)/10)
    r, cutoff = 2*sigma-1, 40
    mu = [0]+[int(fmpz(k).moebius_mu()) for k in range(1,cutoff+1)]
    first = acb(0)
    second = acb(0)
    for d in range(1,cutoff+1):
        for e in range(1,cutoff+1):
            g = gcd(d,e)
            first += mu[d]*mu[e]*acb(g)**(1-r-2*z)/acb(d*e)**(1-z)
    for g in range(1,cutoff+1):
        for a in range(1,cutoff//g+1):
            for b in range(1,cutoff//g+1):
                if gcd(a,b)==1:
                    second += mu[g*a]*mu[g*b]*acb(a*b)**(z-1)/arb(g)**(2*sigma)
    assert (first-second).contains(0) and abs(first-second)<arb("1e-40")
    assert arb(".533564")/(arb(3)/4)+arb(".28858")+arb(".000000019") < 1
    print("grouped arithmetic factor",second.str(15))


if __name__ == "__main__":
    ctx.prec = 224
    arch(arb("1.5"),arb(".3"))
    arch(arb(30),arb("1.75"))
    arch(arb(3*10**12),arb("1.75"))
    arithmetic()
