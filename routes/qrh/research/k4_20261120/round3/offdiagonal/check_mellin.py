"""Independent direct Gamma contour evaluation at unit, half and double product scales."""
from flint import arb, acb, ctx


def run():
    ctx.prec = 224
    pi = arb.pi()
    t = arb(6*10**12)
    u0 = t/(2*pi)
    sigma = arb(7)/8
    branches = (sigma, 1-sigma)
    base = {a.str(): 2*acb(a/2,t/2).lgamma().real for a in branches}
    n = [int((factor*u0).floor().unique_fmpz()) for factor in (arb(1)/2,arb(1),arb(2))]
    sums = {(i,j): arb(0) for i in range(2) for j in range(len(n))}
    log_n = [arb(v).log() for v in n]
    order = 32
    for panel in range(60):
        for node in range(order):
            root, weight = arb.legendre_p_root(order,node,weight=True)
            u = (2*panel+1+root)/8
            z = acb(1,u)
            g = (z*z).exp()
            for a in branches:
                for sgn in (-1,1):
                    g *= 1-(z/acb(a,sgn*t))**2
            for i,a in enumerate(branches):
                logratio = (acb(a/2,t/2)+z/2).lgamma()+(acb(a/2,-t/2)+z/2).lgamma()
                logratio -= base[a.str()]+z*pi.log()
                for j,ln in enumerate(log_n):
                    integrand = (logratio-z*ln).exp()*g/z
                    sums[i,j] += weight*integrand.real/(8*pi)
    # Per-unit unsymmetrized integrand before 1/pi. Analytic sup < 200
    # in the radius-1/2 discs. Two-sided Taylor error for the 15 units.
    trunc = 30*200*(arb(1)/4)**(2*order)/(1-arb(1)/4)/pi
    tail = arb(10)*(-arb(15)**2/2).exp() + (-t/2).exp()
    radius = (trunc+tail).upper()
    for i,a in enumerate(branches):
        for j,v in enumerate(n):
            main = ((arb(v)/u0).log()/2).erfc()/2
            diff = sums[i,j]-main+arb(0,radius)
            assert abs(diff) < 1300/t**2 and not diff.contains(0)
            print("a",a.str(5),"mn",v,"actual Gamma minus erfc",diff.str(15))


if __name__ == "__main__":
    run()
