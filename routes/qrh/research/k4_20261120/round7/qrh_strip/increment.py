"""Uniform short-height counts on the true .865 rectangle."""
from math import comb, factorial, isqrt

from flint import arb

from strip_positive import PI, S, T, THETA, kernel, pair_positivity


C = arb("1.4")
LAM = arb(".4")
HILBERT = arb("4.2")


def coefficient(lp, k, A):
    v = k*lp
    return lp*((-THETA*v).exp()*(1-v/A)-LAM*(-C*v).exp())


def arithmetic(A,X):
    prime = bytearray([1])*(X+1)
    prime[:2] = bytes(2)
    for n in range(2,isqrt(X)+1):
        if prime[n]:
            prime[n*n::n] = bytes((X-n*n)//n+1)
    cutoff = int(A.exp().floor().unique_fmpz())
    small = arb(0)
    theta = arb(0)
    diags = [arb(0),arb(0)]
    for p in range(2,X+1):
        if not prime[p]:
            continue
        lp = arb(p).log()
        theta += lp
        powers = []
        n = p
        while n<=cutoff:
            powers.append(coefficient(lp,len(powers)+1,A))
            n *= p
        if p<=5:
            # Interpolate the maximum on a mesh in the prime's phase.
            grid = 256
            lower = arb(0)
            for j in range(grid+1):
                angle = PI*j/grid
                val = sum((v*((k+1)*angle).cos() for k,v in enumerate(powers)),arb(0))
                lower = lower.min(val)
            lip = sum(((k+1)*abs(v) for k,v in enumerate(powers)),arb(0))
            small += -lower + PI*lip/(2*grid)
        else:
            diags[0] += powers[0]**2
            diags[1] += p*powers[0]**2
            small += sum(map(abs,powers[1:]),arb(0))
    u = arb(X).log()
    decay = 2*THETA-1
    small += ((1+LAM)/(1-(-THETA*u).exp()))*(-decay*u).exp()*(u/decay+1/decay**2)
    return theta,diags,small


def long_norm(j,theta,A,X):
    u = arb(X).log()
    k = 1-2*THETA+j
    slope = 2*(C-THETA)
    G = lambda z:(1-z/A)**2+LAM**2*(-slope*z).exp()
    # On the last cell 1-z/A at the upper integration limit is exactly zero.
    bins = 4096
    step = (A-u)/bins
    total = arb(0)
    for i in range(bins):
        l = u+i*step
        r = u+(i+1)*step
        total += r*((k*l).max(k*r)).exp()*G(l)*step
    rs = arb("1.01624")
    f = u*((k-1)*u).exp()*G(u)
    return rs*total+(rs*X-theta)*f


def count_bound(A, X, width, D, b):
    A, width, D, b = map(arb,(A,width,D,b))
    mean_width = width+4/A
    assert 4*PI/3<HILBERT
    pair_positivity(A,LAM)
    theta,diag,small = arithmetic(A,X)
    j = 3
    coeff = [arb(comb(j,k))**2*b**(2*(j-k))*factorial(k) for k in range(j+1)]
    base = sum((v*diag[0]**k for k,v in enumerate(coeff)),arb(0))
    weighted = sum((v*diag[1]**k for k,v in enumerate(coeff)),arb(0))
    full = (mean_width+HILBERT)*base+HILBERT*weighted
    low = arb(4)/(27*(D+b)**2)*full.sqrt()
    hi0,hi1 = [long_norm(k,theta,A,X) for k in (0,1)]
    high = (((mean_width+HILBERT)*hi0+HILBERT*hi1)/2).sqrt()
    v = A-arb(".000001")
    assert v.exp()+1<A.exp()
    tail = LAM*(-(C-1)*v).exp()*(v/(C-1)+1/(C-1)**2)
    budget = (1-LAM)*(T/(2*PI)).log()/2+arb(".00011")+tail
    tax = LAM*(1/(C-THETA)+1/(C+S-1))
    bins = 512
    cost = arb(0)
    for i in range(1,bins+1):
        y = 2*i/(A*bins)
        q = kernel(THETA-S,y,A)+kernel(2*THETA-1,y,A)-budget-tax-D-small
        cost += q.max(0)**2
    cost *= 4/(A*bins)
    count = (low+high)**2/cost
    print("direct charge",small.str(12),"near norms",*(r.str(10) for r in diag))
    print("far coefficient square norms",hi0.str(11),hi1.str(11))
    print("square-root costs",low.str(10),high.str(10),"single lower mass",cost.str(12))
    print("increment width",width.str(10),"count",count.str(14))
    return count


if __name__=="__main__":
    assert count_bound(47,250000,10**9,4,".27")<1002860
    assert count_bound(42,65000,116000000,"3.2",".48")<420045
    assert count_bound(42,65000,10**8,"3.2",".48")<395545
