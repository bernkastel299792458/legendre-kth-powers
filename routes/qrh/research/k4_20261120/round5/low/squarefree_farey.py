"""Discard squareful Farey denominators before the weighted large sieve."""
from itertools import combinations
from math import prod
from flint import arb, ctx


def positive(x):
    return x.max(arb(0))


def area(A,c):
    return A**2/4-positive(A-c)**2/2+positive(A-2*c)**2/4


def both_area(A,c):
    return positive(c-A/2)**2-positive(c-A)**2


def added_denominator(mesh=4096):
    primes = (2,3,5,7,11)
    k = arb("1.045")
    g = k**2
    z = k*(arb(70).exp()/(arb(4)/3)).sqrt()
    delta = prod(1-1/arb(p) for p in primes)
    bad_square = arb(2).zeta()*prod(1-1/arb(p)**2 for p in primes)-1
    discrepancy = 2**len(primes)
    classes = []
    for j in range(len(primes)):
        for factors in combinations(primes,j):
            d = prod(factors)
            phi = prod(p-1 for p in factors)
            coprime = [p for p in primes if p not in factors]
            removal = 1-prod(1-1/arb(p)**2 for p in coprime)
            classes.append((d,phi,removal,2**len(coprime)-1,coprime))
    gain = arb(0)
    for i in range(mesh//32,mesh):
        a,b = arb(i)/mesh,arb(i+1)/mesh
        cap = arb(1).min(1/(2*b))
        # On a cell crossing a discontinuity use the universal two-arc bound.
        I = arb(1)/24
        phase = arb(0)
        j0 = j1 = arb(0)
        f0,r0 = divmod(2*mesh,i)
        f1,r1 = divmod(2*mesh,i+1)
        if f0==f1:
            lo,hi = arb(r1)/(i+1),arb(r0)/i
            I = I.max(area(lo,cap)+area(1-hi,positive(cap-hi)))
            phase = (lo*(1-lo)).min(hi*(1-hi))
            j0 = both_area(lo,cap).min(both_area(hi,cap))
            c1 = positive(cap-hi)
            j1 = both_area(1-hi,c1).min(both_area(1-lo,c1))
        residue_error = (30/(a*z)).sqrt()
        original = arb(1)/4+phase/2-2*residue_error
        denom = 1+g*a-g*a**2*original
        for d,phi,kappa,terms,primes_used in classes:
            extra = positive(2*kappa*I-4*terms*residue_error)
            if f0==f1:
                both = []
                for branch in (f0,f0-1):
                    neither = prod(1-arb(1 if branch%(p*p)==0 else 2)/(p*p)
                                   for p in primes_used)
                    both.append(2*kappa-1+neither)
                extra += positive(both[0]*j0+both[1]*j1-2*terms**2*residue_error)
            # Count q=d*n, (n,Q)=1, squarefree. Counts divided by z.
            count = positive(delta*(1-bad_square)*(b-a)/d-
                             discrepancy*(1/z+(b/(d*z)).sqrt()))
            new_denom = denom-g*a**2*extra
            assert original>0 and new_denom>0
            gain += count*(d/(arb(phi)*b))*g*a**2*extra/(denom*new_denom)
    return 2*gain


if __name__ == "__main__":
    ctx.prec = 192
    gain = added_denominator()
    print("additional sieve denominator",gain.str(16),"total from rounded baseline",
          (arb("1.1328")+gain).str(16))
    assert arb("1.1328")+gain>arb("1.16613")
