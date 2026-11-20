"""Positive log-bin convolution for complete Ramanujan product energies."""
from bisect import bisect_left
from functools import lru_cache
from math import gcd, prod
from flint import arb, arb_poly, ctx, fmpz


@lru_cache(None)
def _harmonic(n, prec):
    assert prec == ctx.prec
    return (arb(n+1).digamma()+arb.const_euler()) if n else arb(0)


@lru_cache(maxsize=32)
def measure(q, M, subdivisions, precision):
    assert precision == ctx.prec and M >= 2 and subdivisions >= 8
    # Rounded-down real grid endpoints, with exact treatment of the powers of two.
    step = arb(2).log()/subdivisions
    ng = int(((2*arb(M)).log()/step).upper().ceil().unique_fmpz())+6
    floors = []
    for i in range(ng+1):
        if i % subdivisions == 0:
            floors.append(1 << (i//subdivisions))
        else:
            floors.append(int((i*step).exp().floor().unique_fmpz()))
    assert floors[-5] >= 2*M
    primes = [int(p) for p,a in fmpz(q).factor() if a==1]
    assert prod(primes)==q
    divs = [(d,(-1)**sum(d%p==0 for p in primes)) for d in range(1,q+1) if q%d==0]
    hh = [arb(1)]
    prev = arb(1)
    for i,n in enumerate(floors[1:],1):
        if n==floors[i-1]:
            hh.append(arb(0))
        else:
            h = sum((mu*_harmonic(n//d,precision)/d for d,mu in divs),arb(0))
            hh.append(h-prev)
            prev = h
    smooth = [arb(0) for _ in floors]
    def insert(d,j,c):
        if j==len(primes):
            i = bisect_left(floors,d)
            smooth[i] += arb(c*c)/(q*d)
            return
        p = primes[j]
        insert(d,j+1,-c)
        d *= p
        while d <= 2*M:
            insert(d,j+1,c*(p-1))
            d *= p
    insert(1,0,1)
    coeff = arb_poly(hh)**4 * arb_poly(smooth)
    bad = arb(1)/2000
    for p in range(2,2001):
        if gcd(p,q)==1 and fmpz(p).is_prime():
            bad += arb(1)/(p*p)
    return step, floors, [coeff[i] for i in range(ng+1)], 1-bad


def bounds(q,M,T,cut,start,subdivisions=48):
    # cut*k^2 is the true first time before max with start.
    step, floors, coefficients, good = measure(q,M,subdivisions,ctx.prec)
    lower = up = twice = arb(0)
    for i,weight in enumerate(coefficients):
        # Values assigned upper index i lie in (2^((i-5)/J),2^(i/J)] or equal 1.
        lo = max(0,i-5)
        if floors[lo] <= 2*M:
            twice += weight
        if floors[lo] <= M:
            up += weight
        if floors[i] <= M:
            # The upper grid point might be <1 above M; floor captures integer k.
            early = (cut*floors[i]**2).max(start)
            lower += weight*(1-early/T).max(0)
    return good*lower, up, twice, (arb(M)*up).sqrt()
