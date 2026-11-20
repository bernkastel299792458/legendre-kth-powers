"""Squared masses after exact coincidences between two reduced rational frequencies."""
from functools import lru_cache
from math import gcd
from flint import arb, fmpz
from bilinear import upper


@lru_cache(maxsize=32768)
def inclusion(k):
    terms=[(1,1)]
    for p,_ in fmpz(k).factor():
        terms.extend([(int(p)*d,-v) for d,v in list(terms)])
    return terms


def units(lo,hi,s):
    if hi<lo:return 0
    return sum(v*(hi//d-(lo-1)//d) for d,v in inclusion(s))


def divisors(k):
    out=[1]
    for p,e in fmpz(k).factor():
        old=out.copy()
        for j in range(1,int(e)+1):
            out.extend([a*int(p)**j for a in old])
    return out


def large_mass(N,J,P,s,eta,delta,cap=512):
    H=J-N
    M=H//2
    if M<1:return arb(0)
    small=min(M,cap)
    total=arb(0)
    for b in range(1,small+1):
        if gcd(b,s)>1:continue
        lo=(N+b-1)//b;hi=J//b
        count=units(lo,hi,P)
        if count>1:total+=arb(count*(count-1))/lo
    # With n=db,n'=ab a different pair of P-units forces b<=H/2.
    # All subsequent expressions upper-bound sum of D_b(D_b-1)b/N.
    def chunk(lo,hi):
        if lo>hi:return arb(0)
        count=units(lo,hi,s);sum_b=0;harm=arb(0)
        for t,sign in inclusion(s):
            a=(lo-1)//t;z=hi//t
            sum_b+=sign*t*(z*(z+1)-a*(a+1))//2
            if z>a:harm+=sign*(arb(z+1).digamma()-arb(a+1).digamma())/t
        u=eta*H
        discrepancy=(u*u*harm+u*(2*delta-1)*count+delta*(delta-1)*sum_b)/N
        parity=(u*harm+delta*count)*H/(2*N)
        assert min(delta,delta-1)>=0 and count>=0 and sum_b>=0
        return discrepancy.min(parity)
    boundary=small
    while boundary<M:
        end=min(M,2*boundary)
        total+=chunk(boundary+1,end)
        boundary=end
    return total


def collision_masses(N,J,P,s,eta,delta):
    if J<=8192:
        sums=[arb(0) for _ in range(5)]
        correction=[arb(0) for _ in range(3)]
        for n in range(N,J+1):
            if gcd(n,s)>1:continue
            v=arb(1)/n
            inv=arb(1)
            for i in range(5):
                sums[i]+=inv;inv*=v
            pairs=arb(0)
            for d in divisors(n):
                if d==1 or gcd(d,P)>1:continue
                b=n//d
                lo=(N+b-1)//b;hi=J//b
                pairs+=arb(units(lo,hi,P*d))/d
            for p in range(3):
                correction[p]+=pairs*v**(2*p)
        return [upper(value/sums[p]**2) for p in range(3)
                for value in (sums[2*p],correction[p])]
    count=units(N,J,s)
    assert count>0
    M=large_mass(N,J,P,s,eta,delta)
    return [upper((arb(J)/N)**(2*p)*value/count**2)
            for p in range(3) for value in (arb(count),M)]
