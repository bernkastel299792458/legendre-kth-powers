"""Complete moving low-frequency off-diagonal of the three-quarter direct branch."""
from math import gcd
from array import array
from functools import lru_cache

from flint import arb,ctx

from quarter_diagonal import primes


@lru_cache(None)
def first_gap(q):
    S=2**48
    weights=[(S+j-1)//j for j in range(1,q+1)]
    units=[gcd(i,q)==1 for i in range(q)]
    mx=max(sum(weights[j-1] for j in range(1,q+1) if units[(i+j)%q])
           for i in range(q) if units[i])
    return mx,S


def test(N,U=arb(37),alpha=arb(32),q=2310):
    H0=arb(3*10**12);K=arb(".99")*H0;ts=arb(".95")*H0
    Y=(U-3).exp();X=Y*arb("9.5").exp()
    y0=alpha*(q*ts/(2*arb.pi())).sqrt()
    assert N<13*Y
    D=int((arb(N)/y0).upper().floor().unique_fmpz())
    assert D>=1
    powers=2048;sigma=arb(3)/4;a=2*sigma-1
    eta=arb(sum(gcd(i,q)==1 for i in range(q)))/q
    count=0;hi=lo=arb(0)
    for i in range(q):
        v=count-eta*i
        hi=hi.max(v);lo=lo.min(v-eta)
        count+=int(gcd(i+1,q)==1)
    discr=hi-lo+1
    # Prefix bound for sum_{(n,q)=1,n<=x} n^-r uses a weighted harmonic
    # constant from one exact first period; only the tail pays 2D/q^r.
    def prefix_error(r):
        s=arb(0);head=arb(0)
        for i in range(1,q+1):
            if gcd(i,q)==1:s+=arb(i)**(-r)
            head=head.max(s-eta*arb(i)**(1-r)/(1-r))
        return head.max(s-eta*arb(q)**(1-r)/(1-r)+2*discr*arb(q)**(-r))
    def coefficient(r,L):
        return (eta/(1-r)+prefix_error(r)/L**(1-r)).min(1/(1-r))
    L=arb(N)/(D*D)
    # Full positive lcm kernel (no squarefreeness needed).
    scale=2**40
    H=array("Q",[0])
    phi=array("I",range(D+1))
    for p in range(2,D+1):
        if phi[p]==p:
            for j in range(p,D+1,p):phi[j]-=phi[j]//p
    for d in range(1,D+1):H.append(H[-1]+((scale+d-1)//d if gcd(d,q)==1 else 0))
    lcm=sum((arb(phi[d]*H[D//d]**2)/d**2 for d in range(1,D+1) if gcd(d,q)==1),arb(0))/scale**2
    harmonic=arb(H[D])/scale;leak=(arb(N)/Y).log().max(arb(0))/arb("9.5")
    lcm+=2*leak*harmonic+leak**2
    nenergy=coefficient(a,L)*arb(N)**(1-a)*lcm
    one=coefficient(sigma,arb(N)/D)*arb(N)**(1-sigma)*(harmonic+leak)
    # Unit differences in one period. Both signs have the same uniform supremum.
    z,s=first_gap(q);gap=arb(z)/s
    gap+=eta*(arb(N)/q).log()+2*discr/q
    neargap=gap+arb(1)/2
    off=4*(neargap*nenergy+one**2/(2*arb(2).log()))
    M1=4*X**(arb(1)/4)
    euler=1
    for p in primes(q):euler*=1+arb(p)**(-sigma)
    early=ts*((1+arb("1e-9"))*(ts+2)/K)**(2*powers)*(
           12*(ts+2)**(1-sigma)*euler*M1+1)**2
    return D,early,nenergy,off


if __name__=="__main__":
    ctx.prec=144
    for N in (10**13,10**14,5*10**14,10**15,15*10**14,2*10**15):
        D,e,n,y=test(N)
        print("forward product cutoff",N,"complement divisors through",D,
              "early",e.str(7),"weighted energy",n.str(9),"internal off-diagonal",y.str(11),flush=True)
