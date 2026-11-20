"""Integer Boolean sign tables and two actual signed Selberg counterexamples."""
from fractions import Fraction
from functools import lru_cache
from math import gcd,prod
from flint import arb,ctx,fmpz
from actual_split import constants,H

def ideals(K):
    return [x for x in range(1,1<<(1<<K))
            if all(not (x>>m&1) or all(x>>(m^p)&1 for p in (1<<j for j in range(K)) if m&p)
                   for m in range(1<<K))]

def table(k):
    V=1<<k; full=V-1; families=ideals(k)
    pairs=[(i,j,(-1)**(k+i.bit_count()+j.bit_count()))
           for i in range(V) for j in range(V) if (i|j)==full]
    vals=[]
    for x in families:
        for y in families:
            t=sum(s for i,j,s in pairs if x>>i&1 and y>>j&1)
            vals.append(t)
            if k==4 and t<0:
                assert (x==32767) != (y==32767)
                partner=y if x==32767 else x
                assert sum(partner>>v&1 for v in range(16) if v.bit_count()==2)>=5
    return len(families),min(vals),max(vals),sum(t<0 for t in vals)

@lru_cache(None)
def prime(n):
    """Verify primality recursively by the full factorization of n-1 and Lucas's theorem."""
    if n==2:return True
    if n<2:return False
    fs=[(int(p),int(e)) for p,e in fmpz(n-1).factor()]
    assert prod(p**e for p,e in fs)==n-1 and all(prime(p) for p,_ in fs)
    # Full-order witness gives a subgroup of order n-1 among the units.
    for a in range(2,2000):
        if pow(a,n-1,n)==1 and all(gcd(pow(a,(n-1)//p,n)-1,n)==1 for p,_ in fs):return True
    raise ValueError(n)

def nextprime(n):
    while not fmpz(n).is_prime():n+=1
    assert prime(n)
    return n

def rational_sign(ps,U,V):
    divs=[prod(ps[i] for i in range(len(ps)) if bits>>i&1) for bits in range(1<<len(ps))]
    def row(v):
        vals=[]
        for d in divs:
            g=sum((Fraction(int(fmpz(j).moebius_mu())**2,int(fmpz(j).euler_phi()))
                   for j in range(1,1+v//d) if gcd(j,210*d)==1),Fraction(0))
            vals.append(g*Fraction(d,int(fmpz(d).euler_phi())))
        return vals
    F,G=row(U),row(V);full=len(divs)-1
    return sum(((-1)**(len(ps)+i.bit_count()+j.bit_count())*x*y
                for i,x in enumerate(F) for j,y in enumerate(G) if (i|j)==full),Fraction(0))

def sample(ps,U,V,offset=".5",near_threshold=False):
    m=prod(ps); z,c,r,*_=constants(1732099); X=(c+2*r).exp()
    def choice(v):return nextprime(int((z/(arb(v)+arb(offset))).lower().floor().unique_fmpz())+1)
    P=choice(U);R=choice(V)
    if R==P:R=nextprime(P+1)
    assert U<z/P<U+1 and V<z/R<V+1 and P*R>z and max(U,V)<min(P,R)
    assert prime(P) and prime(R) and all(prime(p) for p in ps)
    C=rational_sign(ps,U,V)
    q=P*R*m;ratio=X/q;rho=z*z/q
    assert max(ps)<rho<min(P,R) and C<0
    exact=arb(C.numerator)/C.denominator
    if near_threshold:
        assert arb(247)/11<rho<arb(247)/11+arb("1e-12") and 22<ratio<23 and exact<arb("-.28585")
    else:
        assert 23<ratio<200
        if len(ps)==4:assert arb("-1.186856")<exact<arb("-1.186855")
        else:assert arb("-9.740826")<exact<arb("-9.740825")
    return P,R,q,ratio,rho,C

def actual_spike():
    from parity_target import kernel
    ps=(11,13,17,19);m=prod(ps);z,c,r,*_=constants(1732099)
    P=nextprime(int((z/arb("250.5")).lower().floor().unique_fmpz())+1)
    center=(c+arb.pi()/H).exp()
    R=nextprime(int((center/(23*m*P)).upper().ceil().unique_fmpz()))
    q=m*P*R;v=H*((23*q)/c.exp()).log()
    U=int((z/P).floor().unique_fmpz());V=int((z/R).floor().unique_fmpz())
    C=rational_sign(ps,U,V)
    assert all(prime(p) for p in ps) and P!=R and min(P,R)>max(U,V) and P*R>z
    assert arb.pi()<=v<arb.pi()+arb(".0001") and (c+2*r).exp()/50<q<(c+2*r).exp()/23
    a=(1-arb("1e-12"))*H*(c-116);assert a<v<H*r and kernel(v,a)>arb(".1384")
    assert C==Fraction(-3556553,12441600)
    return P,R,q,U,V,v,C

if __name__=="__main__":
    ctx.prec=160
    for k in range(5):
        t=table(k)
        print("dimensions, nonempty ideals, min/max, negative pairs",k,*t)
        if k<=3:assert t[1]>=0
        else:assert t==(167,-2,6,22)
    for s,U,V in [((11,13,17,19),4224,323),((11,13,17,19,23),7477,7477)]:
        P,R,q,a,b,C=sample(s,U,V)
        print("small primes",s,"P,R,q",P,R,q,"X/q,z**2/q",a.str(13),b.str(13),"exact fraction",str(C),
              "exact normalized signed coefficient enclosed by",(arb(C.numerator)/C.denominator).str(14))
    P,R,q,a,b,C=sample((11,13,17,19),247,4199,"1e-12",True)
    print("near sharp onset P,R,q, z^2/q - 247/11, exact normalized coefficient",P,R,q,(b-arb(247)/11).str(14),C)
    P,R,q,U,V,v,C=actual_spike()
    print("first real k=23 positive lobe P,R,q,u,v, angle, exact coefficient",P,R,q,U,V,v.str(16),C)
