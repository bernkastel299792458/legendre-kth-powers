"""Physical mass at every repeated-prime multiple on a large-wheel modulus prefix."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from odd_sieve import denominator
from whole_spike import phi,sq,upper
from moving_anchor import rare

def repeated(k,Q,width):
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp();x=arb(116).exp()
    assert fmpz(k).is_prime() and gcd(k,Q)==1 and z*z<xl
    P=max(37,max(int(p) for p,_ in fmpz(Q).factor()))
    ps=[p for p in range(2,P+1) if fmpz(p).is_prime()]
    tail=(arb(1)/1000).exp()
    for p in range(P+1,1001):
        if fmpz(p).is_prime():tail*=1+arb(1)/(p*(p-1))
    U=arb(1)
    for p in ps:
        if Q%p and p!=k:U*=arb(p)/(p-1)
    G=denominator(z,Q);D=2**len(ps)*U;F=(1+z.log())**2
    slope=edge=arb(0)
    for g in range(1,k):
        if not sq(g) or gcd(g,Q*k)>1:continue
        for b in range(1,(k-1)//g+1):
            if not sq(b) or gcd(b,Q*g*k)>1:continue
            for t in range(1,(k-1)//(g*b)+1):
                if not sq(t) or gcd(t,Q*g*k)>1:continue
                low=xl*t/(k*k*z);up=z/(g*k*b);span=(up/low).log()
                if span<=0:continue
                assert span>0
                mean=arb(1)
                for p in ps:
                    h=1-arb(1)/p
                    l=Q*k*g*b%p==0;r0=Q*k*g*t%p==0
                    mean*=h*h if l and r0 else h if l or r0 else 1-arb(1)/p**2
                fac=2*(arb(g)/phi(g))**2*(arb(k)/(k-1))/(phi(b)*phi(t)*G**2)
                slope+=fac*(mean*tail**2*span+D*F*tail/low)/(k*k*g)
                edge+=fac*D*F*U*tail*up
    mass=X*A/H+2*arb(width)*x/H*S
    return u*H*(-c).exp()*(slope*mass+edge*S)

def calculate(Q,start,end,width):
    assert 1<=start<end and fmpz(Q).moebius_mu() and Q%210==0
    z,c,r,*_=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp()
    assert xl*end>X*(end-1) and xl*start>X*(start-1) and arb(width)>0
    ks=[k for k in range(max(2,start),end) if gcd(k,Q)==1]
    assert all(fmpz(k).is_prime() for k in ks)
    reps=sum((repeated(k,Q,width) for k in ks),arb(0))
    err=arb(0)
    for k in ks:
        ps=[p for p in range(2,k) if fmpz(p).is_prime() and Q%p]
        assert len(ps)<2 or ps[0]*ps[1]>=k
        P=max(37,max(int(p) for p,_ in fmpz(Q).factor()))
        for p in ps[3:]:
            h=rare(k,p,Q,width)
            a,b=upper(k,P,Q,p,width)
            err+=2*h.min(a+b)
    return ks,reps,err

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--Q",type=int,default=223092870)
    ap.add_argument("--start",type=int,default=1);ap.add_argument("--end",type=int,default=131)
    ap.add_argument("--upper",nargs=2);a=ap.parse_args();ctx.prec=144
    ks,rep,err=calculate(a.Q,a.start,a.end,".0002")
    print("first/last actual k",ks[0],ks[-1],"repeated physical mass and all Liouville transfer error",rep.str(16),err.str(16))
    if a.upper:assert rep<arb(a.upper[0]) and err<arb(a.upper[1])
