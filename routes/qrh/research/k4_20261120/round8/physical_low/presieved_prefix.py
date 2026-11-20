"""All-frequency upper on all actual multipliers before a given presieved cutoff."""
from functools import lru_cache
from math import gcd
import argparse
from flint import arb,ctx,fmpz
from actual_split import H,constants
from empty_lcm import region,MEAN

@lru_cache(None)
def phi(n):return int(fmpz(n).euler_phi())

@lru_cache(None)
def squarefree(n):return bool(fmpz(n).moebius_mu())

def run(C,Q,P,last,mean,show):
    z,c,r,I,mass,peaks,u=constants(C);eta=arb(phi(Q))/Q
    assert squarefree(Q) and last<=128 and 5<=P<=997
    G=eta*(z.log()+arb("1.331"));xn=(c-2*r).exp();xh=(c+2*r).exp()
    assert z*z<xn and gcd(Q,last)==1
    ps=[p for p in range(2,P+1) if fmpz(p).is_prime()]
    ta=arb(1)
    for p in range(P+1,1001):
        if fmpz(p).is_prime():ta*=1+arb(1)/(p*(p-1))
    ta*=(arb(1)/1000).exp();coef=(1+z.log())**2
    U=arb(1)
    for p in ps:
        if Q%p:U*=arb(p)/(p-1)
    D=2**len(ps)*U
    @lru_cache(None)
    def prob(g,b,t):
        v=arb(1)
        for p in ps:
            h=arb(1)-arb(1)/p
            left=(Q*g*b)%p==0;right=(Q*g*t)%p==0
            v*=h*h if left and right else h if left or right else 1-arb(1)/p**2
        return v
    actual=arb(0)
    for k in range(2,last):
        if gcd(k,Q)>1:continue
        assert xn/k>xh/last
        s=e=arb(0);num=0
        for g in range(1,k):
            if not squarefree(g) or gcd(g,Q)>1:continue
            rho=arb(g)/phi(g)
            for b in range(1,(k-1)//g+1):
                if not squarefree(b) or gcd(b,g*Q)>1:continue
                for t in range(1,min(b,(k-1)//(g*b))+1):
                    if not squarefree(t) or gcd(t,g*Q)>1:continue
                    A=xn*t/(k*z);B=z/(g*b);ell=(B/A).log()
                    if ell<0:continue
                    assert ell>0 and A>1
                    factor=(1 if b==t else 2)*rho**2/(phi(b)*phi(t)*G**2)
                    s+=factor*(prob(g,b,t)*ta**2*ell+D*coef*ta/A)/(k*g)
                    e+=factor*D*coef*U*ta*B
                    num+=1 if b==t else 2
        sl=u*(2*r).exp()*mass*s
        ed=u*arb(H)*(-c).exp()*peaks*e
        actual+=sl+ed
        if show:print("k",k,"ordered rows",num,"slope edge and cumulative",*(v.str(10) for v in (sl,ed,actual)),flush=True)
    _,v,_=region("116",C,MEAN if mean else (),True,threshold=xh/last,sieve_mod=Q)
    inv=u*(2*r).exp()*mass*v
    return actual,inv,actual+inv

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=1732099)
    ap.add_argument("--Q",type=int,default=210);ap.add_argument("--next",type=int,default=29)
    ap.add_argument("--small",type=int,default=37);ap.add_argument("--mean",action="store_true")
    ap.add_argument("--rows",action="store_true");ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=160
    v=run(a.C,a.Q,a.small,a.next,a.mean,a.rows)
    print("Q",a.Q,"q above e^(c+2r) /",a.next,"all actual, inverse, total",*(t.str(14) for t in v))
    if a.upper:assert v[-1]<arb(a.upper)
