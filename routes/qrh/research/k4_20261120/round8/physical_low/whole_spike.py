"""Full real multiplier k, including repeated prime multiples, after lcm aggregation."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from odd_sieve import denominator,parameters
from parity_target import kernel

Q=210
@lru_cache(None)
def phi(n):return int(fmpz(n).euler_phi())
def sq(n):return bool(fmpz(n).moebius_mu())
def gp(z,mod=Q):
    eta,corr,err=parameters(mod,ctx.prec)
    return eta*(z.log()+arb("1.332583")+corr)+err/z.sqrt().sqrt()

def upper(k,P,mod=Q,g=1,width=".0002"):
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp()
    G=denominator(z,mod);K=arb(H);x=arb(116).exp();mass=X*A/K+2*arb(width)*x/H*S;P0=u*K*(-c).exp()
    assert gcd(g,mod)==1 and sq(g) and max(int(p) for p,_ in fmpz(mod).factor())<=P
    ps=[p for p in range(2,P+1) if fmpz(p).is_prime()]
    tail=arb(1)
    for p in range(P+1,1001):
        if fmpz(p).is_prime():tail*=1+arb(1)/(p*(p-1))
    tail*=(arb(1)/1000).exp()
    U=arb(1)
    for p in ps:
        if mod%p:U*=arb(p)/(p-1)
    D=2**len(ps)*U;coef=(1+z.log())**2
    s=e=arb(0)
    for b in range(1,(k-1)//g+1):
        if not sq(b) or gcd(b,mod*g)>1:continue
        for t in range(1,min(b,(k-1)//(g*b))+1):
            if not sq(t) or gcd(t,mod*g)>1:continue
            lo=xl*t/(k*z);hi=z/(g*b);ell=(hi/lo).log()
            if ell<=0:continue
            delta=arb(1)
            for p in ps:
                h=1-arb(1)/p
                left=mod*g*b%p==0;right=mod*g*t%p==0
                delta*=h*h if left and right else h if left or right else 1-arb(1)/p**2
            fac=arb(1 if t==b else 2)*(arb(g)/phi(g))**2/(phi(b)*phi(t)*G**2)
            s+=fac*(delta*tail**2*ell+D*coef*tail/lo)/(k*g)
            e+=fac*D*coef*U*tail*hi
    return P0*mass*s,P0*S*e

def shared_lower(k,g,P=23,mod=Q):
    z,c,r,I,A,S,u=constants(1732099);y=z/g;Qp=mod*g;mult=k*g
    assert g<k and fmpz(g).is_prime() and gcd(g,mod)==1 and g<=P and max(int(p) for p,_ in fmpz(mod).factor())<=P
    h=arb(H);a=(1-arb("1e-12"))*h*(c-116);start=h*(c-116);b=2*arb.pi()-a
    xh=(c+b/h).exp();xl=(c-b/h).exp();lo=xh/(mult*y);vmin=xl/(mult*y)
    ell=(y/lo).log();eta=arb(phi(Qp))/Qp
    unit=prob=arb(1);s=arb(1)/1000;np=0
    for p in range(2,1001):
        if not fmpz(p).is_prime():continue
        if p<=P:
            np+=1
            if Qp%p:
                unit*=arb(p)/(p-1);prob*=1-arb(1)/p**2
        else:s+=arb(1)/p**2
    prob*=eta**2;D=unit*2**np;B=y**(arb(1)/3);B0=1000000
    slope=ell*(prob-3*eta*s)-eta*(2**np+y.sqrt()+1+y.log()+s)/lo
    slope-=unit**2*(arb(1)/B0+(y/vmin).sqrt()/B)*(ell+1/lo)
    E=(y+1)*(unit*D*(1+B0+y.log()/arb(2).log())+unit**2*(B+y/B**2))
    dw=(b-start)/2048;area=dw*sum(kernel(start+dw*j,a) for j in range(1,2049))
    charge=2*u*h*(-c).exp()*(arb(g)/(g-1)/gp(z,mod))**2*(xl/h*slope*area/mult-E*a.sin()/(2*a))
    return charge.max(arb(0))

def inv(k,wide=None):
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp();G=denominator(z,Q)
    lo=xl/k if wide is None else X/wide;hi=X/k
    h=arb(H);mass=X*A/h+2*arb(".0002")*arb(116).exp()/h*S
    eta=arb(48)/210
    Z=arb(1)
    for p in range(11,1001):
        if fmpz(p).is_prime():Z*=1+arb(1)/(p*(p-1))
    Z*=(arb(1)/1000).exp()
    def harmonic(l,span):
        return Z*(eta*span+33*(1+z.log())/l)
    top=int((z*z/lo).upper().floor().unique_fmpz());total=arb(0)
    for g in range(1,top+1):
        if not sq(g) or gcd(g,Q)>1:continue
        end=int((z*z/(g*lo)).upper().floor().unique_fmpz())
        for b in range(1,end+1):
            if not sq(b) or gcd(b,Q*g)>1:continue
            for t in range(1,min(b,end//b)+1):
                if not sq(t) or gcd(t,g*Q)>1:continue
                low=lo*t/z;up=z/(g*b);span=(up/low).log()
                if span<=0:continue
                # l <= g u v <= h implies v>=lo/(g*up).
                H1=harmonic(low,span);H2=harmonic(lo/(g*up),(hi/lo).log())
                total+=(1 if b==t else 2)*(arb(g)/phi(g))**2*H1*H2/(g*phi(b)*phi(t))
    cap=(arb(48)+40)/Q
    return u*h*(-c).exp()*mass*total*cap/G**2

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--k",type=int,default=23)
    ap.add_argument("--P",type=int,default=37);ap.add_argument("--end",type=int);ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=144
    assert 23<=a.k<50 and fmpz(a.k).is_prime()
    s,e=upper(a.k,a.P);lower=[(g,shared_lower(a.k,g)) for g in (11,13,17,19,23) if g<a.k]
    # All wrong signs on X/50<q<=X/23 were paid uniformly, even if n is not squarefree.
    if a.end is None:corr=inv(a.k)
    else:
        from annular_inverse import cost as annular
        assert a.k<a.end<=50 and all(gcd(k,Q)>1 for k in range(a.k+1,a.end))
        z,c,r,*_=constants(1732099)
        assert (c-2*r).exp()/a.k>(c+2*r).exp()/a.end
        assert (c-2*r).exp()/(a.k-1)>(c+2*r).exp()/a.k
        corr=annular(a.k,a.end)[1]
    cost=s+e-sum((v for g,v in lower),arb(0))+2*arb(".00000009043441")+corr+arb("2.03e-13")
    print("k",a.k,"coprime slope/edge, exact-aggregated prime-gcd lower, joint mean+low upper, middle upper",
          s.str(15),e.str(15),[(g,v.str(10)) for g,v in lower],corr.str(12),cost.str(16))
    if a.upper:assert cost<arb(a.upper)
