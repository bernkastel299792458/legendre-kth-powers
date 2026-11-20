"""Dyadic grouping of the actual gcd for all nonzero low modes of large primorial wheels."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator,upper_harmonic
from empty_lcm import MEAN,conditional_rows,norm,inner,local
from annular_inverse import harmonic_sums

def prepare(Q,end,width):
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();x=arb(116).exp();h=arb(H)
    denom=denominator(z,Q);mass=X*A/h+2*arb(width)*x/h*S
    eta=arb(int(fmpz(Q).euler_phi()))/Q;tau=2**len(fmpz(Q).factor());h0=10**12
    ps=[i for i in range(11,250) if Q%i and fmpz(i).is_prime()]
    assert Q%210==0 and ps and fmpz(Q).moebius_mu()
    rows=conditional_rows(MEAN,z);params=(0,10,20,25,30,33,35,37,39,41,43,45,47)
    Z=P2=arb(1)
    for p in range(11,2001):
        if Q%p and fmpz(p).is_prime():Z*=1+arb(1)/(p*(p-1));P2*=1+arb(1)/(p-1)**2
    Z*=(arb(1)/2000).exp();P2*=(arb(1)/1999).exp()
    tail=(2*(arb(11)/10)**2/arb(10).sqrt()).exp()/arb(h0).sqrt()
    @lru_cache(None)
    def first(top):
        seen=[];prod=1
        for p in ps:
            if prod*p>top:return tuple(seen)
            prod*=p;seen.append(p)
        raise ValueError(top)
    @lru_cache(None)
    def rlocal(top,s):
        val=arb(1)
        for p in first(top):val*=local(p,s,ctx.prec)
        return val
    @lru_cache(None)
    def maxrho(top):
        v=arb(1)
        for p in first(top):v*=arb(p)/(p-1)
        return v
    @lru_cache(None)
    def G(i):
        b=2**(i+1)
        if i<=9:return sum((arb(1)/int(fmpz(v).euler_phi()) for v in range(1,b)
                             if gcd(v,Q)==1 and fmpz(v).moebius_mu()),arb(0))
        return upper_harmonic(b,Q,ctx.prec).min(Z*(1+arb(b).log()))
    @lru_cache(None)
    def beta(i,s):
        if i<=9:return inner(i,Q,s,ctx.prec)
        return local(Q,s,ctx.prec)*rlocal(2**(i+1),s)*G(i)
    @lru_cache(None)
    def pos(i,top):
        low=z/(2**(i+1)*top*h0)
        if low>1:
            small=Z*(eta*arb(2).log()+(2*tau+1)*(1+z.log())/low)
            un=(P2*small**2+4*tail).sqrt().min(2*P2.sqrt())
        else:un=2*P2.sqrt()
        return un*G(i)
    @lru_cache(None)
    def sig(i,top):
        scale=2**(i+1)*top/z
        ns=[norm(100-t,200-2*t,ctx.prec)*beta(i,100-t)*rlocal(top,100-t) for t in params]
        value=rows[-1][1]*ns[0]
        for j in range(1,len(rows)):
            level,eps=rows[j];diff=(rows[j-1][1]-eps).max(arb(0))
            if diff.is_zero():continue
            base=scale*level.exp();v=ns[0]
            for t,n0 in zip(params[1:],ns[1:]):v=v.min(base**(arb(t)/100)*n0)
            value+=diff*v
        late=[(scale*z**(arb(t)/100)).sqrt()*norm(50,100+t,ctx.prec) for t in (5,8,10,12,15,20)]
        return value+beta(i,50)*rlocal(top,50)*min(late,key=lambda t:float(t.upper()))
    @lru_cache(None)
    def gw(a,b):
        if b<=4000:
            return sum(((arb(g)/int(fmpz(g).euler_phi()))**2/g for g in range(a,b+1)
                        if gcd(g,Q)==1 and fmpz(g).moebius_mu()),arb(0))
        span=(arb(b)/a).log()
        return maxrho(b)**2*(eta*span+(2*tau+1)/arb(a)).min(span+1/arb(a))
    @lru_cache(None)
    def cel(s,e):
        # All admissible g in the dyad receive a common norm envelope, but their
        # true admissible multiplicative mass is trimmed to the hyperbolic window.
        qlo=X/e;qhi=X/s;lim=int((z*z/qlo).upper().floor().unique_fmpz());vv=arb(0)
        for t in range(lim.bit_length()):
            gl=2**t;gh=min(2*gl-1,lim);imax=(lim//gl).bit_length()-1
            if gw(gl,gh).is_zero():continue
            for i in range(imax+1):
                for j in range(i,imax+1-i):
                    y=z*z/(2**(i+j))
                    l=max(gl,int((y/(4*qhi)).lower().floor().unique_fmpz()))
                    b=min(gh,int((y/qlo).upper().floor().unique_fmpz()))
                    if b<l:continue
                    v=gw(l,b)
                    if v.is_zero():continue
                    val=(sig(i,gh)*pos(j,gh)).min(sig(j,gh)*pos(i,gh))
                    vv+=(1 if i==j else 2)*v*val
        return vv
    return cel,u*h*(-c).exp()*mass/denom**2

def low(Q,cut,limit,width,signed_prefix=False):
    cells,pref=prepare(Q,limit,width);step=cut;total=arb(0)
    # Summatory absolute Ramanujan weight and its first moment by divisor inversion:
    # |c_Q(n)| = sum_{d|(n,Q)} product_{p|d}(p-2).
    if signed_prefix:
        from ramanujan_prefix import signed_maxima
        variation_factor=1+4*((limit+Q-1)//Q)
        a=cut;caps=[]
        while a<limit:
            caps.append(limit//a);a=min(limit,(5*a+3)//4)
        envelopes=signed_maxima(Q,caps)
    while step<limit:
        end=min(limit,(5*step+3)//4);top=limit//step
        n,weighted=harmonic_sums(Q,top);jump=n-harmonic_sums(Q,(limit-1)//end)[0]
        if signed_prefix:
            peak0,peak1=envelopes[top]
            n=min(n,variation_factor*peak0)
            weighted=min(weighted,variation_factor*peak1)
        peak=arb(2)*n/Q
        tv=arb(2)/Q*(2*arb.pi()/Q*(end-step)*weighted+jump)
        total+=cells(step,end)*((2+(arb(end)/step).log())*peak+tv);step=end
    return pref*total

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--Q",type=int,default=30030);ap.add_argument("--cut",type=int,default=43)
    ap.add_argument("--limit",type=int);ap.add_argument("--width",default=".0002");ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=144;v=low(a.Q,a.cut,a.limit or a.Q,a.width)
    print("all low modes, dyadic grouped arithmetic upper",v.str(15))
    if a.upper:assert v<arb(a.upper)
