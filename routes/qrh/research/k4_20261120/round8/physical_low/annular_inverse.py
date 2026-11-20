"""Signed inverse mean and all low modes over a complete modulus annulus."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from odd_sieve import denominator
from empty_lcm import conditional_rows,MEAN,norm,inner
from whole_spike import phi,sq

@lru_cache(None)
def ramanujan_weights(Q):
    ds=[(1,1)]
    for p,_ in fmpz(Q).factor():
        p=int(p)
        if p>2:ds += [(d*p,v*(p-2)) for d,v in ds]
    return tuple(ds)

def harmonic_sums(Q,top):
    count=weighted=0
    for d,v in ramanujan_weights(Q):
        m=top//d
        count+=v*m
        weighted+=v*d*m*(m+1)//2
    return count,weighted

def cost(start,end,low_only=False,mean_only=False,mod=210,harmonic_limit=210,width=".0002"):
    z,c,r,I,A,S,u=constants(1732099);x=arb(116).exp();K=arb(H);Q=mod;X=(c+2*r).exp()
    mass=X*A/K+2*arb(width)*x/K*S
    assert 1<=start<end and (mean_only or start>=23) and not (low_only and mean_only)
    assert Q%210==0 and sq(Q) and harmonic_limit>0
    ql=X/end;qh=X/start;G=denominator(z,Q);limit=int((z*z/ql).upper().floor().unique_fmpz())
    rows=conditional_rows(MEAN,z)
    eta=arb(phi(Q))/Q
    top=0 if mean_only else harmonic_limit//start
    n,weighted=harmonic_sums(Q,top)
    jumps=0 if mean_only else n-harmonic_sums(Q,(harmonic_limit-1)//end)[0]
    peak=(0 if low_only else eta)+arb(2)*n/Q
    variation=arb(2)/Q*(2*arb.pi()/Q*(end-start)*weighted+jumps)
    abel=(2+(arb(end)/start).log().min(arb(2).log()))*peak+variation
    # Absolute fixed outer row after the coprimality inversion by h.
    h0=10**14; Z=arb(1); P2=arb(1)
    for p in range(11,2001):
        if fmpz(p).is_prime() and Q%p:
            Z*=1+arb(1)/(p*(p-1));P2*=1+arb(1)/(p-1)**2
    Z*=(arb(1)/2000).exp();P2*=(arb(1)/1999).exp()
    tail=(arb(2)*(arb(11)/10)**2/arb(10).sqrt()).exp()/arb(h0).sqrt()
    params=(0,10,20,25,30,33,35,37,39,41,43,45,47)
    @lru_cache(None)
    def signed(i,g):
        conductor=Q*g;scale=2**(i+1)*g/z
        ns=[norm(100-t,200-2*t,ctx.prec)*inner(i,conductor,100-t,ctx.prec) for t in params]
        value=rows[-1][1]*ns[0]
        for j in range(1,len(rows)):
            level,eps=rows[j];change=(rows[j-1][1]-eps).max(arb(0))
            if change.is_zero():continue
            base=scale*level.exp();v=ns[0]
            for t,n0 in zip(params[1:],ns[1:]):v=v.min(base**(arb(t)/100)*n0)
            value+=change*v
        candidates=[(scale*z**(arb(t)/100)).sqrt()*norm(50,100+t,ctx.prec) for t in (5,8,10,12,15,20)]
        return value+inner(i,conductor,50,ctx.prec)*min(candidates,key=lambda v:float(v.upper()))
    @lru_cache(None)
    def absolute(i,g):
        low=z/(2**(i+1)*g*h0)
        assert low>1
        core=Z*(eta*arb(2).log()+(2*2**len(fmpz(Q).factor())+1)*(1+z.log())/low)
        # For h>h0 a short dyadic interval has absolute squarefree harmonic <=2.
        weight=sum((arb(1)/phi(b) for b in range(1,2**(i+1)) if sq(b) and gcd(b,Q*g)==1),arb(0))
        return weight*(P2*core**2+4*tail).sqrt()
    total=arb(0);nc=0
    for g in range(1,limit+1):
        if not sq(g) or gcd(g,Q)!=1:continue
        imax=(limit//g).bit_length()-1
        for i in range(imax+1):
            for j in range(imax+1-i):
                ray=z*z/(g*2**(i+j))
                if ray<ql or ray/4>qh:continue
                mix=(absolute(i,g)*signed(j,g)).min(absolute(j,g)*signed(i,g))
                total+=(arb(g)/phi(g))**2/g*mix*abel;nc+=1
    return nc,u*K*(-c).exp()*mass/G**2*total

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--start",type=int,default=23)
    ap.add_argument("--end",type=int,default=29);ap.add_argument("--upper");ap.add_argument("--low-only",action="store_true")
    ap.add_argument("--mean-only",action="store_true")
    a=ap.parse_args();ctx.prec=144
    n,v=cost(a.start,a.end,a.low_only,a.mean_only);print("curved cells",n,"selected signed inverse multiplier",v.str(15))
    if a.upper:assert v<arb(a.upper)
