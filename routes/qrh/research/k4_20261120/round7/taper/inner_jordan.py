"""Additional Jordan variance in the earlier j<Y portion of the same sieve."""
from functools import lru_cache
from math import comb
from flint import arb,ctx,fmpz
from causal_mellin import prefix


@lru_cache(maxsize=60)
def responses(e0,e1,prec,S=16,grid=256):
    assert ctx.prec==prec
    A,B=prefix(2310,S)
    K=2**44
    lo=arb(e0)/1000
    hi=arb(e1)/1000
    e=lo.union(hi)
    step=arb(1)/grid
    slope=arb(1)
    value=arb(0)
    vals=[arb(0)]
    old=1
    err_slope=err_func=arb(0)
    for i in range(1,S*grid+1):
        t=arb(i)/grid
        a=t-step
        n=int(t.exp().floor().unique_fmpz())
        count=n-old
        delta=arb(int(A[n])-int(A[old]))/K
        logdelta=arb(int(B[n])-int(B[old]))/K
        mass=arb(count)/(old+1)
        rounding=arb(count)/K
        # Common tilt within a cell. Signed prefixes include the actual
        # squarefree and unit restrictions; only variation uses unsigned mass.
        tilt=(-e*a).exp()
        error=mass*(-lo*a).exp()*hi*step
        linear=rounding*(1+t)+160*arb(2)**(-52)*t*mass
        value+=step*slope+tilt*(t*delta-logdelta)
        err_func+=step*err_slope+step*error+linear
        slope+=tilt*delta
        err_slope+=error+rounding
        vals.append(value+arb(0,err_func.upper()))
        old=n
    return vals


def response(t,vals,grid=256):
    if t<=0:return arb(0)
    j=int((t*grid).lower().floor().unique_fmpz())
    node=arb(j)/grid
    return vals[j]+arb(0,((1+t)*(t-node)).upper())


@lru_cache(None)
def saving(width,prec):
    assert prec==ctx.prec
    W=arb(width);step=64
    first=int((W*step).unique_fmpz())
    primes=[p for p in range(13,100) if fmpz(p).is_prime()]
    lowers=[]
    for e0 in range(40,100,5):
        lo,hi=arb(e0)/1000,arb(e0+5)/1000
        vals=responses(e0,e0+5,prec)
        ans=arb(0);unit=arb(480)/2310
        for j,p in enumerate(primes):
            lp=arb(p).log()
            dens=unit*(1-arb(1)/p)/p
            prob=(1-arb(p)**(-1-lo))*arb(p)**(-1-hi)
            for k in range(first,16*step):
                a,b=arb(k)/step,arb(k+1)/step
                mid=(a+b)/2
                count=dens*(1-(a-b).exp())-2**(6+j)*(a-W-30).exp()
                v=(response(mid,vals)-response(mid-lp,vals)
                   -response(mid-W,vals)+response(mid-W-lp,vals))
                lower=abs(v)-2*(1+b)*(b-a)/2
                if lower>0 and count>0:
                    ans+=prob*(lo*(a-W)).exp()*count*(lower/W)**2
            unit*=1-arb(1)/p
        lowers.append(ans.lower())
    return min(lowers)


@lru_cache(None)
def rough_saving(width,prec):
    """Radicals whose smallest prime after 11 is between 101 and 499."""
    assert prec==ctx.prec
    W=arb(width)
    primes=[p for p in range(13,500) if fmpz(p).is_prime()]
    e1=e2=e3=arb(0)
    groups=[]
    for j,p in enumerate(primes,1):
        e3+=e2/p
        e2+=e1/p
        e1+=arb(1)/p
        if p<101:continue
        density=arb(480)/2310*(1-e1+e2-e3)/p
        disc=32*sum(comb(j,h) for h in range(4))
        groups.append((p,arb(p).log(),density,disc))
    lowers=[]
    for start in range(40,100,5):
        lo,hi=arb(start)/1000,arb(start+5)/1000
        vals=responses(start,start+5,prec)
        total=arb(0)
        for p,lp,density,disc in groups:
            prob=(1-arb(p)**(-1-lo))*arb(p)**(-1-hi)
            for k in range(16*32):
                a,b=arb(k)/32,arb(k+1)/32
                mid=(a+b)/2
                count=density*(1-(a-b).exp())-disc*(a-W-30).exp()
                if not count>0:continue
                val=response(mid,vals)-response(mid-lp,vals)
                lip=1+b
                if a>=W:
                    val=val-response(mid-W,vals)+response(mid-W-lp,vals)
                    lip*=2
                lower=abs(val)-lip*(b-a)/2
                if lower>0:
                    total+=prob*((lo if a>=W else hi)*(a-W)).exp()*count*(lower/W)**2
        lowers.append(total.lower())
    return min(lowers)


if __name__=="__main__":
    ctx.prec=160
    for w in ("8.5","9","9.5","10"):
        v=saving(w,ctx.prec)
        extra=rough_saving(w,ctx.prec)
        print(w,v.str(15),extra.str(15),flush=True)
        assert v>0 and extra>0
