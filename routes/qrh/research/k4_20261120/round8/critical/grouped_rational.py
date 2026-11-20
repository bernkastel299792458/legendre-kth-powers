"""Grouped rational projections with averaged gap sums and resolved saddle edges."""
from functools import lru_cache,partial
from math import isqrt
import numpy as np
from flint import arb,ctx,fmpz
from interference import covariance,reduction,finite,fourth as moving,period
from rational_fourth import fourth as rational
from twisted import constants


@lru_cache(None)
def counts(q, limit):
    assert 8 <= limit <= 4000000
    bins=[]
    a=1
    while a<=limit:
        b=min(limit,a+a//12)
        bins.append((a,b))
        a=b+1
    lo,hi=(np.array(x,dtype=np.int64) for x in zip(*bins))
    units=np.resize(np.array(period(q,False),dtype=np.int64),limit+1)
    units[0]=0
    np.cumsum(units,out=units)
    n=units[hi]-units[lo-1]
    ij=np.arange(limit+1,dtype=np.int64)
    linear=np.cumsum(ij*np.resize(np.array(period(q,False),dtype=np.int64),limit+1))
    sums=linear[hi]-linear[lo-1]
    bad=np.zeros((len(bins),len(bins)),dtype=np.int64)
    prime=bytearray([1])*(limit+1)
    prime[:2]=bytes(2)
    for p in range(2,isqrt(limit)+1):
        if prime[p]: prime[p*p::p]=bytes((limit-p*p)//p+1)
    ps=np.array([p for p in range(2,limit+1) if prime[p] and q%p],dtype=np.int64)
    assert (limit+1)**2*2+2*(limit+1)**2+limit<2**63
    for i in range(0,len(ps),256):
        p=ps[i:i+256,None]
        values=units[hi//p]-units[(lo-1)//p]
        bad+=values.T@values
    return bins,n,sums,bad


def geometry(U,slab,q,alpha,width,start):
    T=U.exp();pi=arb.pi();base=arb(q).sqrt()/(2*pi).sqrt()
    rho,_,_,_,_,du=constants(q,False,ctx.prec)
    _,_,_,_,scaled,disc=constants(q,True,ctx.prec)
    mu=scaled*arb(q).sqrt();disc*=arb(q).sqrt()
    X,Y=base*alpha*width.exp()*T.sqrt(),base/alpha*width.exp()*T.sqrt()
    def raw(dual,x):
        _,_,_,_,m,d=constants(q,dual,ctx.prec)
        return 2*m*x.sqrt()+d
    amplitudes=raw(0,X)*raw(1,Y)/T
    early=2*start/T*raw(0,X*(start/T).sqrt())*raw(1,Y*(start/T).sqrt())
    lamhi=(alpha*width.exp())**2;lamlo=(alpha*(-width).exp())**2
    delta=8/T.sqrt()
    assert delta<arb(".01")
    es=(arb(1)/2).exp();sh=arb(1).sinh()
    dlog=mu*(1+Y.log()+slab/2)+disc
    cg=arb(q).sqrt()
    def bound(r,s):
        R=r/s;w=R.log();root=(r*s).sqrt()
        lower=arb(0)
        for side,y in enumerate((X,Y)):
            den,head,er,maxsq,_,_=constants(q,side,ctx.prec)
            lo=y*(-(2*width)).exp()/r
            H=den*lo.log()+head-er/lo
            if not H>0:
                return arb(0),arb(0)
            gap=(2*y*(1+y.log())/s+(y/s+1)*(2+2*s.log()+2/s))
            off=(2*root*gap+8*y)*maxsq/T
            lower+=(1-start/T)*H-den/2-er/lo-root*off
        # lower is sqrt(rs) times a signed lower bound.
        C=q*T/(2*pi*R)
        A=B=tiny=arb(0)
        for sign in (-1,1):
            ratio=R**sign
            trunc=arb(1).min(arb(1).exp()/ratio)
            jmax=Y*trunc
            A+=es/cg*2*rho*(lamhi*ratio).sqrt()*sh*(mu*jmax+disc)
            B+=es/cg*du*dlog/(lamlo*ratio).sqrt()
            trunc=arb(1).min(delta.exp()/ratio)
            jmax=Y*trunc
            v=mu*base**2*T*trunc**2/2+disc*lamhi*jmax
            tiny+=2*rho*ratio*delta.sinh()*v+du*(mu*jmax+disc)
        A+=es/(q*C).sqrt()*2*rho*C*sh*dlog
        B+=es/(q*C).sqrt()*du*(mu*Y+disc)
        tiny+=2*rho*C*delta.sinh()*dlog+du*(mu*Y+disc)
        edges=2*(A*(1/delta).log()+B/delta)/T+9*(2*pi*R).sqrt()*tiny/(q*T)
        # The absolute periodic tails are averaged in n modulo Qs.
        P=q*s
        edge=du*Y+((X/P)+1)*(rho*q)*(P*(2+P.log()))
        principal=rho*w/root+2*pi*R.sqrt()*edge/(q*T)
        upper=(2/w+104)*amplitudes+edges+principal+early
        return lower,upper
    return bound


def improved(U,q,alpha,width,start,s2,v2,m,v,upper,M,limit):
    assert M<0
    prior=covariance(U,q,alpha,width,start,s2,v2,m,v,upper,M)
    gain,signed,h0=reduction(U,q,alpha,width,start,M)
    vr=(v2-gain/upper**4).max(0)
    sr=(s2-m*m/upper**4).max(0)
    if not gain>0 or not vr>0 or not sr>0:
        return prior
    ratio=(vr/sr).sqrt()
    kappa=(upper/U)**4/ratio
    T=U.exp()
    hilb=arb(1)/2+arb("4.2")*(limit**2+1)/T
    bins,ns,sums,bad=counts(q,limit)
    harmonic=[arb(int(n))**2/int(m) if n else arb(0) for n,m in zip(ns,sums)]
    bound=geometry(U,upper-U,q,alpha,width,start)
    arguments=[arb(arb(a+b)/2,arb(b-a)/2) for a,b in bins]
    base=arb(".25")+(q*arb(start)/(2*arb.pi())).log()/2
    cutoff=(q*T/(2*arb.pi())).sqrt()*alpha.min(1/alpha)*(-width-arb(".25")).exp()
    M0=max(1,int(cutoff.lower().floor().unique_fmpz())-1)
    benefit=arb(0)
    for i,((a,b),r) in enumerate(zip(bins,arguments)):
        for j in range(i):
            if not ns[i] or not ns[j]:
                continue
            c,d=bins[j];s=arguments[j]
            pairs=harmonic[i]*harmonic[j]-arb(int(bad[i,j]))/(a*c)
            if not pairs>0:
                continue
            # Bound real-coordinate functions on the entire closed bin pair.
            w=(r/s).log()
            diff=base-w
            if not w>0:
                continue
            l,h=bound(r,s)
            R=r/s
            early=2*(2*arb.pi()*R**2/(q*T))*(h0*arb(".25")*T/4)*(R/M0).sqrt()
            short=h0+early
            if diff>0:
                short=short.min(h0*arb(".25")/diff)
            alpha_lo=(l-(r*s).sqrt()*(m/(T*w)+kappa*(h+short))).lower()
            if alpha_lo>0:
                benefit+=alpha_lo**2*pairs
    revised=s2+v2+2*(sr*vr).sqrt()+2*(m*v+signed+m*h0)/U**4
    revised-=ratio*benefit/(hilb*upper**4)
    return prior.min(revised)


def fourth(U,q=210,alpha=arb(1),width=arb(".04"),Z=384,limit=65536):
    if U>64:return moving(U,q,alpha,width,Z)
    callback=partial(improved,limit=limit)
    lengths = (arb(".125"),arb(".25"),arb(".625"))
    edge=U
    result=rational(U+1,q,alpha,width,Z)
    for length in lengths:
        result=result.max(finite(edge,q,alpha,width,Z,length,-1,callback))
        edge+=length
    return result


if __name__=="__main__":
    ctx.prec=160
    for i,ceiling in ((35,".001147673"),(37,".000997554"),(40,".000850665")):
        U=arb(i)
        result=fourth(U)
        assert result<arb(ceiling)
        print("grouped saddle",i,result.str(14),flush=True)
