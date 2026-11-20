"""A rigorously rounded harmonic gcd form for a fixed, short, sharp mollifier."""
from functools import lru_cache
from math import gcd, prod
from pathlib import Path
import sys
import numpy as np
from flint import arb,ctx

from six_energy import research,fourth
sys.path.insert(0,str(research/"round4"/"hilbert"))
from linear_mean import linear_mean_coefficients


@lru_cache(maxsize=4)
def data(q,nmax,precision,steps=1):
    assert precision==ctx.prec
    assert 1<=steps<=16 and nmax>=2**(steps-1)
    if nmax>=32768:
        from fast_short import fast_data
        return fast_data(q,nmax,precision,steps)
    mu=np.ones(nmax+1,dtype=np.int64)
    primes=np.ones(nmax+1,dtype=np.bool_)
    for p in range(2,nmax+1):
        if primes[p]:
            mu[p::p]*=-1
            mu[p*p::p*p]=0
            primes[2*p::p]=False
    divisors=[(1,1)]
    for p in (2,3,5,7,11):
        if q%p==0:
            divisors+= [(r*p,-s) for r,s in divisors]
    if max(r for r,s in divisors)!=q:
        raise ValueError("modulus must divide 2310")
    core=[n for n in range(1,nmax+1) if gcd(n,q)==1 and mu[n]]
    weights_core={n:min((nmax//n).bit_length(),steps) for n in core}
    coeff=sorted((r*n,s*int(mu[n])*weights_core[n]) for n in core for r,s in divisors)
    inds=np.asarray([n for n,s in coeff],dtype=np.int64)
    vals=np.asarray([s for n,s in coeff],dtype=np.int64)
    K=len(inds)
    L=int(inds[-1])
    scale=2**44
    if not ((1+arb(L).log())**3*scale<2**62 and max(scale,L*L)*steps**2<2**62):
        raise ValueError("integer accumulator range")
    weights=np.zeros(L+1,dtype=np.int64)
    for i in range(K):
        g=np.gcd(inds[:i+1],inds[i])
        j=inds[i]//g
        numerator=vals[:i+1]*vals[i]
        amounts=np.sign(numerator)*((scale*np.abs(numerator))//(inds[:i+1]*j*steps**2))
        amounts[:i]*=2
        np.add.at(weights,j,amounts)
    # Signed forms A and B use the same integer-quantized coefficients.
    rounding=arb(K)**2/scale
    a=arb(int(weights.sum()))/scale+rounding
    b=-sum((arb(int(weights[i]))*arb(int(i)).log() for i in np.flatnonzero(weights)),arb(0))/scale
    b+=rounding*arb(L).log()
    harmonic=sum((arb(weights_core[k])/(steps*k) for k in core),arb(0))
    harmonic2=sum((arb(weights_core[k]**2)/(steps**2*k) for k in core),arb(0))
    err=sum((arb(2*(K-i)-1)/int(n) for i,n in enumerate(inds)),arb(0))
    gmax=sum((arb(2*i+1)/int(n) for i,n in enumerate(inds)),arb(0))
    rootmass=sum((1/arb(int(n)).sqrt() for n in inds),arb(0))
    return a,b,harmonic,err,rootmass,K,L,harmonic2,rounding,gmax,sum(int(n) for n in inds)


def short_second(U,q,nmax,steps=1):
    """Upper coefficient of integral_0^Z |zeta M_short|^2 /(Z log Z), Z>=exp(U)."""
    a,b,h1,err,rootmass,K,L,_,rounding,gmax,dsum=data(q,nmax,ctx.prec,steps)
    t=U.exp()
    y=(t/(2*arb.pi())).sqrt()
    # At a diagonal, H_{y/max(r,s)} differs from log plus gamma by at most max(r,s)/y.
    # The coefficient a bounds the nonnegative gcd energy by a Jordan-totient expansion.
    alo=a-2*rounding
    diag=a/2+((arb.const_euler()-(2*arb.pi()).log()/2)*alo+b).max(arb(0))/U
    diag+=2*err/(y*U)
    hl=1+arb(L).log()
    averaged=a/2+((arb.const_euler()-(2*arb.pi()).log()/2-arb(1)/2)*alo+b).max(arb(0))/U
    divisor_factor=prod(1+arb(2)/(p*(p+1)) for p in (2,3,5,7,11) if q%p==0)
    averaged+=h1*divisor_factor*dsum/(3*y**2*U)
    diag=diag.min(averaged)
    # Each shift d*m-g*n is a multiple of (d,g). Rank-one product frequencies.
    off=4*(1+arb(L).log()+U/2)*(arb(K)**2/t+gmax*y/t)/U
    off+=16*rootmass**2*y/(t*U)
    # The large-height pointwise RS remainder is <=2*t^-1/4 |M_s|.
    # Its square contributes <=8 sqrt(Z)*rootmass^2. The initial compact
    # interval is bounded by the same trivial polynomial majorant.
    compact=36*(200+200**2//2)*rootmass**2/t
    remainder=(8/t.sqrt()+16*L*hl/(arb(200).sqrt()*t))*hl
    tail=((compact+(8*rootmass**2/t.sqrt()).min(remainder))/U).sqrt()
    return (2*(diag+off).sqrt()+tail)**2


def cm_old(U,W,logh,q):
    """Baseline round-four folded mean, with the diagonal coefficient returned separately."""
    v=arb("1.01")
    T=U.exp()
    order=2048
    diag,hilb=linear_mean_coefficients(6,v*T,v*order/(order-1))
    div={1:1}
    for p in (2,3,5,7,11):
        shift=p if not q%p else p**2
        div.update({n*shift:-sg for n,sg in div.copy().items()})
    assert T*logh.exp()>max(div)
    den=sum((arb(sg)/n for n,sg in div.items()),arb(0))
    intercept=sum(((max(sg,0)-sg*arb(n).log())/n for n,sg in div.items()),arb(0))
    h=den+(den*(W/3+logh)+intercept).max(arb(0))/U
    tap=2*(W+logh).exp()*(1-(1+W)*(-W).exp())/W**2
    count=den*tap+sum(sg<0 for sg in div.values())/T
    rem=[p for p in (5,7,11) if not q%p]
    r=prod(1+arb(1)/p for p in rem)
    return diag*r*h+hilb*2**len(rem)*count/U,diag


def cm_local(U,W,logh,q):
    """Host critical_mean multiplier, and a lower coefficient for its small-frequency harmonic."""
    sys.path.insert(0,str(research/"round5"/"spectrum"))
    from critical_mean import critical_mean
    v,tau,m=arb("1.01"),arb("1.03"),2048
    near_average=v*m/(m-1)*(1-tau**(1-m))
    return critical_mean(U,W,logh,q=q),near_average


def normalized_row(U,V,q,nmax,W,logh,cm_source,steps=1,*,fourth_fn=None,sieve_base=6,small_factor=1):
    """Uniform endpoint on U<=log T<=V. V=None activates the baseline on the final half-line."""
    assert sieve_base in (6,30,210) and q%sieve_base==0 and arb(nmax)<(U+logh).exp()
    m,v=2048,arb("1.01")
    assert 0<small_factor<=1
    assert (q//sieve_base)*nmax<sieve_base*small_factor*v*arb("1.03")/arb.pi()*U.exp()
    ybar=v*m/(m-1)
    cm,diagonal=cm_source(U,W,logh,q)
    moment=fourth if fourth_fn is None else fourth_fn
    c4=(moment(U)*v**(1+4/U)*m/(m-1-4/U))**(arb(1)/4)
    unit=ybar**(arb(3)/4)/U**(arb(3)/2)
    initial=(c4*cm.sqrt()+unit)**(arb(4)/3)
    if V is None:
        return initial,initial,arb(0)
    r=prod(1+arb(1)/p for p in (2,3,5,7,11) if (q//sieve_base)%p==0)
    _,_,h,_,l1,_,_,h2,_,_,_=data(q,nmax,ctx.prec,steps)
    shrink=diagonal*r/V
    short=short_second(U,q,nmax,steps)*v**(1+1/U)*m/(m-1-1/U)
    error=40*(1+l1)*ybar.sqrt()*(-U/2).exp()/U
    best,tbest=initial,arb(0)
    for i in range(1,101):
        tau=arb(i)/100
        res=cm-(2*tau*h-tau**2*h2)*shrink
        assert res>0
        # Include the subtracted constant in the short piece. The real first
        # moment of zeta*M_short is T plus an explicit contour-shift error.
        constant=(1-2*tau).max(arb(0))/U+(1-2*tau).min(arb(0))/V
        joint=tau**2*short+constant*ybar+tau*error
        assert joint>0
        candidate=(c4*res.sqrt()+ybar**(arb(1)/4)*joint.sqrt()/U)**(arb(4)/3)
        if candidate<best:
            best,tbest=candidate,tau
    return best,initial,tbest


def split_endpoint(U,W,logh,q=210,nmax=2048,cm_source=cm_old,steps=1,*,fourth_fn=None):
    """Compute the best certified row bound with a finite partition and a final baseline."""
    rows=[normalized_row(U+i,U+i+1,q,nmax,W,logh,cm_source,steps,fourth_fn=fourth_fn)
          for i in range(8)]
    rows.append(normalized_row(U+8,None,q,nmax,W,logh,cm_source,steps,fourth_fn=fourth_fn))
    largest=arb(0)
    for row in rows:
        largest=largest.max(row[0])
    return largest,rows


if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser()
    ap.add_argument("--n",type=int,default=2048)
    ap.add_argument("--split",action="store_true")
    ap.add_argument("--local",action="store_true")
    ap.add_argument("--q",type=int,default=210)
    ap.add_argument("--steps",type=int,default=1)
    ap.add_argument("--u",default="43")
    args=ap.parse_args()
    ctx.prec=128
    A,B,H,_,_,K,L,_,_,_,_=data(args.q,args.n,ctx.prec,args.steps)
    print("A,B,harmonic, K, L",A.str(12),B.str(12),H.str(12),K,L,flush=True)
    print("joint second",short_second(arb(args.u),args.q,args.n,args.steps).str(12),flush=True)
    if args.split:
        best,rows=split_endpoint(arb(args.u),arb("9.5"),arb("-3.5"),q=args.q,nmax=args.n,
                                 cm_source=cm_local if args.local else cm_old,steps=args.steps)
        print("K1 baseline, improved, tau on first row",rows[0][1].str(12),best.str(12),rows[0][2].str(4))
