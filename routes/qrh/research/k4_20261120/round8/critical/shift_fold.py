"""Folded mean for a displaced, short-core-subtracted Mobius polynomial."""
from functools import lru_cache
from math import isqrt

import numpy as np
from flint import arb,ctx

from moving_line import exact
from fold_mean import partial_folds
from critical_mean import critical_mean


@lru_cache(None)
def head_groups(N,q,bits=8):
    valid=np.ones(N+1,dtype=bool)
    valid[0]=False
    for p in range(2,isqrt(N)+1):
        valid[p*p::p*p]=False
    for p in (2,3,5,7,11):
        if q%p==0: valid[::p]=False
    # Each block has endpoints in ratio at most 1+2^-bits.
    out=[]
    n=1
    while n<=N:
        last=min(N,n+(n>>bits))
        count=int(np.count_nonzero(valid[n:last+1]))
        if count:out.append((n,last,count))
        n=last+1
    return out


@lru_cache(None)
def weighted_head(N,q,hs,prec):
    assert ctx.prec==prec
    x=2*arb(hs)
    return sum((count*arb(n)**(x-1) for n,_,count in head_groups(N,q)),arb(0))


def shifted_cm(U,V,h,W,lh,q,base,N,tau=arb(0),depth=12):
    assert 0<=tau<=1 and arb(0)<h<arb(1)/8 and U<=V
    x=2*h
    hs=h.str(40,radius=False)
    assert abs(h-arb(hs))<arb("1e-35")
    # Round the power upwards separately, so the cached head majorizes it.
    H=weighted_head(N,q,hs,ctx.prec)*(arb("1e-34")*arb(N).log()).exp()
    from short_block import data
    HN=data(q,N,ctx.prec)[2]
    n=arb(N); T=V.exp()
    pieces=128
    # x>0. For physical index r*d the extra square weight is (r*d)^x.
    def mod(base,B,rs,v,t,order,ybar,eps,width,corr,U,X,pieces,
            harmonic,energy,rho,offset):
        e=(U+lh).exp()
        assert N<e
        Y=T*lh.exp();Z=Y*W.exp()
        C=2**sum(q%p==0 for p in (2,3,5,7,11))+2
        def tail(z):
            assert z>n
            head=(z.min(Y)**x-n**x)/x
            zero=(z.min(Y)/n).log()
            if z<=Y:return head,zero
            hi=z.min(Z)
            # Substitute y=Y exp(t), omega=1-t/W.
            def F(y):
                a=1-(y/Y).log()/W
                return y**x*(a**2/x+2*a/(W*x**2)+2/(W**2*x**3))
            a=1-(hi/Y).log()/W
            return head+F(hi)-F(Y),zero+W*(1-a**3)/3
        def newharmonic(cut,subtract=True):
            t0=tau if subtract else arb(0)
            total=harmonic(cut)-(2*t0-t0**2)*HN*sum(1/arb(r) for r in rs)/V
            for r in rs:
                z=T*cut/r
                assert z>n and U.exp()*cut/r>n
                rx=arb(r)**x
                high,zero=tail(z)
                factor=(r*n)**x
                err=C/n.sqrt()*(2*(factor-1)+factor/(1-2*x)-1)
                assert (1-x)*factor>1
                increment=(1-t0)**2*(rx*H-HN)+rho*(rx*high-zero)+err
                total+=increment/(r*U)
            return total
        def newenergy(l,rr,r):
            return energy(l,rr,r)*(T*rr.min(r*X))**x
        allharm=newharmonic(B*X,False)
        fake=allharm/sum(1/arb(r) for r in rs)
        return partial_folds(depth)(base,B,rs,v,t,order,ybar,eps,width,corr,U,X,pieces,
                        newharmonic,newenergy,fake,arb(0))
    return critical_mean(U,W,lh,pieces,q,base=base,fold=mod)


if __name__=="__main__":
    ctx.prec=160
    U=arb(37);V=U+arb(1)/2
    for v in (".00001",".0025",".005",".01",".02"):
        for tau in ("0",".75","1"):
            t=arb(tau);h=arb(v)
            m=shifted_cm(U,V,h,arb("9.5"),arb(-3),2310,210,2**18,t)
            print(v,tau,m.str(12),flush=True)
