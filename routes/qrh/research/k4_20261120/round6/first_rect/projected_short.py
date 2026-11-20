"""Projected asymmetric AFE second moments of the short zero detector in a translated interval."""
from functools import lru_cache
from fractions import Fraction
from math import gcd
from flint import arb,ctx
import numpy as np
from periodic_local import period,folded
from periodic_fourth import harmonic,reciprocal_gap
from verify_fine import coarse
from short_block import short_second


@lru_cache(maxsize=None)
def coeffs(q,n,steps):
    """Signed upper gcd coefficients A,B, and absolute sums for the core coprime to q."""
    mu=coarse.mobius_up_to(n)
    inds=np.array([j for j in range(1,n+1) if mu[j] and gcd(j,q)==1],dtype=np.int64)
    z=np.array([int(mu[int(j)])*min((n//int(j)).bit_length(),steps) for j in inds],dtype=np.int64)
    K=len(inds); scale=2**42
    weights=np.zeros(n+1,dtype=np.int64)
    assert 2*steps**2*scale<2**62
    # Absolute exact harmonic gcd form is <=(1+log n)^3 before rounding.
    assert scale*(1+arb(n).log())**3+K*K<2**62
    for i in range(K):
        ds=inds[:i+1];g=np.gcd(ds,inds[i]);r=inds[i]//g
        zz=z[:i+1]*z[i]
        terms=np.sign(zz)*(scale*abs(zz)//(ds*r*steps**2))
        terms[:i]*=2
        np.add.at(weights,r,terms)
    rad=arb(K)**2/scale
    A=arb(int(weights.sum()))/scale+rad
    B=-sum((arb(int(weights[j]))*arb(int(j)).log() for j in np.flatnonzero(weights)),arb(0))/scale+rad*arb(n).log()
    prefix=arb(0);e1=e2=h2=m2=zroot=arb(0)
    tot=arb(sum(map(int,abs(z))))/steps
    for j,c0 in zip(inds,z):
        j=int(j);c=arb(abs(int(c0)))/steps
        e1+=c*(2*prefix+c)/j
        e2+=c*(2*(tot-prefix)-c)/j
        prefix+=c; h2+=c**2/j;m2+=c*c;zroot+=c/arb(j).sqrt()
    return A,B,tot,e1,e2,h2,m2,zroot


@lru_cache(maxsize=None)
def progression(q,dual,precision):
    w=np.array(list(map(abs,period(q,dual))),dtype=np.int64)
    rho=arb(int(w.sum()))/q
    vals=list(map(int,w))
    _,constant,error=harmonic(tuple(x*x for x in vals),ctx.prec)
    avg=arb(sum(x*x for x in vals))/q
    error=error.max(avg/arb(1).exp()+abs(constant))
    disc=arb(0)
    nums=np.arange(q,dtype=np.int64)
    c0=d0=c1=d1=arb(0)
    for r in range(1,q+1):
        at=w[nums]*w[(nums-r)%q]
        denom=int(at.sum())
        best=0
        for k in range(1,q):
            if gcd(k,q)!=1:continue
            seq=at[(k*nums)%q]
            before=np.cumsum(seq)-seq
            bot=int((q*before-denom*nums).min())
            top=int((q*(before+seq)-denom*nums).max())
            best=max(best,top-bot)
        c=arb(denom)/q; d=arb(best)/q
        kap=sum(arb(1)/(r+j*q) for j in range(16))-arb(r+15*q).log()/q
        c0+=c/q;d0+=d/q;c1+=c*kap;d1+=d*kap
    before=np.cumsum(w)-w
    disc=arb(int((q*(before+w)-int(w.sum())*nums).max())-int((q*before-int(w.sum())*nums).min()))/q
    return rho,avg,constant,error,disc,c0,c1,d0,d1


def projected(size,q,n,steps,alpha):
    D=arb(size);H=arb(3000175332800);R=D/2;C=H+R;v=arb("1.01")
    J=v*arb("1.02")*R;B0=C+v*R;M=2048;p=1+1/B0.log()
    rt=arb(q).sqrt();a=alpha*rt;b=rt/alpha
    A,B,K,smax,smin,h2,m2,zroot=coeffs(q,n,steps)
    pi=arb.pi();sides=[]
    for dual,scale in ((False,a),(True,b)):
        y=scale*((C+J)/(2*pi)).sqrt();yl=scale*((C-J)/(2*pi)).sqrt()
        mean,avg,c,er,disc,c0,c1,d0,d1=progression(q,dual,ctx.prec)
        assert yl>=q and n*y>16*q
        leading=avg*y.log()+c
        assert leading>0
        diag=J*(leading*A+avg*B+er*smin/yl)
        logshift=(n*y).log()
        off=2*((d0*logshift+d1)*K**2+(c0*logshift+c1)*y*smax)
        off+=reciprocal_gap(ctx.prec)*(zroot*(2*mean*y.sqrt()+disc))**2
        assert diag>0 and off>0
        value=(diag+off).sqrt()
        sides.append(value/rt if dual else value)
    kerr=16*(2*pi)**(arb(1)/4)*sum((arb(d)/a).sqrt().max((a/d).sqrt())/arb(d).sqrt()
                   for d in range(1,q+1) if q%d==0)
    rem=kerr*(C-J)**(-arb(1)/4)*folded(J*h2,m2,J,arb(1),arb(1),pi).sqrt()
    glob=short_second(B0.log(),q,n,steps)*B0*B0.log()
    return (sum(sides)+rem)**2+glob*M/(M-p)*arb("1.02")**(p-M)


@lru_cache(maxsize=None)
def best_projected(size,q,n,steps):
    if n>65536:return None
    return min(projected(size,q,n,steps,arb(a)) for a in ("1","1.5","2"))
