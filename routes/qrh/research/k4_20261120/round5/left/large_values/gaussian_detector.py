"""Gaussian Mellin detector and optimistic Type-I block-cost obstruction."""
from functools import lru_cache
from math import factorial,isqrt
from pathlib import Path
import sys
import numpy as np
from flint import arb,arb_series,ctx

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from short_block import short_second

Q,N=210,32768
THETA=arb(7)/8
D=arb(3)/8
H=3000175332800


@lru_cache(maxsize=None)
def zprime(c_int,precision):
    assert precision==ctx.prec
    c=arb(c_int)/1000
    z=arb_series([c,1],prec=2).zeta()
    return -z[1]/z[0]


def fraction(lo,hi,j,scale,S):
    s=arb(j)/1000
    d=s-arb(1)/2
    c=2*s-arb(1)/2
    b=D*arb(2).sqrt()
    J=(D**2/b**2).exp()*arb.pi().sqrt()*b/(4*arb.pi()**2*(c-THETA))
    F=(hi-(2*arb.pi()).log())/2+zprime(2*j-500,ctx.prec)+arb(".001")
    p=3*(1-s)/(3*s-1)
    slope=1-2*d-p
    power=(slope*lo).max(slope*hi).exp()
    # The part of each critical integral with |v|>40 is less than 1e-40.
    # The sampling inequality uses (T+40)log(T+40)/(T log T)<1.00000001.
    return J*F*S*arb("1.00000001")*power*arb(scale)**(-2*d)/(7*(arb(1)/2-arb("1e-40"))**2)


def full_box(scale):
    best=arb(0)
    where=None
    for t in range(229,360):
        lo,hi=arb(t)/8,arb(t+1)/8
        if hi<arb(H).log():
            continue
        S=short_second(lo,Q,N)
        for j in range(800,875):
            f=fraction(lo,hi,j,scale,S)
            if f>best: best,where=f,(str(lo),j)
            elif not f<best: best=best.max(f)
    assert arb(229)/8<arb(H).log()<arb(230)/8
    return best,where


def phi(z):
    return (1+(z/arb(2).sqrt()).erf())/2


@lru_cache(maxsize=1)
def energies(precision):
    assert precision==ctx.prec
    s=arb(85)/100
    T=arb(35).exp()
    y=128*T
    b=D*arb(2).sqrt()
    assert phi(b*(y/2**26).log())>arb(".999")
    assert phi(b*(y/2**49).log())>arb(".99")
    M=2**26
    sieve=np.ones(M+1,dtype=bool)
    sieve[:2]=False
    for p0 in range(2,isqrt(M)+1):
        if sieve[p0]: sieve[p0*p0::p0]=False
    result=[]
    for j in range(15,49):
        m=2**j
        x=arb(m)
        if j<26:
            g=arb(0)
            for i in range(16):
                l,r=m+m*i//16,m+m*(i+1)//16
                cnt=int(np.count_nonzero(sieve[l+1:r+1]))
                g+=cnt*arb(r)**(-2*THETA)
            g*=arb(".999")**2
        else:
            cnt=2*x/(2*x).log()-arb("1.25506")*x/x.log()
            g=arb(".99")**2*cnt*(2*x)**(-2*THETA)
        result.append((j,x,g))
    return result


def obstruction():
    s=arb(".85")
    p=3*(1-s)/(3*s-1)
    T=arb(35).exp()
    target=245*(35*p).exp()
    total=small=arb(0)
    for j,x,g in energies(ctx.prec):
        # For k>=8 both advertised charges contain m^k times the coefficient energy.
        lower=(g*x).sqrt()*target**(-arb(1)/16)
        for k in range(1,8):
            no_collision=(1-arb(k*(k-1))/2*x**(-2*s)/g).max(arb(0))
            mult=(factorial(k)*no_collision).max(arb(1))
            energy=g.sqrt()*mult**(arb(1)/(2*k))
            mv=(T.max(x**k)/target)**(arb(1)/(2*k))
            hx=(x.sqrt()*target**(-arb(1)/(2*k))).max(x**(arb(1)/6)*(T/target)**(arb(1)/(6*k)))
            lower=lower.min(energy*mv.min(hx))
        total+=lower
        if j==25:small=total
    return small,total


def joint_thresholds(available=None,starts=(15,19,20,21,22),energy_rows=None):
    s=arb(".85")
    p=3*(1-s)/(3*s-1)
    T=arb(35).exp()
    target=245*(35*p).exp()
    if available is not None:
        target*=available
    out={j:arb(0) for j in starts}
    if energy_rows is None:
        energy_rows=energies(ctx.prec)
    # A dual feasible multiplier gives a rigorously rounded lower bound.
    for mi in (8,10,12,14,16,18,20,22,24,26,28,30,32,34,36,40):
        mu=arb(mi)/100
        def dual(a,h):
            frac=((h*a/mu)**(1/(1+h))).min(arb(1))
            return a/frac**h+mu*frac
        total=arb(0)
        for j,x,g in reversed(energy_rows):
            base=(g*x).sqrt()
            lower=base.min(dual(base*target**(-arb(1)/16),arb(1)/16))
            for k in range(1,8):
                no_collision=(1-arb(k*(k-1))/2*x**(-2*s)/g).max(arb(0))
                k2=arb(1)/(2*k)
                en=g.sqrt()*(factorial(k)*no_collision).max(arb(1))**k2
                mv=dual(en*(T.max(x**k)/target)**k2,k2)
                hx=dual(en*x.sqrt()*target**(-k2),k2).max(
                   dual(en*x**(arb(1)/6)*(T/target)**(k2/3),k2/3))
                lower=lower.min(mv.min(hx))
            total+=lower
            if j in out:
                out[j]=out[j].max(total-mu)
    return out


if __name__=="__main__":
    ctx.prec=160
    U=arb(35)
    S=short_second(U,Q,N)
    p=3*(1-arb(".85"))/(3*arb(".85")-1)
    target=245*(35*p).exp()
    assert phi(D*arb(2).sqrt()*(128*arb(H)).log())>1-arb("1e-30")
    for scale in (128,512):
        f=fraction(U,U,850,scale,S)
        whole,row=full_box(scale)
        print("scale",scale,"S35",S.str(12),"benchmark fraction",f.str(12),
              "count",(target*f).str(12),"full-box fraction",whole.str(12),"row",row,flush=True)
    short,all_blocks=obstruction()
    print("sum of necessary dyadic thresholds, first 11 and all 34",short.str(12),all_blocks.str(12))
    assert short>arb(".7065") and all_blocks>arb("1.0197")
    print("joint thresholds using full count budget",[(j,c.str(8)) for j,c in joint_thresholds().items()],flush=True)
