"""Positive harmonic continuation from both boundaries, local and global tests."""
from functools import lru_cache
from math import comb,factorial,isqrt
from pathlib import Path
import sys
from types import FunctionType

from flint import arb

sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round7"/"qrh_strip"))
import increment
from strip_positive import H,T,PI,THETA,S,kernel


bb=THETA-arb(1)/2
bmax=(T/(2*PI)).log()/4+arb(".0001")
fail=420071
def coefficient(lp,k,A):
    u=k*lp
    return lp*(-THETA*u).exp()*(1-u/A)/(1+(-2*bb*u).exp())


def arch_check():
    h=H-1
    d=H/10000
    assert 4/arb(20)+PI*bb/2<1
    near=(1+(d+1)/h).log()+4/(h-d)
    tail=2/(PI*d)*((T+3).log()+(1+d).log()+3)
    poles=2*arb(66)*arb(30).exp()/h**2
    assert near/4+tail/4+poles<arb(".0001")


def profile(A,y):
    if y==0:
        return kernel(THETA-S,y,A)-bmax
    assert y>0 and A*y<=arb("2.0000001")
    width=(A-PI/(2*y)).max(0)
    correction=width**2/(2*A)*(1-(-(THETA-S)*A).exp())*(y*A-PI/2).max(0)
    return kernel(THETA-S,y,A)-correction-bmax


_arith=FunctionType(increment.arithmetic.__code__,
                    dict(increment.arithmetic.__globals__,coefficient=coefficient))
@lru_cache(maxsize=24)
def data(Ai,X):
    A=arb(Ai)
    th,ds,small=_arith(A,X)
    h0,h1=[increment.long_norm(k,th,A,X) for k in (0,1)]
    return ds,small,h0,h1


def local(Ai,X,width,D,b):
    A,W,d,b=map(arb,(Ai,width,D,b))
    assert 20<=A<=60
    ds,small,h0,h1=data(Ai,X)
    factor=[arb(comb(3,k))**2*b**(6-2*k)*factorial(k) for k in range(4)]
    mm=[sum((v*x**k for k,v in enumerate(factor)),arb(0)) for x in ds]
    w=W+4/A
    hh=increment.HILBERT
    low=arb(4)/(27*(d+b)**2)*((w+hh)*mm[0]+hh*mm[1]).sqrt()
    high=(((w+hh)*h0+hh*h1)/2).sqrt()
    n=512
    cost=4/(A*n)*sum(((profile(A,2*i/(A*n))-d-small).max(0)**2 for i in range(1,n+1)),arb(0))
    cap=(low+high)**2/cost
    print("width",width,"four parameters",Ai,X,D,b,"true cap",cap.str(14))
    return cap


def global_phase(Ai,X=160000):
    A=arb(Ai)
    assert 20<=A<=60
    ps=bytearray([1])*(X+1)
    ps[:2]=bytes(2)
    for n in range(2,isqrt(X)+1):
        if ps[n]:ps[n*n::n]=bytes((X-n*n)//n+1)
    th=arb(0); V=arb(0); E=arb(0); ranks=[]
    cut=int(A.exp().floor().unique_fmpz())
    for p in range(2,X+1):
        if not ps[p]:continue
        lp=arb(p).log();th+=lp
        first=coefficient(lp,1,A)
        ranks.append(first)
        V+=first
        z=p*p;k=2
        while z<=cut:
            E+=coefficient(lp,k,A)
            z*=p;k+=1
    u=arb(X).log()
    decay=2*THETA-1
    E+=(-decay*u).exp()*(u/decay+1/decay**2)/(1-(-THETA*u).exp())
    k=1-THETA;rs=arb("1.01624")
    def primitive(t):
        return (k*t).exp()*((1-t/A)/k+1/(A*k*k))
    V+=rs*(primitive(A)-primitive(u))+(rs*X-th)*(-THETA*u).exp()*(1-u/A)
    D=profile(A,arb(0))-E
    ratio=D/V
    print("band",Ai,"upper prime norm",V.str(10),"lower signed sum per zero",
          D.str(10),"prime-phase bias",ratio.str(10))
    # Use only a sorted prefix for the comparison; order is certified afterwards.
    ranks.sort(key=float,reverse=True)
    for goal in (".005",".01",".025",".05"):
        g=arb(goal);target=(D-g*V)/(1-g)
        if target<=0:continue
        total=arb(0);m=0
        while m<len(ranks) and total+ranks[m]<target:
            total+=ranks[m];m+=1
        assert 0<m<len(ranks) and all(ranks[i]>ranks[i+1] for i in range(m))
        assert all(z<=ranks[m-1] for z in ranks[m:])
        assert (-THETA*u).exp()*u < ranks[m-1]
        print("bias",goal,"requires at least",m+1,"distinct primes")
    return ratio,V,D


def distant_pairs(bias,span=450):
    # Each reflected pair at |gamma-t|<=span contributes an interval integral
    # >=4 atan(B/1.5). The arithmetic term on the 2-line has a primitive.
    B=arb(21)
    gamma=( (T+2*span+2*B)/(2*PI) ).log()/2+arb("1e-9")
    cap=(2*(span+B)*gamma+2*arb(2).zeta().log())/(4*(B/arb("1.5")).atan())
    lower=bias*bias-cap/fail
    print("long signed pairs cutoff",span,"near row cap",cap.str(12),
          "normalized long signed pair sum / R^2",lower.str(12))
    return lower


if __name__=="__main__":
    arch_check()
    print("H, T",H.str(14),T.str(14))
    for p,n in [((47,250000,10**9,4,".27"),658676),
                ((42,65000,116000000,"3.2",".48"),256863),
                ((44,130000,375000000,"3.86",".30"),419291)]:
        assert local(*p)<n
    for a in (26,36,40,45,50):
        bias,V,D=global_phase(a)
        if a==26:
            assert bias>arb(".07612") and distant_pairs(bias)>arb(".0004")
