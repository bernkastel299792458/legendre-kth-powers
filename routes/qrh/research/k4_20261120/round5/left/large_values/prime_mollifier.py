"""Critical joint second moment for a short Mobius core extended by a block of primes."""
from functools import lru_cache
from math import isqrt
from pathlib import Path
import sys
import numpy as np
from numba import njit
from flint import arb,ctx

sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from fast_short import arithmetic,intlog
from short_block import short_second as base_second
from gaussian_detector import fraction


@njit
def calculate(N,pr):
    spf,mu,ph,jl,lg=arithmetic(N,6)
    small=np.array([n for n in range(1,N+1) if mu[n]!=0 and np.gcd(n,6)==1])
    core=np.concatenate((small,pr))
    nc,ns=len(core),len(small)
    rank=np.zeros(N+1,np.int64)
    for i in range(ns):rank[small[i]]=i
    phi=np.empty(nc,np.int64)
    jlog=np.empty(nc,np.float64)
    logs=np.empty(nc,np.float64)
    signs=np.empty(nc,np.int64)
    offsets=np.zeros(ns+1,np.int64)
    for i in range(nc):
        n=core[i]
        if i<ns:
            signs[i],phi[i],logs[i],jlog[i]=mu[n],ph[n],lg[n],jl[n]
            v=n;length=1
            while v>1:v//=spf[v];length*=2
            offsets[i+1]=offsets[i]+length
        else:
            signs[i],phi[i]=-1,n-1
            logs[i]=intlog(n)
            jlog[i]=n*logs[i]/(n-1)
    divs=np.empty(offsets[-1],np.int64)
    for i in range(ns):
        lo=offsets[i];divs[lo]=1;n=core[i];length=1
        while n>1:
            p=spf[n]
            for z in range(length):divs[lo+length+z]=divs[lo+z]*p
            n//=p;length*=2
        for z in range(length):divs[lo+z]=rank[divs[lo+z]]
    rs=np.array([1,2,3,6],np.int64)
    pos=np.zeros(4,np.int64)
    state=np.zeros((4,nc),np.float64)
    A=B=G=GM=R=H=0.0
    K=4*nc
    ds=0
    for j in range(nc): H+=1.0/core[j]
    for ii in range(K):
        d=9223372036854775807
        ri=0
        for sel in range(4):
            if pos[sel]<nc:
                candidate=rs[sel]*core[pos[sel]]
                if candidate<d:
                    d,ri=candidate,sel
        j=pos[ri];pos[ri]+=1
        r,n=rs[ri],core[j]
        x=(mu[r]*signs[j])/d
        ld=lg[r]+logs[j]
        da=db=0.0
        for it in range(4):
            b=rs[it]
            if r%b:continue
            length=offsets[j+1]-offsets[j] if j<ns else 2
            for z in range(length):
                if j<ns:vi=divs[offsets[j]+z]
                else:vi=0 if z==0 else j
                old=state[it,vi]
                ch=ph[b]*phi[vi]*x*(2*old+x)
                da+=ch
                db+=ch*((jl[b]+jlog[vi])-ld)
                state[it,vi]=old+x
        A+=da;B+=db
        G+=(2*(K-ii)-1)/d;GM+=(2*ii+1)/d
        R+=1/np.sqrt(d);ds+=d
    return A,B,G,GM,R,H,ds,K,6*core[-1]


@lru_cache(maxsize=3)
def data(N,B,prec):
    assert ctx.prec==prec and 100<N<B<=2**28 and N<=2**23
    sieve=np.ones(B+1,dtype=bool)
    sieve[:N+1]=False
    for p in range(2,isqrt(B)+1):
        # Multiples of a composite have already been removed by its smallest prime.
        start=max(p*p,((N+1+p-1)//p)*p)
        sieve[start::p]=False
    primes=np.flatnonzero(sieve)
    del sieve
    aa,bb,g,gm,r,h,ds,K,L=calculate(N,primes)
    eps=arb(1)/2**52
    H=1+arb(L).log()
    e=64*(K+100)*eps*H**3
    rel=4*(K+3)*eps
    assert rel<arb("0.001") and K*L<2**62 and L<2**32
    return (arb(aa)+e,arb(bb)+e*(1+3*H),e,arb(g)/(1-rel),arb(gm)/(1-rel),
            arb(r)/(1-rel),arb(h)/(1-rel),ds,K,L,len(primes))


def prime_second(U,N,B):
    a,b,e,g,gmax,r,h,ds,K,L,_=data(N,B,ctx.prec)
    T=U.exp();y=(T/(2*arb.pi())).sqrt();H=1+arb(L).log()
    common=arb.const_euler()-(2*arb.pi()).log()/2
    di=a/2+(common*(a-2*e)+b).max(arb(0))/U+2*g/(y*U)
    avg=a/2+((common-arb(1)/2)*(a-2*e)+b).max(arb(0))/U
    avg+=h*(1+arb(1)/3)*(1+arb(1)/6)*ds/(3*y*y*U)
    off=4*(1+arb(L).log()+U/2)*(arb(K)**2/T+gmax*y/T)/U+16*r**2*y/(T*U)
    compact=36*(200+200**2//2)*r**2/T
    rem=(8/T.sqrt()+16*L*H/(arb(200).sqrt()*T))*H
    return (2*(di.min(avg)+off).sqrt()+((compact+(8*r**2/T.sqrt()).min(rem))/U).sqrt())**2


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser()
    cli.add_argument("--n",type=int,default=20)
    cli.add_argument("--b",type=int,default=26)
    args=cli.parse_args()
    ctx.prec=128
    N,B=2**args.n,2**args.b
    U=arb(35);s=arb(".85");S=prime_second(U,N,B)
    # Pairing with 1-beta costs at most 3(c-Theta)/(2(c-1/2)) of the original coefficient.
    c=2*s-arb(1)/2
    pair=3*(c-arb(7)/8)/(2*(c-arb(1)/2))
    f=fraction(U,U,850,512,S)*pair*(arb(".5")/(arb(".35")-arb("1e-39")))**2
    print("N,B,primes,K",N,B,data(N,B,ctx.prec)[-1],data(N,B,ctx.prec)[-3])
    print("upper A,B,S35, paired Gaussian fraction with cutoff .35",
          *[x.str(12) for x in (*data(N,B,ctx.prec)[:2],S,f)],flush=True)
