"""Gcd-prefix energy with dyadic logarithms and an explicit binary64 error budget."""
from functools import lru_cache
from math import prod
import numpy as np
from numba import njit
from flint import arb,ctx


@njit
def intlog(n):
    base=1
    h=0
    while 2*base<=n:
        base*=2
        h+=1
    y=(n-base)/(n+base)
    z=y*y
    poly=0.0
    for k in range(19,-1,-1):
        poly=1.0/(2*k+1)+z*poly
    return h*0.6931471805599453+2*y*poly


@njit
def arithmetic(nmax,q):
    # Only indices n <= nmax occur here. The squarefree q component is stored separately.
    bound=max(nmax,q)
    spf=np.zeros(bound+1,np.int64)
    mu=np.ones(bound+1,np.int64)
    phi=np.ones(bound+1,np.int64)
    jlog=np.zeros(bound+1,np.float64)
    logs=np.zeros(bound+1,np.float64)
    for p in range(2,bound+1):
        if spf[p]==0:
            for n in range(p,bound+1,p):
                if spf[n]==0:
                    spf[n]=p
    for n in range(2,bound+1):
        p=spf[n]
        x=n//p
        mu[n]=0 if x%p==0 else -mu[x]
        phi[n]=phi[x]*(p if x%p==0 else p-1)
        logs[n]=intlog(n)
        jlog[n]=jlog[x]+p*logs[p]/(p-1)
    return spf,mu,phi,jlog,logs


@njit
def prefixes(q,nmax,steps):
    spf,mu,phi,jlog,logs=arithmetic(nmax,q)
    core=np.array([n for n in range(1,nmax+1) if mu[n]!=0 and np.gcd(n,q)==1])
    divisors=np.array([r for r in range(1,q+1) if q%r==0])
    nc,nr=len(core),len(divisors)
    K=nc*nr
    rank=np.zeros(nmax+1,np.int64)
    for j in range(nc):
        rank[core[j]]=j
    nd=np.empty(K,np.int64)
    for i in range(nr):
        for j in range(nc):
            nd[i*nc+j]=divisors[i]*core[j]
    order=np.argsort(nd)
    sub=np.zeros((nr,nr),np.int64)
    nsub=np.zeros(nr,np.int64)
    for i in range(nr):
        for j in range(nr):
            if divisors[i]%divisors[j]==0:
                sub[i,nsub[i]]=j
                nsub[i]+=1
    offsets=np.zeros(nc+1,np.int64)
    for i in range(nc):
        n=core[i]
        num=1
        while n>1:
            n//=spf[n]
            num*=2
        offsets[i+1]=offsets[i]+num
    vsubs=np.empty(offsets[-1],np.int64)
    vw=np.ones(nc,np.int64)
    h1,h2=0.0,0.0
    for i in range(nc):
        n=core[i]
        x=n
        lo=offsets[i]
        vsubs[lo]=1
        l=1
        while x>1:
            p=spf[x]
            for z in range(l):
                vsubs[lo+l+z]=vsubs[lo+z]*p
            l*=2
            x//=p
        for z in range(l):
            vsubs[lo+z]=rank[vsubs[lo+z]]
        while vw[i]<steps and n*(2**vw[i])<=nmax:
            vw[i]+=1
        w=vw[i]/steps
        h1+=w/n
        h2+=w*w/n
    state=np.zeros((nr,nc),np.float64)
    A,B,G,R,Gmax=0.0,0.0,0.0,0.0,0.0
    for pos in range(K):
        ix=order[pos]
        i,j=ix//nc,ix%nc
        r,n=divisors[i],core[j]
        d=nd[ix]
        x=(mu[r]*mu[n]*vw[j])/(steps*d)
        ld=logs[r]+logs[n]
        da,db=0.0,0.0
        for tt in range(nsub[i]):
            bi=sub[i,tt]
            b=divisors[bi]
            for zz in range(offsets[j],offsets[j+1]):
                vi=vsubs[zz]
                v=core[vi]
                gphi=phi[b]*phi[v]
                old=state[bi,vi]
                change=(gphi*x)*(2*old+x)
                da+=change
                db+=change*((jlog[b]+jlog[v])-ld)
                state[bi,vi]=old+x
        A+=da
        B+=db
        G+=(2*(K-pos)-1)/d
        Gmax+=(2*pos+1)/d
        R+=1/np.sqrt(d)
    return A,B,h1,h2,G,R,K,nd[order[-1]],Gmax,np.sum(nd)


@lru_cache(maxsize=8)
def fast_data(q,nmax,precision,steps=1):
    """Protocol compatible with short_block.data, including A radius."""
    assert ctx.prec==precision and 1<=steps<=16 and nmax>=2**(steps-1)
    assert q%6==0 and prod(p for p in (2,3,5,7,11) if q%p==0)==q
    if q*nmax>=2**32 or nmax>2**24:
        raise ValueError("outside binary64 certification range")
    a,b,h1,h2,g,r,K,L,gmax,dsum=prefixes(q,nmax,steps)
    unit=arb(1)/2**52
    assert arb(K+100)*unit<arb(1)/1000
    assert abs(arb(0.6931471805599453)-arb(2).log())<unit
    H=1+arb(L).log()
    radius=64*(K+100)*unit*H**3
    bradius=radius*(1+3*H)
    rel=4*(K+3)*unit
    # Symmetric enclosures are needed for H1 and H2 in their signed combination.
    h1=arb(h1,arb(abs(h1))*rel/(1-rel))
    h2=arb(h2,arb(abs(h2))*rel/(1-rel))
    return (arb(a)+radius,arb(b)+bradius,h1,arb(g)/(1-rel),
            arb(r)/(1-rel),K,int(L),h2,radius,arb(gmax)/(1-rel),int(dsum))


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser()
    cli.add_argument("--q",type=int,default=210)
    cli.add_argument("--n",type=int,default=32768)
    cli.add_argument("--steps",type=int,default=1)
    args=cli.parse_args()
    ctx.prec=128
    a,b,h,g,r,k,l,h2,err,gmax,dsum=fast_data(args.q,args.n,ctx.prec,args.steps)
    print("upper A,B, A error radius",a.str(14),b.str(14),err.str(6),flush=True)
