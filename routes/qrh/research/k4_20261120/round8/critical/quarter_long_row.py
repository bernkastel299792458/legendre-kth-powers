"""The long e=1 stationary row, completed in its larger raw index."""
from math import gcd,isqrt,prod

import numpy as np
from flint import arb,ctx

from quarter_diagonal import primes
from quarter_signed_block import periodic,harmonic
from quarter_negative import geometry,atoms
from quarter_far_pairs import positive_prefix


def mobius(q,n):
    prime=np.ones(n+1,dtype=bool);prime[:2]=False
    for p in range(2,isqrt(n)+1):
        if prime[p]:prime[p*p::p]=False
    mu=np.ones(n+1,dtype=np.int8);mu[0]=0
    for p in np.flatnonzero(prime):
        p=int(p)
        if q%p:
            mu[p::p]*=-1;mu[p*p::p*p]=0
        else:
            mu[p::p]=0
    return mu


def prefix(mu):
    n=len(mu)-1;scale=2**44
    assert 1+arb(n).log()<100 and n<10**9
    k=np.arange(1,n+1,dtype=np.int64)
    s=np.cumsum((scale*mu[1:].astype(np.int64))//k,dtype=np.int64)
    return s,scale


def mobius_bound(q,d0,top=10**7):
    s,scale=prefix(mobius(q,top))
    local=arb(int(np.max(abs(s[d0-2:])) )+top)/scale
    ref,den=prefix(mobius(1,100000))
    lid=np.maximum.accumulate(abs(ref)[::-1])[::-1]
    B=arb(1)/(69*arb(96955).log())
    cap=10**14;hs=[1]
    for p in primes(q):
        for h in hs.copy():
            n=h*p
            while n<=cap:
                hs.append(n);n*=p
    total=prod(1/(1-1/arb(p)) for p in primes(q));mass=acc=arb(0)
    for h in hs:
        x=arb(top)/h
        if x>=96955:v=1/(69*x.log())
        elif h>top:v=arb(1)
        else:v=B.max(arb(int(lid[top//h-1])+len(lid))/den)
        mass+=1/arb(h);acc+=v/h
    return local.max(acc+total-mass)


def matrices(q):
    # Integer upper bounds for all running trigonometric discrepancies.
    den=2**25;co=[];si=[]
    for k in range(q):
        angle=2*arb(k)/q
        co.append(int((den*angle.cos_pi()).lower().floor().unique_fmpz()))
        si.append(int((den*angle.sin_pi()).lower().floor().unique_fmpz()))
    co=np.array(co,dtype=np.int64);si=np.array(si,dtype=np.int64)
    js=np.arange(1,q+1,dtype=np.int64);unit=(np.gcd(js,q)==1).astype(np.int64)
    c=np.array([prod(p-1 if k%p==0 else -1 for p in primes(q)) for k in js],dtype=np.int64)
    assert q*q*q*den<2**63
    ds={};dj=0
    for k in range(q):
        idx=k*js%q;g=gcd(k,q)
        def variation(x,y,scale,error):
            x=np.cumsum(x,dtype=np.int64);y=np.cumsum(y,dtype=np.int64)
            # Include the prefix at index zero.
            dx=max(0,int(x.max()))-min(0,int(x.min()))
            dy=max(0,int(y.max()))-min(0,int(y.min()))
            return int(((arb(dx**2+dy**2).sqrt()+error)/scale).upper().ceil().unique_fmpz())+1
        v=variation(q*unit*co[idx]-int(c[k-1])*den,q*unit*si[idx],q*den,4*q*q)
        ds[g]=max(ds.get(g,0),v)
        if g==1:
            dj=max(dj,variation(c*co[idx]-den,c*si[idx],den,4*int(sum(abs(c)))))
    b1=[dj*int(x) for x in unit]
    b2=[int(abs(z))*ds[gcd(i+1,q)] for i,z in enumerate(c)]
    nbest,dbest,csum=0,1,0
    for i,v in enumerate(c,1):
        csum+=abs(int(v))
        if csum*dbest>nbest*i:nbest,dbest=csum,i
    cp=arb(nbest)/dbest
    return dj,ds,b1,b2,cp


def lattice(q,N,lo,eta,which):
    # Sum small index k exactly through L=32q, then use a positive periodic tail.
    a=arb(1)/2
    dj,ds,b1,b2,cp=which
    Cdisc=arb(2**len(primes(q)))
    cut=32*q
    total=arb(0)
    def term(k,d,b,cap):
        # Single-cell discrepancy at fixed k bounded by min(d,cap*N/(k*l))
        # for an outer mollifier index l.  The decreasing integral + unit error
        # also covers all l>=1; only the discrepancy uses the real lo below.
        y=N/k**2
        t0=cap*N/(d*k)
        if t0<y:
            v=2*d*t0.sqrt()+2*cap*N/k*(1/t0.sqrt()-1/y.sqrt())
        else:
            v=2*d*y.sqrt()
        return b*(eta*v+Cdisc*d/lo.sqrt())/arb(k).sqrt()
    for k in range(1,cut+1):
        i=(k-1)%q
        if b1[i]:total+=term(k,dj,1,cp+1)
        if b2[i]:
            dd=ds[gcd(k,q)]
            total+=term(k,dd,b2[i]//dd,2)
    for b in (b1,b2):
        mean=arb(sum(b))/q
        # Nonnegative period, sum of all entries bounds the interval discrepancy.
        dd=arb(sum(b))
        tail=2*mean/arb(cut).sqrt()+2*dd/arb(cut)**(arb(3)/2)
        L=(N/lo).sqrt()
        pows=2*mean*L.sqrt()+2*dd
        total+=2*eta*N.sqrt()*tail+Cdisc*pows/lo.sqrt()
    return total*4*arb.pi()/q


def result(d0=100000,q=2310):
    assert 2<=d0<=10**7 and q==2310
    U=arb(37);T=U.exp();alpha=arb(64);w=arb('.75');eps=arb('.03')
    K=arb('2.25e12');ts=arb('1.5e12');m=2048;P=128;D=arb('1.01')*T
    a=arb(1)/2;sg=arb(3)/4;z=a/2;pi=arb.pi()
    eta,C,osc=periodic(q,ctx.prec)
    low,high,tc,inner,outer,yf=geometry(q,str(U),str(alpha),str(w),ctx.prec)
    _,yr,raw,_,ram=atoms(U,alpha,w,q)
    bound=mobius_bound(q,d0)
    mu=mobius(q,d0)
    occ=np.flatnonzero(mu[1:])+1
    # True sum for the first full d-row uses one common continuous integral.
    # The piece with d=1 vanishes.
    h=absd=half=count=arb(0)
    for d in occ:
        d=int(d)
        if d==1:continue
        v=arb(d);hh=1/v.sqrt()
        h+=int(mu[d])*(1-hh)/d
        absd+=hh.sqrt()*hh;half+=hh;count+=1
    genuine_small=(high if h>0 else low)*h+tc*absd+inner*half+outer*count
    N2=q*2*T/(2*pi);N=N2*(2*eps).exp()
    # Entire frequency-cutoff dependent AFE remainder on the remaining indices.
    eta,Cs=positive_prefix(q,'direct',ctx.prec)
    unitmax=eta/(1-sg)+Cs
    table=matrices(q)
    # Absolute dual coefficient power prefixes bounded by the mean and finite period.
    cs=[prod(p-1 if k%p==0 else -1 for p in primes(q)) for k in range(1,q+1)]
    sh=arb(0);Ch=arb(0)
    for k,v in enumerate(cs,1):
        sh+=abs(v)/arb(k).sqrt();Ch=Ch.max(sh-2*ram*arb(k).sqrt())
    Ch=Ch.max(sh-2*ram*arb(q).sqrt()+2*sum(abs(v) for v in cs)/arb(q).sqrt())
    atom=2/arb(q).sqrt()*(q*ts/(2*pi))**(-z)*unitmax*N**(1-sg)*(2*ram*yr.sqrt()+Ch)
    atom*=eta*(N/d0).log()+2*arb(2**len(primes(q)))/d0
    speed=2*P*(K/ts)**(-z)+z+(m+z)*(D/ts)**(-z)
    edge=(ts/K)**(2*P)*ts/(2*P-z+1)+(D/(2*T))**m*2*T/(m-1)
    edge+=((ts/K)**(2*P)*ts.sqrt()+(D/(2*T))**m*(2*T).sqrt())*(2*pi).sqrt()
    time=atom*(18+2*speed+3/w+7/eps+edge)
    lattice_error=lattice(q,N2,arb(d0),eta,table)
    # Continuous longer index, original short index. The outer Möbius interval
    # costs 2B after any positive decreasing taper/weight is partially summed.
    population=two=arb(0)
    harmonic_short=harmonic((N2/d0).sqrt(),q,eta)
    # The u-small half has integral from the time substitution j=N_t/(d*u).
    population+=4*bound*harmonic_short*(a/(2*eta))*high
    # The j-small half retains c_q(j)^2/q and integrable weight j^(a-1).
    scale=(q/(2*pi))**(-a)*D**(1-a)*(1/(1-a)+1/(m+a-1))
    Kr=prod(1+(p-2)*arb(p)**a for p in primes(q))/(q*a)
    two=4*bound*(high/2+Kr*scale)
    return genuine_small,bound,time,lattice_error,population,two


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--cut',type=int,default=100000)
    ctx.prec=144
    out=result(ap.parse_args().cut)
    print('small true row, reciprocal Mobius supremum, upper tail time, lattice, u-short, j-short',
          *(v.str(11) for v in out),flush=True)
    print('complete physical e=1 upper, excluding already paid nonstationary part for large d',
          (out[0]+sum(out[2:])).str(12),flush=True)
