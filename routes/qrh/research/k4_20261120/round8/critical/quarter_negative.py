"""A genuinely negative family of saddle contributions on the three-quarter line."""
from math import gcd
from functools import lru_cache
from flint import arb,ctx,fmpz
from quarter_diagonal import primes,signed
from quarter_far_pairs import positive_prefix


def atoms(U,alpha,w,q):
    T=U.exp();sg=arb(3)/4;a=2*sg-1;ts=arb('1.5e12')
    top=(q*2*T/(2*arb.pi())).sqrt()
    yf=alpha*w.exp()*top;yr=w.exp()/alpha*top
    eta,C=positive_prefix(q,'direct',ctx.prec)
    ram,Cr=positive_prefix(q,'dual',ctx.prec)
    mass=(C+eta*yf**(1-sg)/(1-sg))*(Cr+ram*yr**sg/sg)
    mass/=arb(q).sqrt()*(q*ts/(2*arb.pi()))**(a/2)
    return yf,yr,mass,eta,ram


@lru_cache(None)
def geometry(q,Ustr,astr,wstr,prec):
    assert ctx.prec==prec
    U,alpha,w=map(arb,(Ustr,astr,wstr))
    sg=arb(3)/4;a=2*sg-1;z=a/2
    T=U.exp();K=arb('2.25e12');ts=arb('1.5e12')
    D=arb('1.01')*T;m=2048;P=128;pi=arb.pi()
    yf,yr,mass,eta,ram=atoms(U,alpha,w,q)
    # Working in log time, every regular derivative is piecewise monotone.
    speed=(2*P)*(K/ts)**(-z)+z+(m+z)*(D/ts)**(-z)
    smooth=2*speed+2/w
    # Constant-amplitude Fresnel replacement, and the extension of both endpoints.
    edge=(ts/K)**(2*P)*ts/(2*P-z+1)+(D/(2*T))**m*2*T/(m-1)
    saddle_edge=((ts/K)**(2*P)*ts.sqrt()+(D/(2*T))**m*(2*T).sqrt())*(2*pi).sqrt()
    time0=2*mass*(18+smooth+edge+saddle_edge)
    pfx=0;lo=hi=arb(0)
    for j in range(1,q+1):
        lo=lo.min(pfx-eta*j);pfx+=int(gcd(j,q)==1);hi=hi.max(pfx-eta*j)
    delta=hi-lo+1
    Sunit=eta*yf**(1-a)/(1-a)
    # Use the period certificate at exponent a, not at sigma.
    from quarter_signed_block import periodic
    Sunit+=periodic(q,ctx.prec)[1]
    # Difference from length on any interval in j costs one incomplete period
    # plus the discrepancy of complete-period length.
    inner=q*(ram+1)*Sunit
    lam=(alpha*(-w).exp())**2
    outer=delta/lam**a*yr**(1-a)
    scale=2*eta/a*(alpha*(q/(2*pi)).sqrt())**(-a)*(a*w).sinh()/(a*w)
    lower=scale*(D**(1-a/2)-K**(1-a/2))/(1-a/2)
    upper=scale*D**(1-a/2)*(1/(1-a/2)+1/(m+a/2-1))
    return lower,upper,time0,4*pi/q*inner,4*pi/q*outer,yf


def single(q,U,alpha,w,d,e,positive=False):
    assert d>e>=1 and gcd(d*e,q)==1 and d<(U-3).exp()
    sg=arb(3)/4;a=2*sg-1
    gg=gcd(d,e);s=e//gg;R=arb(d)/e
    lo,hi,time0,inner,outer,yf=geometry(q,str(U),str(alpha),str(w),ctx.prec)
    mass=(arb(d)*e)**(-sg)
    main=(hi if positive else lo)*(arb(e)**(-a)-arb(d)**(-a))/(d*s)
    period=q*s
    mean=1+arb(fmpz(q).euler_phi())*(1+arb(period).log())
    uniform=1+arb(period)*(1+arb(period).log())
    # The prefix splits at P*mean/uniform. Combine the pointwise and
    # full-period count controls before partial summation.
    averaged=mean*yf**(1-a)/(1-a)+uniform**a*(period*mean)**(1-a)/(1-a)
    small=(inner*s).min(4*arb.pi()/q*averaged)
    return main,time0*mass,R**(1-sg)*(small+outer*R**a)*mass


if __name__=='__main__':
    ctx.prec=160
    U=arb(37);alpha=arb(64);w=arb('.75');q=2310
    total=arb(0);cnt=0
    for d in range(2,1001):
        if gcd(d,q)>1 or int(fmpz(d).moebius_mu())!=-1:continue
        main,time,lattice=single(q,U,alpha,w,d,1)
        gain=main-time-lattice
        if d in (13,17,19,97,997):
            print('mollifier pair',d,1,'continuous, time error, arithmetic error, certified negative amount',
                  *(v.str(11) for v in (main,time,lattice,gain)),flush=True)
        if gain>0:total+=gain;cnt+=1
    print('genuinely negative selected pairs with e=1, total negative credit',cnt,total.str(13),flush=True)
    whole=arb(0)
    for d in range(2,10001):
        mu=int(fmpz(d).moebius_mu())
        if mu and gcd(d,q)==1:
            m,t,h=single(q,U,alpha,w,d,1,mu>0)
            whole+=mu*m+t+h
    print('complete row e=1 and all d<=10000, genuine upper',whole.str(13),flush=True)
    for B in (64,128,256,512,1024):
        units=[(k,int(fmpz(k).moebius_mu())) for k in range(1,B+1) if gcd(k,q)==1 and fmpz(k).moebius_mu()]
        cost=arb(0);main=arb(0);time=arith=arb(0);count=0
        for i,(d,mu) in enumerate(units):
            for e,me in units[:i]:
                sign=mu*me
                m,t,h=single(q,U,alpha,w,d,e,sign>0)
                main+=sign*m;time+=t;arith+=h;count+=1
        print('complete d>e triangle',B,count,'signed continuous upper, time, arithmetic, genuine upper',
              *(v.str(11) for v in (main,time,arith,main+time+arith)),flush=True)
