"""Complete paired estimate after reflecting an arbitrary subset of Euler factors."""
from functools import lru_cache
from inspect import getsource
from math import prod
from flint import arb,ctx

from balanced_branch import data,seq,upper
from dual_projection import improved
from grouped_rational import geometry
from interference import covariance,reduction,means,period
from shifted_harmonic import harmonic


def rebind(fn,substitutions,**variables):
    text=getsource(fn)
    for a,b in substitutions:
        assert text.count(a)==1
        text=text.replace(a,b)
    env=dict(fn.__globals__,**variables)
    exec(compile(text,__file__,"exec"),env)
    return env[fn.__name__]


@lru_cache(None)
def library(q,F):
    B=q//F
    assert F*B==q
    shapes=((F,B),(B,F))
    get=lambda q,side:seq(q,*shapes[int(side)])
    const=lambda q,side,prec:data(q,*shapes[int(side)],prec)
    den=lambda side:shapes[int(side)][1]
    red=rebind(reduction,[("arb(q).sqrt() if dual else 1","arb(den(dual)).sqrt()")],
               period=get,den=den)
    cov=rebind(covariance,[],reduction=red)
    mean=rebind(means,[("q if dual else 1","den(dual)"),
                       ("M=max(map(abs,period(q,True)))",
                        "M=max(map(abs,period(q,True)))*max(map(abs,period(q,False)))")],
                period=get,den=den)
    har=rebind(harmonic,[],period=get)
    original="""rho,_,_,_,_,du=constants(q,False,ctx.prec)
    _,_,_,_,scaled,disc=constants(q,True,ctx.prec)
    mu=scaled*arb(q).sqrt();disc*=arb(q).sqrt()"""
    new="""rho,_,sqdisc,_,ma,da=constants(q,False,ctx.prec)
    _,_,_,_,mb,db=constants(q,True,ctx.prec)
    mua,du=ma*arb(B).sqrt(),da*arb(B).sqrt()
    mu,disc=mb*arb(F).sqrt(),db*arb(F).sqrt()"""
    phi=lambda n:sum(period(n,False))
    fourier=arb(phi(F)*sum(abs(n) for n in period(B,True)))/B
    G=rebind(geometry,[(original,new),
           ("2*rho*(lamhi*ratio).sqrt()","2*mua*(lamhi*ratio).sqrt()"),
           ("2*rho*ratio*delta.sinh()","2*mua*ratio*delta.sinh()"),
           ("2*rho*C*sh*dlog","2*mua*C*sh*dlog"),
           ("2*rho*C*delta.sinh()*dlog","2*mua*C*delta.sinh()*dlog"),
           ("edge=du*Y+((X/P)+1)*(rho*q)*(P*(2+P.log()))",
            "edge=sqdisc*Y+max_forward*((X/P)+1)*fourier*(P*(2+P.log()))")],
           constants=const,B=B,F=F,max_forward=max(map(abs,get(q,False))),fourier=fourier)
    calc=rebind(improved,[],geometry=G,covariance=cov,reduction=red)
    return mean,har,calc


def finite(U,q,F,alpha,width,Z,slab=None,limit=65536):
    B=q//F
    a=arb(q).sqrt()*alpha
    b=arb(q).sqrt()/alpha
    pi=arb.pi()
    scale=a.max(b)*width.exp()
    start=max(1000,int((2*pi*scale**2).upper().ceil().unique_fmpz())+1)
    c=upper(q,F,B,U,alpha,width,Z,start)
    d=upper(q,B,F,U,1/alpha,width,Z,start)
    means,har,calc=library(q,F)
    h=har(U,q,alpha,width,start)/U**4
    cross=(c*d).sqrt()
    s2=c+d+2*cross
    v2=2*(cross+h)
    up=(s2.sqrt()+v2.sqrt())**2
    if slab is not None:
        m,v,edge=means(U,q,alpha,width,start,slab=slab)
        slopes=("1","1.08","1.16","1.25","1.35","1.45","1.6","1.85","2.2")
        up=up.min(calc(U,q,alpha,width,start,s2,v2,m,v,edge,-1,limit,slopes))
    primes=[p for p in (2,3,5,7,11) if q%p==0]
    assert prod(primes)==q
    ef=prod(1+1/arb(p).sqrt() for p in primes)
    K=arb(0)
    for D in range(1,F+1):
        if F%D==0:
            for E in range(1,B+1):
                if B%E==0:
                    ratio=arb(B*D)/(E*a)
                    K+=ratio.max(1/ratio).sqrt()/arb(D*E).sqrt()
    K*=16*(2*pi)**(arb(1)/4)*(width/2).exp()
    small=arb(17) if start==1000 else 4*(arb(start)/(2*pi))**(arb(1)/4)+1
    early=ef**4*(200*arb(14)**4+(start-200)*small**4)/(U.exp()*U**4)
    return early+(up**(arb(1)/4)+K*(U/U.exp())**(arb(1)/4)/U)**4


def fourth(U,q=210,F=42,alpha=arb("1.06"),width=arb(".34"),Z=384,limit=65536):
    edge=U
    row=arb(0)
    for dx in map(arb,(".125",".25",".625","1","1","1","1","1","1","1","1","1")):
        row=row.max(finite(edge,q,F,alpha,width,Z,dx,limit))
        edge+=dx
        if edge>=U+1:
            tail=finite(edge,q,F,alpha,width,Z)
            if row>tail:
                return row
    return row.max(tail)


if __name__=="__main__":
    ctx.prec=160
    for u,cap in ((35,".000810500"),(37,".000729891"),(40,".000652476")):
        row=fourth(arb(u))
        assert row<arb(cap)
        print("reflected Euler product",u,row.str(15),flush=True)
