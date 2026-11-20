"""Time-smoothed periodic AFE; Hilbert boundary and twice-integrated shift remainder."""
from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd,prod
from flint import arb,arb_poly,ctx
from periodic_fourth import branch,period,f,reciprocal_gap
from fast_period import fast_near


@lru_cache(maxsize=None)
def cutoff_coefficients(q,dual,K,precision):
    # In the endpoint norm these data are unweighted, positive prefix peaks.
    vals=period(q,dual)
    divs=[h for h in range(1,q+1) if q%h==0]
    rho={h:Fraction(sum(gcd(k,q)==h for k in range(q)),q) for h in divs}
    D={}
    for h in divs:
        hits=0
        D[h]=Fraction(0)
        for k in range(1,q+1):
            hits+=gcd(k,q)==h
            D[h]=max(D[h],Fraction(hits)-k*rho[h])
    co=[Fraction(0)]*3
    for h,k in product(divs,repeat=2):
        if gcd(h,k)>1 or (not dual and (h!=1 or k!=1)):continue
        v=[vals[(g*h)%q]*vals[(g*k)%q] for g in range(q)]
        S=peak=0
        for n in range(1,K+1):
            S+=v[n%q]
            new=max(peak,S*S)
            diff=new-peak
            if diff:
                co[0]+=diff*rho[h]*rho[k]/n**2
                co[1]+=diff*(rho[h]*D[k]+rho[k]*D[h])/n
                co[2]+=diff*D[h]*D[k]
            peak=new
        if (h,k)!=(1,1):
            assert sum(v)==0 and K>=q
    raw=[vals[g]**2 for g in range(q)]
    mu=Fraction(sum(raw),q)
    S=0
    discrepancy=Fraction(0)
    for k in range(1,q+1):
        S+=raw[k%q]
        discrepancy=max(discrepancy,Fraction(S)-mu*k)
    count=0
    harm2=Fraction(0)
    for k in range(1,K+1):
        if gcd(k,q)==1:
            harm2+=Fraction(2*count+1,k*k)
            count+=1
    return tuple(map(f,co)),f(rho[1]),f(D[1]),f(mu),f(discrepancy),f(harm2),count


def endpoint_norm(ell,Y0,q,dual,K):
    # Y^-2 times sum a_n(T)^2, whose support length is Y^2.
    co,r,d,mu,D,h2,count=cutoff_coefficients(q,dual,K,ctx.prec)
    X0=Y0/(K+1)
    assert X0>K and X0>3
    # Integrate N(t)^2/t^3 after its exact prefix. Preserve the negative lower boundary.
    h2+=(r+d/X0)**2-(arb(count)/K)**2+4*r*d/K+(d/K)**2
    h2+=2*r**2*(ell-arb(K*(K+1)).log())
    s=(2*r**2/(K+1)+(2*r*d*(1+X0.log())+2*d*d)/Y0)
    num=(r/(K+1)+d/Y0)**2
    return co[0]+co[1]/Y0+co[2]/Y0**2+mu**2*h2+2*mu*D*s+D**2*num


@lru_cache(maxsize=256)
def shift_weights(q,Jint,precision):
    # J is rounded upward.  Sum the long harmonic tail by decreasing integration.
    J=arb(Jint)/1024
    nmax=max(128*q,Jint//1024+1)
    residues=[]
    for j in range(1,q+1):
        n=j
        w=arb(0)
        while n<nmax:
            w+=(arb(1).min(J/n))/n
            n+=q
        residues.append(w+J*(arb(1)/n**2+arb(1)/(q*n)))
    return residues


@lru_cache(maxsize=256)
def shift_constants(q,dual,Jint,precision,mixed=False):
    residues=shift_weights(q,Jint,precision)
    other=list(map(abs,period(q,not dual))) if mixed else None
    _,ds,rs=fast_near(list(map(abs,period(q,dual))),residues,other)
    return ds,rs


@lru_cache(maxsize=256)
def projected_shift(q,dual,Jint,precision,mixed=False):
    from fast_period import projective_near
    v=list(map(abs,period(q,dual)))
    w=list(map(abs,period(q,not dual))) if mixed else v
    return projective_near(v,w,shift_weights(q,Jint,precision),w,v)


def smooth_fourth(U,q=6,alpha=arb(1),width=arb("0.15"),Z=96,*,paired=False,disjoint=False,
                  mixed_bound=None,projective=False,centering=None):
    assert width>0
    pad=width.exp()
    a,b=arb(q).sqrt()*alpha,arb(q).sqrt()/alpha
    start=max(1000,int((2*arb.pi()*(a.max(b)*pad)**2).upper().ceil().unique_fmpz())+1)
    assert (a.max(b)*pad)*(2*arb.pi()/start).sqrt()<1
    def off(U,q,dual,scale,ell,Y0,first,second,m,disc):
        # scale includes the longest cutoff exp(width).
        J=scale**2/((4 if paired else 1)*arb.pi()*width)
        Ji=int((J*1024).upper().ceil().unique_fmpz())
        if projective:
            ds,rs=projected_shift(q,dual,Ji,ctx.prec)
            shifts=(1+arb(q)/Y0)**2*ds+(2+(4*q*(1+Y0.log())+4*q*q)/Y0)*rs
        else:
            ds,rs=shift_constants(q,dual,Ji,ctx.prec)
            shifts=first*ds+second*rs
        lower=2*shifts+16*reciprocal_gap(ctx.prec)*(m+disc/(2*Y0.sqrt()))**4
        g=1 if dual else 2
        hilb=arb.pi()*arb("1.31541")/g
        top=hilb*endpoint_norm(ell,Y0,q,dual,max(2*q,192))
        tiny=hilb*max(map(abs,period(q,dual)))**4*(1+Y0.log())**4*(-U).exp()
        return scale**2/(2*arb.pi())*(lower+top)+tiny
    c=branch(U,q,False,a*pad,Z,start,off)
    d=branch(U,q,True,b*pad,Z,start,off)
    primes=[p for p in [2,3,5,7,11] if q%p==0]
    ef=prod(1+1/arb(p).sqrt() for p in primes)
    K=16*(2*arb.pi())**(arb(1)/4)*pad.sqrt()*sum(
        (arb(j)/a).sqrt().max((a/j).sqrt())/arb(j).sqrt() for j in range(1,q+1) if q%j==0)
    small=arb(17) if start==1000 else 4*(arb(start)/(2*arb.pi()))**(arb(1)/4)+1
    err=((ef**4*(200*arb(403)**4+(start-200)*small**4)+K**4*U)*(-U).exp())**(arb(1)/4)/U
    ordinary=c**(arb(1)/4)+d**(arb(1)/4)
    if paired:
        from shifted_harmonic import harmonic
        h=harmonic(U,q,alpha,width,start)/U**4
        phased=(c.sqrt()+d.sqrt()+(2*((c*d).sqrt()+h)).sqrt()).sqrt()
        if mixed_bound is not None:
            cross=mixed_bound(U,q,alpha,width,Z,start).min((c*d).sqrt())
            phased=phased.min(((c+d+2*cross).sqrt()+(2*(cross+h)).sqrt()).sqrt())
            if centering is not None:
                # S=|A|²+|B|², V=2Re(exp(i phi)AB). Center S before Cauchy.
                m,v,upper=centering(U,q,alpha,width,start)
                assert m>=0 and upper>=U
                s2=c+d+2*cross
                v2=2*(cross+h)
                var=(s2-m*m/upper**4).max(arb(0))
                fourth=s2+v2+2*(var*v2).sqrt()+2*m*v/U**4
                phased=phased.min(fourth**(arb(1)/4))
        ordinary=ordinary.min(phased)
    if disjoint:
        early=ef**4*(200*arb(14)**4+(start-200)*small**4)*(-U).exp()/U**4
        afe=K*(U*(-U).exp())**(arb(1)/4)/U
        return early+(ordinary+afe)**4
    return (ordinary+err)**4


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--q",type=int,default=30)
    cli.add_argument("--alpha",default="1.5")
    cli.add_argument("--width",default=".08")
    cli.add_argument("--u",default="40")
    cli.add_argument("--z",type=int,default=96)
    a=cli.parse_args()
    ctx.prec=160
    print("smooth fourth",smooth_fourth(arb(a.u),a.q,arb(a.alpha),arb(a.width),a.z).str(17))
