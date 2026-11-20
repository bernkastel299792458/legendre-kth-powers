"""Certified piecewise centered BV norms, followed by the fixed P5 comparison."""

from pathlib import Path
import argparse
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import verify_bv as coarse
from verify_bv import A, check, detector_constants, height_moment


def finite_data(W, y0, signed_low=False):
    # G(t)=sum_{n<=exp(t)}mu(n)(t-log n)/n. A term is continuous
    # at each integer boundary, including t=0, where it vanishes.
    S = arb(32).log()
    N = 2048
    P, Q = 192, 384
    head = [S*i/P for i in range(P+1)]
    mid = [W*i/Q for i in range(Q+1)]
    quad = [(W+S)*i/768 for i in range(769)] if signed_low else []
    endpoints = head + [W+t for t in head] + mid
    points = endpoints+quad
    order = sorted(range(len(points)), key=lambda i: float(points[i]))
    mu = coarse.mobius_up_to(int(float((W+S).exp()))+10)
    check((W+S).exp()<len(mu)-1 and (W+S).exp()<10**14, "Möbius table coverage")
    slope, offset, n = arb(0), arb(0), 0
    G = [None]*len(points)
    for i in order:
        t = points[i]
        check(n==0 or arb(n).log()<=t, "ordered finite table")
        while n+1 < len(mu) and arb(n+1).log() <= t:
            n += 1
            if mu[n]:
                term = arb(mu[n])/n
                slope += term
                offset += term*arb(n).log()
        # An undecidable comparison can occur only if this term contributes
        # less than the Arb enclosure. Also cover exact endpoints log(32).
        val = slope*t-offset
        if n+1 < len(mu):
            diff = t-arb(n+1).log()
            if not diff < 0:
                check(t<arb(n+2).log(), "single unresolved Möbius term")
                val = val.union(val+arb(mu[n+1])/(n+1)*diff)
        G[i] = val
    H = G[:P+1]
    HW = G[P+1:2*(P+1)]
    M = G[2*(P+1):len(endpoints)]
    mass = lambda a,b: b-a+b.exp()/y0
    # A(log n) and its tail energy at s>=log(32).
    signed, parts = arb(0), []
    for j in range(1,N):
        signed += arb(mu[j])/j
        parts.append(abs(signed)*(arb(1)/j).log1p())
    tails = [None]*N
    tail = (arb(8)/N).sqrt()
    far_energy = arb(8)/N
    for j in range(N-1,0,-1):
        tail += parts[j-1]
        tails[j] = tail
        if j>=32:
            far_energy += tail**2*((arb(1)/j).log1p()+(j+1)/y0)
    head_data = []
    for i,(a,b) in enumerate(zip(head,head[1:])):
        # Any lower integer works for A. The floor selection is checked.
        j = max(1,int(float(a.exp()))-1)
        while j<31 and arb(j+1).log()<=a:
            j += 1
        check(arb(j).log()<=a, "head envelope floor")
        variation = (2*(-a).exp()).sqrt()*(1+(-W/2).exp())*(b-a)/2
        Fabs = abs(HW[i]-H[i]).max(abs(HW[i+1]-H[i+1]))+variation
        head_data.append((mass(a,b),Fabs/W,tails[j]))
    c = A("1.00303")
    mid_data = []
    for i,(a,b) in enumerate(zip(mid,mid[1:])):
        variation = (2*(-a).exp()).sqrt()*(b-a)/2
        gl = arb(0).max(M[i].min(M[i+1])-variation)
        gu = c.min(M[i].max(M[i+1])+variation)
        mid_data.append((b,gl,gu,b-a+1/y0))
    signed = None
    if signed_low:
        values=G[len(endpoints):]
        quadrature=[]
        for i,(a,b) in enumerate(zip(quad,quad[1:])):
            variation=(2*(-a).exp()).sqrt()*(b-a)/2
            qlo=arb(0).max(c-values[i].max(values[i+1])-variation)
            qhi=c.min(c-values[i].min(values[i+1])+variation)
            quadrature.append((a,b,qlo,qhi))
        query=[]
        for t,g in zip(endpoints,G):
            i=max(0,min(767,int(float(t*768/(W+S)))-1))
            while i>0 and not quad[i]<=t:
                i-=1
            check(quad[i]<=t and t-quad[i]<(W+S)/250,"quadrature prefix")
            query.append((t,c-g,i,t-quad[i]))
        signed=(P,Q,head,mid,quadrature,query)
    return S, head_data, mid_data, far_energy, signed


def signed_low_norm(data,l,u,W,y0):
    """Use G_e(t)=c(1+et)-A_e(t) with an integrated nonnegative deficit."""
    P,Q,head,mid,quadrature,query=data
    c=A("1.00303")
    il=ih=jl=jh=arb(0)
    prefix=[]
    for a,b,qlo,qhi in quadrature:
        prefix.append((il,ih,jl,jh))
        step=b-a
        bot=(-u*b).exp()*qlo
        top=(-l*a).exp()*qhi
        jl+=step*il+step**2*bot/2
        jh+=step*ih+step**2*top/2
        il+=step*bot
        ih+=step*top
    caps=[]
    for t,q,i,step in query:
        il,ih,jl,jh=prefix[i]
        q=arb(0).max(q).min(c)
        jl+=step*il
        jh+=step*ih+c*step**2/2
        ih+=step*c
        caps.append(((-u*t).exp()*q+2*l*il+l**2*jl,
                     (-l*t).exp()*q+2*u*ih+u**2*jh))
    head_sum,mid_sum=arb(0),arb(0)
    bounds=[]
    for (lo,hi),(wl,wh) in zip(caps[:P+1],caps[P+1:2*(P+1)]):
        bounds.append((-(c-1/(1+u))*u+(wl-hi)/W,(wh-lo)/W))
    for i,(a,b) in enumerate(zip(head,head[1:])):
        variation=(2*(-a).exp()).sqrt()*(1+(-W/2).exp()+2*u)*(b-a)/(2*W)
        absolute=abs(bounds[i][0]).max(abs(bounds[i][1])).max(abs(bounds[i+1][0])).max(abs(bounds[i+1][1]))+variation
        head_sum+=(b-a+b.exp()/y0)*(u*b).exp()*absolute**2
    bounds=[]
    for t,(lo,hi) in zip(mid,caps[2*(P+1):]):
        glo=c*(1+l*t)-hi
        ghi=c*(1+u*t)-lo
        bounds.append((l/(1+l)-ghi/W,u-glo/W))
    for i,(a,b) in enumerate(zip(mid,mid[1:])):
        variation=(arb(2).sqrt()*((-a/2).exp()+2*u))*(b-a)/(2*W)
        absolute=abs(bounds[i][0]).max(abs(bounds[i][1])).max(abs(bounds[i+1][0])).max(abs(bounds[i+1][1]))+variation
        mid_sum+=(b-a+1/y0)*(-l*(W-b)).exp()*absolute**2
    return head_sum,mid_sum


def high_norm(h,W,y0,de,ep):
    # Center the logarithmic tail with the complete sums 1/zeta, zeta'/zeta^2.
    dmax, fmax, E = A(".65"), A(".43"), A("1.2")
    vm = arb(2)+ep
    check(sum(arb(n)**-vm for n in range(1,65)) > 1/dmax, "zeta reciprocal")
    check((1/dmax)**-2 <= fmax, "derivative estimate")
    check(1+1/(2*arb(1).exp()) < E, "unimodal remainder")
    cap = W/2
    C = E*(-cap).exp()
    head = (E*(1+(-W).exp()))**2*(1+1/y0)
    # For 0 <= t <= W/2, max(F,D*t)+C <= sqrt(F^2+D^2*t^2)+C.
    # Use the L2 triangle inequality with the exponentially weighted sum.
    near = ((fmax**2*(1+1/y0)+dmax**2*(2+4/y0)).sqrt()+C*(1+1/y0).sqrt())**2
    far = (-cap).exp()*((1+cap)**2+2*(1+cap)+2+(1+cap)**2/y0)
    return arb(2).zeta()*de*(head+near+far)/(h*W**2)


def signed_high_norm(h,W,y0,ep):
    # Uniform after factoring out Y^{-e}. Abel on the logarithmic tail
    # allows the verified cancellation in m to improve its coefficient.
    pi, C, dmax = arb.pi(), A(".011"), 1+ep
    tstar=arb(10**14).log()
    v=2+ep
    upper_A=(A(".5")+2*dmax*(-1-A(".5")/dmax).exp())/A("2.25")
    E0=arb(2).sqrt()*upper_A
    E1=2*C/(arb(1).exp()*(1+tstar))
    E=E0+E1
    d_lo=1/arb(2).zeta()
    d_hi=1/sum(arb(n)**-v for n in range(1,257))
    # The logarithmic derivative is sum Lambda(n)/n^v. Bound it by
    # (-zeta'(2))/zeta(v) above, and by the finite v-moment below.
    z0=sum(arb(n).log()/arb(n)**v for n in range(2,257))
    z2=sum(arb(n).log()/arb(n)**2 for n in range(2,257))+(1+arb(256).log())/256
    c=A(".55")
    shift=abs(z0*d_lo-c).max(abs(z2*d_hi-c))
    # j<=Y: e^{-dt} multiplies E0 exp(-t/2)+E1.
    head=(E0*(1+(-W).exp())*(A(".5")+1/y0).sqrt()
          +E1*(1+(-W).exp())*(1+1/y0).sqrt())**2
    # j>Y: sum of the centered linear function, then of the residual,
    # extended to (0,infty) in r for the linear contribution only.
    quadratic=2-2*c+c**2+5/y0
    main=d_hi*(quadratic.sqrt()+shift*(1+1/y0).sqrt())
    remainder=E*((-W).exp()*(1+1/y0)).sqrt()
    tail=(d_hi*W)**2*(-W).exp()*(1+1/y0)
    return arb(2).zeta()*(head+(main+remainder)**2+tail)/(h*W**2)


def critical_endpoints(U,delta,kap,W,logh):
    T, Z = U.exp(), (U-6).exp()
    pi=arb.pi()
    m0=(1+A("2/3")*A("6/5").sqrt()).sqrt()
    mu={1:1}
    for p in (2,3,5,7,11):
        mu.update({p*j:-c for j,c in mu.copy().items()})
    b=sum(arb(m)/j**2 for j,m in mu.items())
    c=sum((max(0,m)-2*m*arb(j).log())/j**2 for j,m in mu.items())
    off=b*(W/3+logh)+c
    check(off>0 and (U+logh).exp()>2310**2, "critical squarefree range")
    c1=b+off/U
    c2=pi*m0*((2*b*(W+logh).exp()*(1-(1+W)*(-W).exp())/W**2+16/T)/U+c1/(2*T))
    V=U-6
    check(Z>10**20 and V>50, "CS Table 2, last row")
    z=V-arb(2).log()
    a1=Z*z**4/(2*pi**2)+A("29.364")*Z*z**3+A("9.6675e26")
    # The leading ratio is bounded by 1. For the next ratio, the
    # decreasing function (1-log(2)/v)^3/v attains its maximum at V.
    a2=1/(2*pi**2)+A("29.364")*(1-arb(2).log()/V)**3/V+A("9.6675e26")/(Z*V**4)
    a=3/(4*kap)
    v=2/(3*U)
    c0=v*a/(1+a)
    check(0<c0 and c0<1, "gamma range")
    tangent=(v*((1+a).log()-a/(1+a))).exp()
    mass=A("7/6").gamma()/(1-c0)**A("7/6")
    mean_root=A("5/3").gamma()/((1-c0).sqrt()*A("7/6").gamma())
    integral=tangent*mass*(c1*a.sqrt()*mean_root+c2)**A("2/3")
    eta=A(".001")
    k1=((1+eta)*a2*a.sqrt())**A("1/3")*integral
    k1+=((1+eta)*a1/T)**A("1/3")*(c2+Z*c1/T)**A("2/3")/U**A("4/3")
    k2=(1+1/eta)**A("1/3")*(a.sqrt()*pi.sqrt()/2+(Z/T)**3/a)
    H=arb(3*10**12)
    l0=(kap*(1+((1+2*delta/U)/(4*T))**2)).exp()/(1-1/H)
    check(l0>1 and 9/(U+logh).exp().sqrt()<A(".01"), "Littlewood right edge")
    return k1,k2,l0


def right_endpoint(U,delta,kap,W,logh,signed_high=False,signed_low=False):
    """Return K3, far-head energy, S1/U and T*S2 for all log(T)>=U."""
    ep=2*delta/U
    check(U>0 and kap>0 and 0<ep and ep<=A(".1") and W>0 and logh<0, "v interval")
    h, y0=logh.exp(), (U+logh).exp()
    check(y0>2048, "head range")
    S,heads,mids,far_energy,signed_data=finite_data(W,y0,signed_low)
    c,C=A("1.00303"),A(".011")
    shape=1/(1+S)+(1+y0.log())**-2+32/y0
    small_C=C/(1+arb(10**14).log())
    pi=arb.pi()
    m0=(1+A("2/3")*A("6/5").sqrt()).sqrt()
    k3=arb(0)
    lowmax,highmax=arb(0),arb(0)
    highbase=signed_high_norm(h,W,y0,ep) if signed_high else high_norm(h,W,y0,arb(1),ep)
    for i in range(64):
        l, u = ep*i/64, ep*(i+1)/64
        de=(-2*delta-logh*u).exp()
        head=sum(mass*(f+2*u*tail+small_C)**2 for mass,f,tail in heads)
        mid=arb(0)
        for b,gl,gu,mass in mids:
            et=(-u*b).exp()
            g_lo=et*gl
            g_hi=c*(1+u*b)-et*(c-gu)
            bb=(u-g_lo/W).max(g_hi/W-l/(1+l)).max(arb(0))
            mid+=mass*(-l*(W-b)).exp()*bb**2
        if signed_low:
            sh,sm=signed_low_norm(signed_data,l,u,W,y0)
            head=head.min(sh)
            mid=mid.min(sm)
        head+=((1+u*W)*far_energy.sqrt()/W+2*C*shape.sqrt())**2
        low=de*((1+u)/(2*delta)*(head+mid)+(-l*W).exp()*(1+u/y0)*u/(2*delta))
        high=highbase*de
        k=pi*m0*low+(pi.sqrt()/(2*(2*kap).sqrt())+pi*m0/(2*U.exp()))*high*u/(2*delta)
        k3=k3.max(k)
        lowmax=lowmax.max(low)
        highmax=highmax.max(high)
    return k3,far_energy,lowmax,highmax


def fine_endpoints(U,delta,kap,W,logh):
    k1,k2,l0=critical_endpoints(U,delta,kap,W,logh)
    k3,energy,low,high=right_endpoint(U,delta,kap,W,logh)
    return k1,k2,k3,l0,energy,low,high


def verify(anchor,W,logh,delta,kap,U):
    L=arb(anchor)
    k1,k2,k3,l0,energy,low,high = fine_endpoints(U,delta,kap,W,logh)
    bands=detector_constants()
    knots=[arb(i)/1000 for i in range(650,871)]+[A("7/8")]
    u1=(A("16/7")*(1+(L/4).exp()/4)).log()
    check(u1>U, "moment validity at starting height")
    ratio=(k1+k2/U**2)/k3
    base=2*((knots[0]-1)*L).exp()*height_moment(u1, arb(1), arb(1))
    check(knots[0]-1+A("1/4")+1/(4*u1)<0,"base decrease")
    jlog=A("15/14").log()
    outer=(11*((logh+W)/2).exp()).log()
    edge=162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+6*outer)/jlog)
    edge+=18/jlog*height_moment(u1,arb(0),arb(1))
    previous,zm,ze=arb(0),arb(0),arb(0)
    for s,t in zip(knots,knots[1:]):
        p=3*(1-s)/(2-s)
        ln=(2+4*delta/U)/(2-s+3*delta/U)
        hn=2/(2-s)
        check(bands[0][0]<=ln and hn<=bands[-1][1], "detector range")
        cd=max(cap for lo,hi,cap in bands if not(hi<ln or lo>hn))
        k=3*delta*(2*s-1)/(2-s)**2
        B=cd*l0**hn*k3*ratio**p*(ratio**(k/U)).max(arb(1))*(k*(1+U.log()/U)).exp()/(2*arb.pi())
        slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        jump=slope-previous
        check(jump>0,"positive slope jump")
        previous=slope
        zm+=2*jump*B*height_moment(u1,p,1+p)
        ze+=2*jump*edge
        check(t-1+2/L+p/4+(1+p)/(4*u1)<0 and t-1+2/L+1/(4*u1)<0,"decrease")
    eps=4*(-L/4).exp()
    pp=A("8/7")*(1+eps).sqrt()*(L+eps.log1p())**2*(-L/4).exp()/(8*arb(2).log())
    check(2/L<A("1/4"),"prime powers decrease")
    total=base+zm+ze+pp+(-3*L).exp()/(1-(-2*L).exp())
    return dict(K1=k1,K2=k2,K3=k3,far_energy=energy,S1_over_U=low,T_S2=high,total=total)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",type=int,default=254)
    for name,value in (("width","10"),("logh","-3.2"),("delta",".75"),("kappa",".105"),("U","62.8")):
        cli.add_argument("--"+name,default=value)
    args=cli.parse_args()
    ctx.prec=160
    out=verify(args.anchor,A(args.width),A(args.logh),A(args.delta),A(args.kappa),A(args.U))
    for label,value in out.items():
        print(label,value.str(18))
    check(out["total"]<1,"point budget")
