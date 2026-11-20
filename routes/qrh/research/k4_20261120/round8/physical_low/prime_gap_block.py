"""Whole signed finite Fourier band on semiprimes having no physical unit multiple."""
from math import gcd
from functools import lru_cache
from flint import arb,ctx,fmpz
from actual_split import constants,H
from whole_spike import gp
from ramanujan_prefix import signed_maxima

@lru_cache(None)
def small_harmonic(lo,hi,prec):
    assert ctx.prec==prec and 23<=lo<hi
    j=lo;value=arb(0)
    if lo<100000:
        j=min(hi,100000)
        value+=sum((1/arb(k) for k in range(lo+1,j+1) if fmpz(k).is_prime()),arb(0))
    while j<hi:
        j1=min(2*j,hi);xj=arb(j1)
        err=xj.sqrt()*xj.log()*(xj.log()-2)/(8*arb.pi())
        value+=((xj/j).log()-2*err/j).max(arb(0))/xj.log();j=j1
    return value

def prime_rows(z,r,Q,grid,top,small_lo,small_hi,largest,refined,eta,discrepancy):
    end=arb(top);edges=[(end.log()*i/grid).exp() for i in range(grid+1)]
    edgeints=[min(1000000,int(z0.lower().floor().unique_fmpz())) for z0 in edges]
    acc=arb(0);small=0;gg=[]
    reciprocal_square=arb(1)/2000+sum((1/arb(p)**2 for p in range(2,2001) if Q%p and fmpz(p).is_prime()),arb(0))
    for val,n in zip(edges,edgeints):
        for j in range(small+1,n+1):
            if gcd(j,Q)==1 and fmpz(j).moebius_mu():
                acc+=1/arb(int(fmpz(j).euler_phi()))
        small=n;saving=arb(0)
        if refined and n==1000000:
            saving=((eta-reciprocal_square)*(val/n).log()-discrepancy/n-2/arb(n).sqrt()).max(arb(0))
        gg.append(acc+saving)
    # Each prime interval is (a,b]. For the closed excluded subintervals allow
    # one endpoint even if it is prime, at the per-interval harmonic price 1/a.
    rows=[]
    for i in range(grid):
        a=z/edges[i+1];b=z/edges[i];assert 599<a/small_hi<b<arb("2.169e25") and a/small_hi>max(1000000,largest)
        if refined and largest==1:assert a/small_hi>edges[i]
        # For all t in [small_lo,small_hi], t E(b/t) is increasing here.
        arg=b/small_hi;assert arg.log()>6
        thetaerr=small_hi*arg.sqrt()*arg.log()*(arg.log()-2)/(8*arb.pi())
        harmonic=((b/a).log()-2*thetaerr/a)/(b/small_lo).log()
        excluded=(4*r+2*thetaerr/a)/(a/small_hi).log()+small_hi/a
        assert harmonic>0
        rows.append((a,b,harmonic,excluded,gg[i],small_hi))
    return rows

def bound(Q=223092870,m=200,logY="75",low=2,upper="2.5e17",grid=80,top=2000000,spatial=False,refined=False,small_range=None,specific=None):
    z,c,r,I,A,S,u=constants(1732099)
    X=(c+2*r).exp();xl=(c-2*r).exp();Y=arb(logY).exp();kap=arb(upper)
    tau=2**len(fmpz(Q).factor());eta=arb(int(fmpz(Q).euler_phi()))/Q
    discrepancy=arb(tau)
    if refined:
        from wheel_small import osc
        for base in (210,2310,30030,510510):
            if Q%base==0:
                discrepancy=discrepancy.min(arb(2**len(fmpz(Q//base).factor())*osc(base))/base)
    assert Q%210==0 and m>=2 and low>0 and xl/X<1 and z*z<X
    small_lo,small_hi=(small_range if small_range else (1,1))
    outer_factor=arb(1)
    if small_range:
        assert Q==223092870 and 23<=small_lo<small_hi and (isinstance(top,tuple) or top<small_lo)
        if specific:
            (al,ah),(bl,bh)=specific
            assert al==small_lo and bh==small_hi and ah<=bl
            outer_factor=2*small_harmonic(al,ah,ctx.prec)*small_harmonic(bl,bh,ctx.prec)
        else:
            outer_factor=small_harmonic(small_lo,small_hi,ctx.prec)**2-1/arb(small_lo)
        assert outer_factor>0
    if isinstance(top,tuple):
        ta,tb=top
        assert specific and ta<bl and tb<al
        left_rows=prime_rows(z,r,Q,grid,ta,al,ah,bh,refined,eta,discrepancy)
        right_rows=prime_rows(z,r,Q,grid,tb,bl,bh,bh,refined,eta,discrepancy)
        symmetric=False
    else:
        left_rows=prime_rows(z,r,Q,grid,top,small_lo,small_hi,small_hi,refined,eta,discrepancy)
        right_rows=left_rows;symmetric=True
    K=arb(H);R=K*r;a=(1-arb("1e-12"))*K*(c-116)
    mass0=u*(-2*r).exp()*(A-4/(R*(1-(a/R)**2)))
    G=gp(z,Q)
    t=2*arb.pi()*arb(".0002")*(116-c-2*r).exp()*kap/(64*K)
    assert 0<t<arb.pi() and 1-arb.pi()/4<arb(1)/4
    sf=(t.sin()/t).max(arb(1)/4)
    M=S*K*(2*r).exp()/(arb.pi()*kap)
    highs=[2*u*M*tau*eta*sf**(64-n)*t**(-n) for n in range(2,65)]
    # Every gap modulus above this ratio contributes negatively even if it is
    # outside the rectangles used for the lower estimate of their total mass.
    floor=2500
    maxfreq=low*Q//floor
    peak=signed_maxima(Q,[maxfreq])[maxfreq][0]
    positive=mass0*(eta-2*arb((1+4*low)*peak)/Q)
    def tailcap(wmin):
        return min((v*(kap/(wmin*(j+1))+1) for j,v in enumerate(highs)),key=lambda x:float(x.upper()))
    def spatial_cap(v):
        D=5*(v/K)**(arb(1)/3)
        rel=v/(K*D)
        den=(1-arb(".0004")*rel)**2-(a*(2*r).exp()*rel)**2
        assert 1-arb(".0004")*rel>0 and den>0
        return 4*u*(4*r).exp()*(v/K)*(1/D**2+1/D)/den
    assert positive>tailcap(arb(floor))
    if spatial:
        # At smaller w the low spectrum estimate improves monotonically.
        assert mass0*(eta-2*arb((1+4*low)*signed_maxima(Q,[low*Q//10000])[low*Q//10000][0])/Q)>tailcap(arb(floor))+spatial_cap(arb(10)**10)
        assert positive>tailcap(arb(floor))+spatial_cap(arb(10000))
    cells=[]
    for i,p in enumerate(left_rows):
        for j in range(i if symmetric else 0,grid):
            v=right_rows[j];wmin=X/(p[1]*v[1])
            if not wmin>max(m,floor) or not (Y<p[0]*v[0]) or not (z<p[0]*v[0]):continue
            if small_range and not p[0]*v[0]>z*p[5]*v[5]:continue
            wcenter_hi=c.exp()/(p[0]*v[0]);wcenter_lo=c.exp()/(p[1]*v[1])
            if spatial and (not wcenter_hi<arb(10)**10 or not wcenter_lo>floor):continue
            # Unit count for each actual fixed outer prime, then both orientations.
            def kept(x,y):
                a,b,hy,exc,_,small_hi=y
                if spatial:
                    d=5*(wcenter_hi/K)**(arb(1)/3)
                    left=wcenter_lo-2*d;right=wcenter_hi+2*d
                    ylo=2*d*a*left/((wcenter_lo+2*d)*right*small_hi)
                    assert left>0
                    rel=2*d/left
                    ystart=a*left/(wcenter_lo+2*d)
                    # Full interval BT and theta bound after clipping.
                    arg=b/small_hi;ee=small_hi*arg.sqrt()*arg.log()*(arg.log()-2)/(8*arb.pi())
                    exc=(rel+2*ee/a)/(a/small_hi).log()+small_hi/a
                    if ylo>10:exc=exc.min(2*rel/ylo.log()+small_hi/ystart)
                    kcount=eta*(c.exp()/x[0]*(1/a-1/b)+2*d)+discrepancy
                else:
                    kcount=eta*X/x[0]*(1/a-xl/X/b)+discrepancy
                return x[2]*(hy-kcount*exc-x[5]/x[0]).max(arb(0))
            keep=(kept(p,v).max(kept(v,p)))*(1 if not symmetric or i==j else 2)
            if not keep>0:continue
            n=int((low*Q/wmin).upper().floor().unique_fmpz())
            cells.append((n,wmin,keep*p[4]*v[4],spatial_cap(wcenter_hi) if spatial else arb(0)))
    if not cells:return 0,arb(0)
    caps=signed_maxima(Q,[x[0] for x in cells])
    total=arb(0);good=0
    for n,wmin,weight,physical in cells:
        zeroth=caps[n][0]
        phase=eta-2*arb((1+4*low)*zeroth)/Q
        if not phase>0:continue
        # q/X <= 1/wmin, and each fixed-q Ramanujan moment has tail v(Q+y).
        neg=mass0*phase-tailcap(wmin)-physical
        if neg>0:
            good+=1;total+=weight*neg/G**2
    return good,total*outer_factor

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--Q",type=int,default=223092870);ap.add_argument("--cut",type=int,default=200)
    ap.add_argument("--logY",default="75");ap.add_argument("--low",type=int,default=2)
    ap.add_argument("--high",default="2.5e17");ap.add_argument("--grid",type=int,default=80)
    ap.add_argument("--top",type=int,default=2000000);ap.add_argument("--lower");ap.add_argument("--spatial-tail",action="store_true")
    ap.add_argument("--refined",action="store_true")
    ap.add_argument("--small-range",nargs=2,type=int)
    args=ap.parse_args();ctx.prec=144
    n,v=bound(args.Q,args.cut,args.logY,args.low,args.high,args.grid,args.top,args.spatial_tail,args.refined,args.small_range)
    print("certified unordered gap cells, negative signed margin",n,v.str(15))
    if args.lower:assert v>arb(args.lower)
