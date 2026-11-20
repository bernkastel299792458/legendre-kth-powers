"""Littlewood bounds at the selected node, retaining the actual origin of each window."""
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import argparse,sys
from flint import arb,ctx
from math import prod

RESEARCH=Path(__file__).resolve().parents[2]
for folder in ("round6/first_rect","round6/phase","round6/folds"):
    sys.path.insert(0,str(RESEARCH/folder))
from first_bounds import A,H,detector_floor,folded,mixed_low_rows,direct_high,exact_right
from circle_mean import hinge_angular
from fold_mean import source,moment
from short_block import data,short_second
from projected_short import coeffs,progression
from periodic_fourth import reciprocal_gap

V=A("1.01")
M=2048


@lru_cache(maxsize=100)
def rings(low,size,ws,hs,prec,scale=None,q=210):
    l=arb(low);d=arb(size);y=(d/2 if scale is None else arb(scale))*A(hs).exp();x=y*A(ws).exp()
    N=arb(low+size+7);a2=2*(y.log()+2)/y
    center=2-(1+a2)**15
    assert center>A(".5") and l>10 and y>1
    av=[]
    for radius in ("1.44","1.58","1.72","1.86","1.96"):
        R=A(radius);mean=arb(0)
        for i in range(1,97):
            s=2+R*(arb.pi()*i/96).cos()
            pow1=(1-s).max(arb(0))
            z=N**pow1*(1+N.log()+1/(l-2)+1/s)
            c=x**pow1*(1+x.log())
            e=prod(1+arb(p)**(-s) for p in (2,3,5,7,11) if q%p==0)
            f=1+z*e*c
            if s>1:
                b=s-1
                f=f.min(y**(-b)*s*((1+y.log())/b+1/b**2))
            mean+=f.log1p()
        av.append((R,mean/96))
    return av,-center.log()


def global_half(coef,degree,B,C,R):
    p=1+degree/B.log()
    assert V*R<C and p<M
    return coef*B*B.log()**degree*M/(M-p)*(1+(V*R/C)**(M-p))/2


@lru_cache(maxsize=128)
def fourth_mass(low,size,base,alpha,prec):
    R=arb(size)/2;C=arb(low)+R;B=C+V*R
    key=int((B.log()*1000000).lower().floor().unique_fmpz())
    c=moment(key,base,Fraction(alpha),prec,"centered")
    out=global_half(c,4,B,C,R)
    if low==H and base in (6,30) and size<=150000000000:
        from periodic_local import effective_mass
        a=Fraction(alpha)
        out=out.min(effective_mass(size,base,arb(a.numerator)/a.denominator,2,arb(1)))
    return out


@lru_cache(maxsize=128)
def short_stats(low,size,N,steps,prec,q=210):
    R=arb(size)/2;C=arb(low)+R;J=V*A("1.02")*R;B=C+V*R
    assert C-J>1000
    _,_,h1,_,roots,_,_,h2,_,_,_=data(q,N,prec,steps)
    first=160*(1+roots)*(C+V*M/(M-1)*R+4)**A(".25")
    cg=short_second(B.log(),q,N,steps)
    global2=global_half(cg,1,B,C,R)
    if N>65536 or q!=210:return h1,h2,global2,first
    A0,B0,K,smax,smin,hs2,m2,zroot=coeffs(q,N,steps)
    pi=arb.pi();root=arb(q).sqrt()
    ylo=((C-J)/(2*pi)).sqrt();yhi=((C+J)/(2*pi)).sqrt()
    tail=cg*B*B.log()*M/(M-1-1/B.log())*A("1.02")**(1+1/B.log()-M)
    out=global2
    for alpha in (arb(1),A("1.5"),arb(2)):
        a=alpha*root; b=root/alpha
        parts=[]
        for dual,scale in ((False,a),(True,b)):
            y,yl=scale*yhi,scale*ylo
            rho,av,c,er,disc,c0,c1,d0,d1=progression(q,dual,prec)
            assert yl>=q and N*y>16*q and av*y.log()+c>0
            diag=J*((av*y.log()+c)*A0+av*B0+er*smin/yl)
            l=(N*y).log()
            off=2*((d0*l+d1)*K**2+(c0*l+c1)*y*smax)
            off+=reciprocal_gap(prec)*(zroot*(2*rho*y.sqrt()+disc))**2
            assert min(diag,off)>0
            parts.append((diag+off).sqrt()/(root if dual else 1))
        ec=16*(2*pi)**A(".25")*sum((arb(d)/a).sqrt().max((a/d).sqrt())/arb(d).sqrt()
                                     for d in range(1,q+1) if q%d==0)
        rem=ec*(C-J)**(-A(".25"))*folded(J*hs2,m2,J,arb(1),arb(1),pi).sqrt()
        out=out.min((sum(parts)+rem)**2+tail)
    return h1,h2,out,first


@lru_cache(maxsize=512)
def left(low,size,ws,hs,base,alpha,core,prec,q=210,fourth_cap=None):
    R=arb(size)/2;u=R.log();w,h=map(A,(ws,hs))
    if u>20:
        cm,near=source(u,w,h,q,base,12)
    else:
        from narrow_cover import affine_mean
        assert q==210 and base==6
        cm=affine_mean(u,w,h)
        near=V*(1-A("1.03")**(1-M))
    c4=fourth_mass(low,size,base,alpha,prec)
    if fourth_cap is not None:
        assert base==210
        numerator,scale=fourth_cap
        assert numerator>0 and scale>0
        C=arb(low)+R
        c4=c4.min(global_half(arb(numerator)/scale,4,C+V*R,C,R))
    z=V*M/(M-1)*R
    best=(c4**A(".25")*(cm*R*u).sqrt()+z**A(".75"))**A("4/3")
    eu=prod(1+1/arb(p) for p in (2,3,5,7,11) if q%p==0 and base%p)
    choices=[(32768,3),(core,3)]
    if size<10**11:choices=[(512,2),(2048,3),(8192,3)]+choices
    for n,s in choices:
        H1,H2,E,err=short_stats(low,size,n,s,prec,q)
        assert n<R*h.exp() and q//base*n < base*V*A("1.03")*R/(12*arb.pi())
        for step in range(1,51):
            t=arb(step)/50
            res=cm*R*u-(2*t*H1-t*t*H2)*near*eu*R
            joint=t*t*E+(1-2*t)*z+2*t*err
            assert res>0 and joint>0
            best=best.min((c4**A(".25")*res.sqrt()+z**A(".25")*joint.sqrt())**A("4/3"))
    return best


@lru_cache(maxsize=256)
def right(size,ds,ws,hs,prec,q=210):
    R=arb(size)/2;u=R.log();d,w,h=map(A,(ds,ws,hs));e=2*d/u;Y=R*h.exp()
    rows=65536
    lo=mixed_low_rows(u,d,w,w,arb(0),h,q,cells=rows,first=rows-1,tight=True)[0]*u
    from right_fixed import sharp
    high=(direct_high(u,d,w,h,q)*(2+e).zeta()/arb(2).zeta()).min(sharp(u,d,w,h,q))
    rr=(-e*Y.log()).exp()*folded(high,lo,V*R,V*M/(M-1),A("1.274"),arb.pi()*48/210)
    from local_energy import local_right_rows
    extras={} if q==210 else dict(spacing=210,outer_spacing=q,frequency_cut="95")
    cut=(arb(95) if q!=210 else q*V*arb("1.03")*(1+(V*R)**(-arb(1)/5))*( (V*R)**(-arb(3)/5) ).exp()/arb.pi())
    if cut/h.exp()+2<w.exp():
        hc,spec,tail=local_right_rows(u,d,w,h,q,cells=64,**extras)
        rr=rr.min((-e*Y.log()).exp()*(hc*lo+spec[-1]+tail*high))
    if q==210:return rr.min(exact_right(u,d,w,h))
    return rr


def window(low,size,cases,base,alpha,core,q):
    R=arb(size)/2;u=R.log();sigma=A(".854");best=None
    assert 4*M<R and ((1+2/R)/V)**M<A(".000001")
    assert 1/(1-(A(".5")+2/R)**M)<1+A(".000001")
    norm=(1+A(".000001"))**2/(1-1/arb(low))
    for ds,ws,hs in cases:
        d=A(ds);y=R*A(hs).exp();a2=2*(y.log()+2)/y
        assert (1+a2)**15<A("1.5")
        L=left(low,size,ws,hs,base,alpha,core,ctx.prec,q)
        RR=right(size,ds,ws,hs,ctx.prec,q)
        args=(u,d,L,RR,norm,size*a2**2/arb.pi(),arb(1))
        g=rings(low,size,ws,hs,ctx.prec,q=q)
        _,s0=detector_floor(sigma,u,d,L,RR)
        center=int(float(s0)*10000+.5)
        for j in range(center-33,center+22):
            s=arb(j)/10000
            if s>=sigma: continue
            v=hinge_angular(s,args,g)/(sigma-s)
            if best is None or v<best[0]:best=(v,ds,ws,hs,j,L,RR)
    print("window",low,size,"upper",best[0].str(14),"param",best[1:5],
          "left",best[5].str(7),"right",best[6].str(7),flush=True)
    return best[0]


def evaluate(parts,cases,base=210,alpha="1",core=131072,q=210):
    target=(arb(H)*(arb(5)/4).exp()).ceil().unique_fmpz()
    assert target and parts>=1
    endpoints=[H+(int(target)-H)*i//parts for i in range(parts+1)]
    result=sum(window(l,r-l,cases,base,alpha,core,q) for l,r in zip(endpoints,endpoints[1:]))
    print("parts",parts,"base",base,"total",result.str(15),"ratio",(result/805224).str(12),
          "target height ceil",target,flush=True)
    return result


def cumulative(cases,base,alpha,core,q=210):
    from short_block import normalized_row
    T=int((arb(H)*(arb(5)/4).exp()).ceil().unique_fmpz())
    U=arb(T).log();sig=A(".854")
    norm=(1+A(".000001"))**2/(1-1/arb(H))
    assert ((1+2/arb(T))/V)**M<A(".000001") and 8192<T
    best=None
    for ds,ws,hs in cases:
        d,w,lh=map(A,(ds,ws,hs))
        Y=T*lh.exp();a2=2*(Y.log()+2)/Y
        assert (1+a2)**15<A("1.5")
        def cm(u,width,logh,mod):
            return source(u,width,logh,mod,base,12)
        def c4(u):
            key=int((u*1000000).lower().floor().unique_fmpz())
            return moment(key,base,Fraction(alpha),ctx.prec,"centered")
        rows=[normalized_row(U,U,q,core,w,lh,cm,steps=s,fourth_fn=c4,
                             sieve_base=base,small_factor=arb(1)/12)[0] for s in (1,3,6)]
        L=min(rows)*T*U**2
        R=right(2*T,ds,ws,hs,ctx.prec,q)
        # Reflection gives the full cumulative moment over positive ordinates.
        # hinge_angular uses 1/pi for a single translated rectangle; divide
        # both endpoint norms by two to use 1/(2pi) over the reflected domain.
        args=(U,d,L/2,R/2,norm,(T-H)*a2**2/arb.pi(),arb(1))
        g=rings(H,T-H,ws,hs,ctx.prec,T,q)
        _,s0=detector_floor(sig,U,d,L,R);center=int(float(s0)*10000+.5)
        for j in range(center-33,center+22):
            s=arb(j)/10000
            if s>=sig:continue
            n=hinge_angular(s,args,g)/(sig-s)
            if best is None or n<best[0]:best=(n,ds,ws,hs,j,L,R)
    floor,_=detector_floor(sig,U,A(best[1]),best[5],best[6])
    print("radial floor at the selected pair of norms",floor.str(15),"floor ratio",(floor/805224).str(10),flush=True)
    print("cumulative",q,base,"upper",best[0].str(15),"ratio",(best[0]/805224).str(12),
          "parameters",best[1:5],"L",best[5].str(8),"R",best[6].str(8),flush=True)
    return best[0]

if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--q",type=int,default=210,choices=(210,2310))
    ap.add_argument("--prefix",type=int)
    ap.add_argument("--parts",type=int,default=1)
    ap.add_argument("--base",type=int,default=210,choices=(6,30,210))
    ap.add_argument("--alpha",default="1");ap.add_argument("--core",type=int,default=131072)
    ap.add_argument("--cases",default=".85,8.5,-2.8:.9,8.5,-3:.95,9,-3.2")
    ap.add_argument("--check")
    a=ap.parse_args();ctx.prec=192
    cases=[tuple(c.split(",")) for c in a.cases.split(":")]
    if a.prefix:
        ans=window(H,a.prefix,cases,a.base,a.alpha,a.core,a.q)
    else:
        ans=evaluate(a.parts,cases,a.base,a.alpha,a.core,a.q) if a.parts else cumulative(cases,a.base,a.alpha,a.core,a.q)
    if a.check:assert ans<arb(a.check)
