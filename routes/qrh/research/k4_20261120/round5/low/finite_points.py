"""Fixed-height Littlewood bounds, the universal radial-detector floor, and a short box."""
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx
from moving_window import A, centered_boundary, radial_bound
research=Path(__file__).resolve().parents[2]
for path in ("round5/spectrum","round5/mean","round5/left","round5/kernel"):
    sys.path.insert(0,str(research/path))
from short_block import cm_local,normalized_row
from mixed_low import mixed_low_rows
from local_energy import local_right_rows
from direct_high import direct_high
from quintic import bound as quintic


def fixed_right(u,delta,W,logh,q):
    n=16
    low=mixed_low_rows(u,delta,W,W,arb(0),logh,q,cells=n,tight=True)[-1]
    kwargs={} if q==210 else dict(spacing=210,outer_spacing=q,frequency_cut="100")
    hilb,rows,tail=local_right_rows(u,delta,W,logh,q,cells=n,**kwargs)
    high=direct_high(u,delta,W,logh,q)
    e=2*delta/u
    rr=(-2*delta-e*logh).exp()*(hilb*low+(rows[-1]+tail*high)*e/(2*delta))
    return rr*u


def fixed(u,delta,w,lg,q,core):
    H=arb(3000175332800)
    T=u.exp()
    assert T>H and 2*delta/u<=A(".1")
    W,logh=A(w),A(lg)
    lft=normalized_row(u,u,q,core,W,logh,cm_local)[0]
    rr=fixed_right(u,delta,W,logh,q)
    X=T*(W+logh).exp()
    Y=T*logh.exp()
    a2=2*(Y.log()+2)/Y
    assert (1+a2)**9<arb(3)/2
    assert ((1+2/T)/A("1.01"))**2048<A(".000001") and 8192/T<1
    assert 1/(1-(A(".5")+2/T)**2048)<1+A(".000001")
    norm=(1+A(".000001"))**2/(1-1/H)
    outer=11*(q*X).sqrt()*(T+6)
    return lft*T*u**2,rr,norm,(T-H)*a2**2/arb.pi(),outer


def hinge(s,u,delta,left,right,norm,rightedge,outer,asymmetric=False):
    den=2-s+3*delta/u
    nu=(2+4*delta/u)/den
    p=3*(1-s+delta/u)/den
    assert 0<p and p<1 and 1<nu and nu<2
    m=norm**nu*left**p*right**(1-p)/(2*arb.pi())
    if asymmetric:
        m*=2
    d=2-s
    geom=d/16*sum(1/(A("1.5")/(d*j/16)).log() for j in range(1,17))
    def edges(degree):
        return 2*d+rightedge+geom*(arb(2).log()+degree*outer.log())
    best=None
    for q in (3,4,5,6,7,8):
        amount=edges(q+1)+radial_bound(q,nu)*m
        best=amount if best is None else best.min(amount)
    alt=quintic(nu,nu)
    if alt is not None:
        best=best.min(edges(5)+alt*m)
    return best


def detector_floor(sigma,u,delta,left,right):
    a=2-sigma+3*delta/u
    c=3*(1+2*delta/u)
    k=(left/right).log()
    assert c*k>a
    gap=a*a/(c*k-a)
    r=sigma-gap
    nu=(2+4*delta/u)/(a+gap)
    p=3-c/(a+gap)
    return right*(k*p).exp()/(2*arb.pi()*arb(1).exp()*nu*gap),r


def counts(sigma,u,delta,left,right,norm,re,outer,asymmetric=False):
    floor,r=detector_floor(sigma,u,delta,left,right)
    center=int(float(r)*10000+.5)
    record=None
    for j in range(center-17,center+20):
        s=A(j)/10000
        if A(".5")<s and s<sigma:
            n=hinge(s,u,delta,left,right,norm,re,outer,asymmetric)/(sigma-s)
            if record is None or n<record[0]:
                record=(n,s)
    return *record, floor


def global_samples():
    U=A(35)
    cases=[(".85","8.8","-3.2",210),(".92","9.5","-3.5",210),
           ("1","9","-3.5",210),("1.1","9","-3.5",210),(".92","9","-3.5",2310)]
    sigmas=(800,825,850,860,874)
    best={}
    bestfloor={}
    for d,w,lg,q in cases:
        delta=A(d)
        args=fixed(U,delta,w,lg,q,131072)
        for j in sigmas:
            sigma=A(j)/1000
            n,s,lower=counts(sigma,U,delta,*args)
            bestfloor[j]=lower if j not in bestfloor else lower.min(bestfloor[j])
            if j not in best or n<best[j][0]:
                best[j]=(n,s,d,q,args[0],args[1])
    for j in sigmas:
        n,s,d,q,left,right=best[j]
        sigma=A(j)/1000
        target=7*U*(U*3*(1-sigma)/(3*sigma-1)).exp()
        print(j,"count",n.str(13),"target",target.str(12),"ratio",(n/target).str(11),
              "any radial floor/target",(bestfloor[j]/target).str(10),
              "s",s.str(6),"delta",d,"q",q,"AL",left.str(8),"AR",right.str(8),flush=True)


def near_height():
    H=A(3000175332800)
    D="5000000"
    U,delta,*args=centered_boundary(D,frozen=True)
    largest=arb(0)
    for j in range(800,875):
        sig=A(j)/1000
        n,s,_=counts(sig,U,delta,*args,asymmetric=True)
        target=7*H.log()*H**(3*(1-sig)/(3*sig-1))
        ratio=n/target
        assert ratio<1
        largest=largest.max(ratio)
        if j in (800,825,850,860,874):
            print("first window",j,n.str(13),target.str(12),ratio.str(10),flush=True)
    print("worst of all 75",largest.str(13),flush=True)
    U,delta,*args=centered_boundary("6500000",frozen=True)
    largest=arb(0)
    for j in (800,813,826,839,852,865):
        sig=A(j)/1000
        n,_,_=counts(sig,U,delta,*args,asymmetric=True)
        target=6*H.log()*H**(3*(1-sig)/(3*sig-1))
        assert n<target
        largest=largest.max(n/target)
    print("six coarse nodes to H+6500000",largest.str(13),flush=True)


def translated_midheight(size="100000000",frozen=False):
    U,delta,*args=centered_boundary(size,frozen=frozen,log_origin="35")
    for j in (850,865,874):
        sig=A(j)/1000
        n,s,_=counts(sig,U,delta,*args,asymmetric=True)
        print("translated at exp(35)",size,j,n.str(15),s.str(6),flush=True)
        if j==850 and size=="100000000" and not frozen:
            assert n<6164859
        if j==850 and size=="1000000000" and frozen:
            assert n<5178953


if __name__=="__main__":
    ctx.prec=192
    if sys.argv[1:]==["--billion"]:
        translated_midheight("1000000000",frozen=True)
    else:
        near_height()
        global_samples()
        translated_midheight()
