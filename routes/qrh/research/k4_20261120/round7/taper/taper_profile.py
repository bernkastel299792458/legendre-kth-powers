"""Folded critical-line norm for an arbitrary convex combination of real trapezoids."""
from math import prod
from pathlib import Path
import sys
from flint import arb,arb_series

research=Path(__file__).resolve().parents[2]
for where in ("round6/folds","round6/phase","round5/kernel","round5/mean"):
    sys.path.insert(0,str(research/where))
from fold_mean import partial_folds


def layout(segments):
    """segments are (integer starting multiple of Y, log width, positive weight)."""
    assert all(a>=1 and w>0 and c>=0 for a,w,c in segments)
    assert sum(c for _,_,c in segments).contains(1)
    raw=[(arb(a).log(),w,c) for a,w,c in segments if not c.is_zero()]
    breaks=sorted([arb(0)]+[x for a,w,_ in raw for x in (a,a+w)])
    cuts=[breaks[0]]
    for x in breaks[1:]:
        if x>cuts[-1]:cuts.append(x)
        elif not x.overlaps(cuts[-1]):raise ArithmeticError("ambiguous breakpoint")
    rows=[]
    for lo,hi in zip(cuts,cuts[1:]):
        mid=(lo+hi)/2
        initial=rate=arb(0)
        for a,w,c in raw:
            if mid<a:initial+=c
            elif mid<a+w:
                initial+=c*(1-(lo-a)/w)
                rate+=c/w
            else:assert mid>a+w
        rows.append((lo,hi,initial,rate))
    return rows


def critical(U,lh,segments,q=2310,base=210,depth=12,pieces=64,fold_factory=partial_folds,by_row=None):
    default=layout(segments)
    T=U.exp()
    h=lh.exp()
    X=h*default[-1][1].exp()
    v,tau,m=arb("1.01"),arb("1.03"),2048
    p=(v*T)**(-arb(1)/5)
    wid=p**3
    corr=((1+p)*p*(2*wid).exp()).exp()/(1-4*p/arb.pi())
    primes=[k for k in (2,3,5,7,11,13,17,19) if q%k==0]
    assert prod(primes)==q and q%base==0 and h*T>1 and U>20
    rs=[r for r in range(1,q//base+1) if (q//base)%r==0]
    profiles={r:default if by_row is None else layout(by_row[r]) for r in rs}
    if by_row is not None:X=h*max(v[-1][1].upper() for v in profiles.values()).exp()
    rho=1/arb(2).zeta()
    zeta2=arb_series([2,1],prec=2).zeta()
    c0=arb.const_euler()-2*zeta2[1]/zeta2[0]
    for k in primes:
        rho*=arb(k)/(k+1)
        c0+=arb(k).log()/(k+1)
    c0*=rho
    C=2**len(primes)+2
    def tail(s,k):
        total=arb(0)
        for l,r,b,d in profiles[k]:
            a=s.max(l).min(r)
            va,vb=b-d*(a-l),b-d*(r-l)
            total+=(r-a)*(va*va+va*vb+vb*vb)/3
        return total
    offs={k:rho*(lh+tail(arb(0),k))+c0+3*C/(h*T).sqrt() for k in rs}
    off=max(a.upper() for a in offs.values())
    def harm(cut):
        tot=arb(0)
        for k in rs:
            z=cut/k
            assert z*T>1
            if z<=h:
                tot+=(rho*z.log()+c0+3*C/(z*T).sqrt())/k
            else:
                assert z>h
                tot+=(offs[k]-rho*tail((z/h).log(),k)+3*C/(z*T).sqrt())/k
        return rho*sum(arb(1)/k for k in rs)+tot.max(arb(0))/U
    def primitive(z,k):
        z=z.min(X)
        if z<=h:return z
        assert z>h
        total=h
        for l,r,b,d in profiles[k]:
            a=h*l.exp()
            end=z.max(a).min(h*r.exp())
            v=b-d*((end/h).log()-l)
            total+=end*(v*v+2*d*v+2*d*d)-a*(b*b+2*d*b+2*d*d)
        return total
    def energy(lo,hi,k):
        a,b=(lo/k).min(X),(hi/k).min(X)
        if a>=b:return arb(0)
        return ((primitive(b,k)-primitive(a,k))*rho+2*C*(b/T).sqrt()).max(arb(0))
    return fold_factory(depth)(base,q//base,rs,v,tau,m,v*m/(m-1),p,wid,corr,U,X,
                                pieces,harm,energy,rho,off)
