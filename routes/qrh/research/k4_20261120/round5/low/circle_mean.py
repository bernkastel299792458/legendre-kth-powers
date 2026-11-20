"""Interval Jensen bounds using the varying real part on each outer circle."""
from flint import arb
from functools import lru_cache
from finite_points import A, radial_bound, quintic
from radial_detectors import bound as general_radial


@lru_cache(maxsize=None)
def means(size,width,logh):
    H=3000175332800
    D=A(size); Y=(D/2)*A(logh).exp();X=Y*A(width).exp()
    N=arb((H+D+6).upper().ceil().unique_fmpz())
    a2=2*(Y.log()+2)/Y
    center=2-(1+a2)**15
    assert center>A(".5") and N>H+D+3 and X>Y and Y>1
    out=[]
    for label in ("1.44","1.58","1.72","1.86","1.96"):
        R=A(label); total=arb(0)
        for i in range(1,97):
            # Symmetry reduces the two semicircles to [0,pi]; cos is decreasing there.
            sig=2+R*(arb.pi()*i/96).cos()
            assert sig>0
            pow1=(1-sig).max(arb(0))
            z=N**pow1*(1+N.log()+1/arb(H-2)+1/sig)
            c=X**pow1*(1+X.log())
            e=arb(1)
            for p in (2,3,5,7):
                e*=1+arb(p)**(-sig)
            f=1+z*e*c
            if sig>1:
                b=sig-1
                f=f.min(Y**(-b)*sig*((1+Y.log())/b+1/b**2))
            total+=f.log1p()
        out.append((R,total/96))
    return out,-center.log()


def hinge_angular(s,args,rings):
    u,delta,left,right,norm,rightedge,_=args
    den=2-s+3*delta/u;nu=(2+4*delta/u)/den;p=3*(1-s+delta/u)/den
    assert 0<p<1 and 1<nu<2
    m=norm**nu*left**p*right**(1-p)/arb.pi()
    av,center=rings
    d=2-s
    rows=[]
    for R,a in av:
        assert R>d
        g=d/48*sum(1/(R/(d*j/48)).log() for j in range(1,49))
        rows.append((g,a))
    def horizontal(n):
        v=[g*(center+n*a) for g,a in rows]
        t=v[0]
        for x in v[1:]:t=t.min(x)
        return 2*d+rightedge+t
    candidates=[radial_bound(q,nu)*m+horizontal(q+1) for q in (3,4,5,6,7,8)]
    alt=quintic(nu,nu)
    if alt is not None:candidates.append(alt*m+horizontal(5))
    alt=general_radial(nu,nu)
    if alt is not None:candidates.append(alt*m+horizontal(8))
    best=candidates[0]
    for x in candidates[1:]:best=best.min(x)
    return best
