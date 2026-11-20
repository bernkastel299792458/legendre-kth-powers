"""Centered rational-window detector for a finite rectangle above verified RH."""
from fractions import Fraction
from flint import arb, ctx
from physical_tail import refine
from short_box import A, budget
from verify_euler import (linear_mean_coefficients, direct_high,
                         sharp_right, signed_high_norm, low_saving)
from adaptive import radial_bound
from sieved_fourth import fourth_six
from functools import lru_cache


@lru_cache(maxsize=None)
def centered_boundary(size, frozen=False, log_origin=None):
    D = A(size)
    H = A(3000175332800) if log_origin is None else A(log_origin).exp()
    R = D/2
    C = H+R
    U = R.log()
    q = 210
    delta, W, logh = A(".64"), A(8), A("-2.8")
    M, v = 2048, A("1.01")
    ybar = v*M/(M-1)
    eps = A(".000001")
    assert 4*M/R<1 and ((1+2/R)/v)**M<eps and 1/(1-(A(".5")+2/R)**M)<1+eps
    norm = (1+eps)**2/(1-1/H)
    Y = R*logh.exp()
    B = C+v*R
    c4 = fourth_six(B.log()) * B * B.log()**4 * M/(M-1-4/B.log())
    # For y<C the interval is positive and the factor half is exact.
    # Beyond C the second copy has measure at most (vR/C)^M before
    # accounting for polynomial growth of the cumulative fourth moment.
    rtail = (v*R/C)**(M-1-4/B.log())
    assert rtail<eps
    c4 *= (1+rtail)/2
    if frozen:
        from frozen_fourth import frozen_fourth
        c4=c4.min(frozen_fourth(H,D))
    cd,ch = linear_mean_coefficients(q, v*R,ybar,"density")
    old = arb.pi()*(1+A("2/3")*A("6/5").sqrt()).sqrt()
    hb = signed_high_norm(logh.exp(),W,Y,2*delta/U)
    high = direct_high(U,delta,W,logh,q)
    cd *= high.min(hb)/hb
    sc = ch/old
    right = sc*sharp_right(U,delta,arb.pi()*sc**2/(8*cd**2),W,logh)
    right -= ch*(-2*delta).exp()*low_saving(U,delta,W,logh,q)
    assert right>0
    div = {1:1}
    for prime in (2,3,5,7,11):
        f = prime if q%prime==0 else prime**2
        div.update({f*j:-sign for j,sign in div.copy().items()})
    assert Y>max(div)
    density = sum(A(sign)/j for j,sign in div.items())
    offset = sum((max(sign,0)-sign*A(j).log())/j for j,sign in div.items())
    harm = density+(density*(W/3+logh)+offset).max(A(0))/U
    taper = 2*(W+logh).exp()*(1-(1+W)*(-W).exp())/W**2
    unweighted = density*taper+sum(sign<0 for sign in div.values())/R
    cd,ch = linear_mean_coefficients(6,v*R,ybar)
    cm = cd*(1+A(1)/5)*(1+A(1)/7)*harm+ch*4*unweighted/U
    left = (c4**A("1/4")*(cm*R*U).sqrt()+(ybar*R)**A("3/4"))**A("4/3")
    a2=2*(Y.log()+2)/Y
    assert (1+a2)**9<arb(3)/2
    # The outer dip below the central line reaches Re z = 1/2.
    # Euler summation at N=1 gives the published easy bound 4*upper height.
    xmax = Y*W.exp()
    outer = 11*(q*xmax).sqrt()*(H+D+6)
    rightedge = 2*a2**2*D/(2*arb.pi())
    return U,delta,left,right*U,norm,rightedge,outer


def weighted(low,size,frozen=False):
    H,D,L=arb(3000175332800),A(size),A(low)
    U,delta,left,right,norm,rightedge,outer = centered_boundary(size,frozen=frozen)
    count=A(".3")*H.log()+6+((H/(2*arb.pi())).log()/(2*arb.pi())+A(".15")/H)*D
    count+=D**2/(4*arb.pi()*H)
    nodes=list(range(650,869,3))+[875]
    prev=arb(0)
    out=((A(".65")-1)*L).exp()*count
    for i,j in zip(nodes,nodes[1:]):
        s,t=A(i)/1000,A(j)/1000
        den=2-s+3*delta/U
        nu=(2+4*delta/U)/den
        p=(3*(1-s)+3*delta/U)/den
        assert 0<p and p<1 and 1<nu and nu<2
        power=norm**nu*left**p*right**(1-p)/arb.pi()
        horizontal_factor=arb(0)
        horiz_pieces=16
        for m in range(1,horiz_pieces+1):
            rad=(2-s)*m/horiz_pieces
            horizontal_factor+=(2-s)/horiz_pieces/(A("1.5")/rad).log()
        candidates=[]
        for q in (3,4,5,6,7,8):
            edge=2*(2-s)+horizontal_factor*(arb(2).log()+(q+1)*outer.log())+rightedge
            candidates.append(radial_bound(q,nu)*power+edge)
        hinge=candidates[0]
        for alt in candidates[1:]:
            hinge=hinge.min(alt)
        slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        assert slope>prev
        out+=(slope-prev)*hinge
        prev=slope
    return out


def scalar(lo,hi,stretch,parts=4,frozen=False):
    H,Q = arb(3000175332800),A(10000)
    K=H+stretch
    a=(1-A("1e-12"))*K*(4*(-A(hi)/4).exp()).log1p()/2
    I=arb.pi()*a.sin()/a
    S=stretch+1280000
    _,oldedge=budget(A(lo),A(hi),A("1.1328"),stretch)
    new=refine(lo,hi,stretch)[0]-oldedge
    eps=1/(16*Q**2)
    caps=[]
    heights=[H+A(S)*i/parts for i in range(parts+1)]
    for t in heights[:-1]:
        z=(a*(1-t/K)).max(A(0)).min(arb.pi()/2)
        caps.append((z.sin()+2*Q*a/(arb.pi().sqrt()*K)).min(A(1))/a.sin())
    cost=A(0)
    for i,(current,nxt) in enumerate(zip(caps,caps[1:]+[A(0)])):
        dem=Fraction(S*(i+1),parts)
        assert current>nxt
        cost+=(current-nxt)*weighted(lo,str(dem),frozen=frozen)
    cost*=2*eps.exp()
    g0=(1-a.cos())/a**2
    top=K+128*Q
    tail=2*K/I*(2*arb.pi()*g0)/(2*arb.pi().sqrt()*Q)*eps.exp()
    tail*=top**2*(1+4/A(128)**2)*(-A(128)**2/4).exp()
    assert tail<arb("1e-1700")
    return new+cost+tail,cost,new

if __name__=="__main__":
    ctx.prec=192
    lo,hi="115.033663","115.033675"
    total,zero_cost,other=scalar(lo,hi,50000000,8)
    assert total<arb("0.999999129") and zero_cost>0
    n=(A(hi)/4).exp().floor().unique_fmpz()
    assert 4*arb(n).log()<A(hi) and A(hi)<4*arb(n+1).log()
    print(lo,hi,"total",total.str(18),"zero cost",zero_cost.str(18),"last n",n)
