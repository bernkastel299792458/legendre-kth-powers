"""Compact-frequency test and modulus-210 cumulative hinges in the first L band."""
from flint import arb, ctx
from functools import lru_cache
from fractions import Fraction
from pathlib import Path
import sys

research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round4"/"euler"))
sys.path.insert(0,str(research/"round2"/"local"))
from verify_euler import A,boundary,coefficient,quintic_bound
from check_edge import budget


@lru_cache(maxsize=None)
def boundary_data():
    U,delta,W,logh=A("28.7"),A(".86"),A(9),A("-3.3")
    q=210
    left,right,norm=boundary(U,delta,W,logh,q,q,True,direct=True,fold="density")
    assert 9/((U+logh)/2).exp()<arb(1)/4 and q*(W+logh).exp()>1
    denom=A("15/14").log()
    ec=162*(-logh).exp()/(2*arb.pi())
    ec+=2*(2+(arb(2).log()+9*(11*arb(q).sqrt()*((W+logh)/2).exp()).log())/denom)
    return U,delta,left,right,norm,ec,27/denom


@lru_cache(maxsize=None)
def detector(j):
    U,delta,*_=boundary_data()
    s=arb(j)/1000
    lo,hi=(2+4*delta/U)/(2-s+3*delta/U),2/(2-s)
    assert A("1.4")<=lo and hi<=A("16/9")
    cd=coefficient(lo,hi)
    quin=quintic_bound(lo,hi)
    return cd if quin is None else cd.min(quin)


@lru_cache(maxsize=None)
def jump_data(low,upper):
    L=A(low)
    nodes=list(range(650,upper-14,2))+[upper]
    prev=arb(0)
    results=[]
    for i,j in zip(nodes,nodes[1:]):
        s,t=arb(i)/1000,arb(j)/1000
        slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        assert slope>prev
        results.append((s,slope-prev,detector(i)))
        prev=slope
    return results


def cumulative(H,T,low,upper):
    U,delta,left,right,norm,ec,es=boundary_data()
    L=A(low)
    u=T.log()
    assert u>U
    # CMS Lemma 9, differenced at the fixed lower endpoint.
    h=T-H
    count=arb(".3")*H.log()+6+((H/(2*arb.pi())).log()/(2*arb.pi())+arb(".15")/H)*h
    count+=h**2/(4*arb.pi()*H)
    count=count.min(T*u)
    value=((A(".65")-1)*L).exp()*count
    edge=ec+es*u
    for s,jump,cd in jump_data(low,upper):
        den=2-s+3*delta/u
        nu=(2+4*delta/u)/den
        p=(3*(1-s)+3*delta/u)/den
        hinge=cd*norm**nu*(T*left*u*u)**p*(right*u)**(1-p)/(2*arb.pi())+edge
        value+=jump*hinge
    return value


def cell(low,high,angle,upper=800,parts=32,cutoff_ratio=None):
    H,Q=arb(3000175332800),arb(10000)
    pi=arb.pi()
    l,h=A(low),A(high)
    d=(4*(-h/4).exp()).log1p()/2
    K=A(angle)/d if cutoff_ratio is None else A(cutoff_ratio)*H
    assert H<K
    a=K*d*(1-A("1e-12"))
    I=pi*a.sin()/a
    g0=(1-a.cos())/a**2
    top=K+128*Q
    gross,high_zero=budget(l,h,A("1.09"),K-H)
    base=gross-high_zero
    assert 0<a and a<pi and (2*pi-2*a)/512>arb(1)/1024
    cmax=h+(4*(-l/4).exp()).log1p()/2
    assert cmax+arb(7).log()-K.log()+A("1.09")<140
    assert 2*l.exp()/(1024*K*140**2)>arb(50).exp()+1
    far=2*K/I*(2*pi*g0)/(2*pi.sqrt()*Q)*(1/(16*Q**2)).exp()
    far*=top**2*(1+4/arb(128)**2)*(-arb(128)**2/4).exp()
    assert far<arb("1e-1700")
    heights=[H+(top-H)*i/parts for i in range(parts+1)]
    smooth=2*Q*a/(pi.sqrt()*K)
    caps=[]
    for t in heights[:-1]:
        angle=((1-t/K)*a).max(arb(0)).min(pi/2)
        caps.append((angle.sin()+smooth).min(arb(1))/a.sin())
    cold=arb(0)
    for i,(v,w) in enumerate(zip(caps,caps[1:]+[arb(0)])):
        jump=v-w
        if not jump>0:
            assert jump.contains(0)
            jump=jump.max(arb(0))
        if jump>0 or not jump.is_exact():
            cold+=jump*cumulative(H,heights[i+1],low,upper)
    # Right/left zero symmetry converts the total cosine majorant
    # cosine majorant into twice the single right-weight exponential.
    sym=2*(1/(16*Q**2)).exp()
    cold*=sym
    unit=sym*caps[0]*(-l/8).exp()
    allowed=(1-base-cold-far)/unit
    return allowed,base,cold,top


def prove():
    H=arb(3000175332800)
    for theta,ratio,allow in [(800,"1.008",75000),(810,"1.05",230000),
                              (820,"1.05",19000)]:
        score,base,cold,top=cell("115.03334","115.05",None,theta,cutoff_ratio=ratio)
        assert score>allow
        print("near the verified cutoff",theta,ratio,allow,score.str(13),
              "ordinate",top.upper().ceil().unique_fmpz())

    allowance=62000
    ceiling=arb(0)
    angles=("2.03","2.1","2.2","2.25","2.3","2.4","2.45","2.5","2.55")
    for year in range(115,176):
        slabs=8 if year<123 else 1
        yearly=arb(0)
        best_lower=None
        for i in range(slabs):
            l=max(Fraction("115.03334"),Fraction(year)+Fraction(i,slabs))
            h=Fraction(year)+Fraction(i+1,slabs)
            for angle in angles:
                score,base,cold,top=cell(str(l),str(h),angle)
                if score>allowance:
                    yearly=yearly.max(top)
                    best_lower=score if best_lower is None else best_lower.min(score)
                    break
            else:
                raise ValueError(f"no passing cutoff in {l} to {h}")
        ceiling=ceiling.max(yearly)
        if year<123 or year in (129,139,149,159,169,175):
            print("through",year+1,"cumulative ordinate",ceiling.upper().ceil().unique_fmpz(),
                  "year allowance lower bound",best_lower.str(12))
        if year==122:
            assert ceiling<arb("2.55e13")
    assert ceiling<arb("1.31e19") and H>arb(3*10**12)


if __name__=="__main__":
    ctx.prec=192
    prove()
