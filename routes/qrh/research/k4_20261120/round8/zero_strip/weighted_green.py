"""Two nearby real-part hinges with a cosine at the actual physical frequency."""
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx

research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/'round7'/'taper'))
from mellin_bridge import finite_row
from exact_bridge import radial_table,RLOW,angular_edge,interpolated_point,H
from strip_boundary import THETA

def radial(line,nu):
    ix=nu*200
    j=int(ix.lower().floor().unique_fmpz()); k=int(ix.upper().ceil().unique_fmpz())
    if j==k:return line[j-RLOW]
    t=(ix-j)/(k-j)
    return ((1-t)*line[j-RLOW].log()+t*line[k-RLOW].log()).exp()

def kernel(U,left,right,delta,n,frequency,ell=None):
    l=arb(1)/2 if ell is None else ell;r=1+delta/U
    t=(r-n)/(r-l)
    nu=4/(2+t);P=3*t/(2+t)
    L=(left*U**2).log()+U;R=(right*U).log()
    norm=((1+arb('1e-6'))**2/(1-1/arb(3*10**12))).log()
    base=(nu*norm+P*L+(1-P)*R).exp()/(2*arb.pi())
    pl=((r-n)*frequency).sinh()/(t*((r-l)*frequency).sinh())
    pr=((n-l)*frequency).sinh()/((1-t)*((r-l)*frequency).sinh())
    return nu,P,base,pl,pr

def coefficient_ratio(frequency,theta,a,b,eps):
    h=b-a;C=eps*(frequency*h).exp()
    assert 0<eps<=1 and eps*(frequency*h).sinh()<=frequency*h
    B=theta-a+C*(theta-b)
    K=(frequency*h).sinh()/frequency*(-frequency*(theta-b)).exp()
    return (1/(1+eps)).max(B/(B+eps*K)),C


def amplitude(C,frequency,gap,u,v):
    # C/2 times the integral of exp(-frequency*t) from gap+v-u to gap+v+u.
    # Its lower and upper bounds occur at the two opposite frequency endpoints.
    def value(t):return -C*(-t*(gap+v-u)).exp()*(-2*t*u).expm1()/(2*t)
    return value(frequency.upper()).union(value(frequency.lower()))

def demo(L=arb(143),a=arb('.865'),b=arb('.870'),eps=arb('.90')):
    x=4*(-L/4).exp()
    d=x.log1p(); freq=L+d/2
    t=arb(H)*(arb(7)/4).exp();upper=t+arb('.1');U=upper.log()
    assert 3*10**12<arb(H)-arb('.1') and arb.pi()/freq<arb('.1') and t*d<1
    delta,w,h=map(arb,('1.1','8.5','-2.25'))
    l,r=finite_row(U,U,delta,w,h,2**20,128,'1',210,'centered',2310,
                   causal='real',cutoff=300,prime=True,adaptive_core=True,jordan='rough')
    edge=angular_edge(U,U,w,h,q=2310)
    nr1,p1,z1,q1,r1=kernel(U,l,r,delta,a,freq)
    nr2,p2,z2,q2,r2=kernel(U,l,r,delta,b,freq)
    K,C=coefficient_ratio(freq,THETA,a,b,eps)
    chord=(L*(b-a)).exp()
    assert chord>C
    M=1+C+eps*(freq*(b-a)).cosh()
    fac1=(1+eps*q1)**p1*(1+eps*r1)**(1-p1)
    fac2=(1+q2)**p2*(1+r2)**(1-p2)
    scalar_a=z1*interpolated_point(nr1)+edge
    scalar_b=z2*interpolated_point(nr2)+edge
    old=scalar_a+chord*scalar_b
    options=[]
    for line in radial_table(ctx.prec):
        hi1=z1*radial(line,nr1)
        hi2=z2*radial(line,nr2)
        options.append(K*(hi1*fac1+C*hi2*fac2+M*edge)+(chord-C)*scalar_b)
    new=options[0]
    for v in options[1:]:new=new.min(v)
    scale=2*((a-1)*L).exp()*2*((L*(b-a)).cosh()-1)/(b-a)
    print('T',t.str(14),'L',L.str(6),'ordinates times physical width',(t*d).str(10))
    print('scalar hinge cap',old.str(14),'cosine hinge cap',new.str(14),'ratio',(new/old).str(12))
    print('two chord terms: old',(old*scale).str(13),'new',(new*scale).str(13),'saving',((old-new)*scale).str(13))
    assert old>new
    return old,new,scale

if __name__=='__main__':
    ctx.prec=160
    demo()
