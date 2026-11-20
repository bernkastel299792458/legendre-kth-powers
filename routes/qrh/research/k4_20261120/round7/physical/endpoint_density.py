"""Two smooth positive endpoint distributions on the first exterior lobe."""
from fractions import Fraction
from flint import arb, fmpz
from bilinear import rational
from odd_sieve import denominator
from lobe_variation import derivatives


def components(a,b,K,power,cells=768):
    assert 1<=power<=6 and 0<b<7
    m=arb(power)
    c=m*(m-1)/(6*b*b)+m/(6*b)+arb(1)/20
    d=m/(6*b)+arb(1)/12
    h=b/cells
    caps=[arb(0),arb(0)];areas=[arb(0),arb(0)];osc=[arb(0),arb(0)]
    for i in range(cells):
        w=(2*i+1)*h/2;u=w/b
        v,vp=derivatives(a+w,a)
        q=u**power;dq=m/b*u**(power-1)
        for j,f,fp in ((0,1-q,-dq),(1,q,dq)):
            caps[j]-=h*f*v
            areas[j]-=h*w*f*v
            osc[j]+=h*abs(fp*v+f*vp).upper()
    left=abs(derivatives(a,a)[0]);right=abs(derivatives(a+b,a)[0])
    result=[]
    for j in (0,1):
        f=caps[j]+arb(0,(b*h**2*c/24).upper())
        A=areas[j]+arb(0,(b*h**2*(2*d+b*c)/24).upper())
        C=osc[j]+b*h*c/2+(left if j==0 else right)+f/K
        assert f>0 and A>0 and C>0
        result.append((f,A,C))
    return result


def cost(lo,hi,size,ratios,insides,modulus,provider,power):
    from cover import H
    l,h=map(arb,(lo,hi));K=arb(H+size);r=arb('1e-6')
    cmax=h+(4*(-l/4).exp()).log1p()/2
    a=(1-arb('1e-12'))*K*(4*(-h/4).exp()).log1p()/2
    b=2*(arb.pi()-a);mass=arb.pi()*a.sin()/a
    base=2*(cmax+r)*(r/2).exp()/mass
    assert l-r>arb('114.98') and cmax+r<116 and 2*arb.pi()/K<r
    pieces=components(a,b,K,power)
    total=arb(0);area=arb(0)
    for (f,A,C),ratio,width in zip(pieces,ratios,insides,strict=True):
        z=rational(Fraction(ratio))*((l-K.log())/2).exp();G=denominator(z,modulus)
        inside=rational(Fraction(width))
        assert 0<inside<a and z<(l-r).exp() and G>0
        err,_=provider(l,cmax,K,z,G,2**48,f,C,A+f*inside/2,False,True,inside,True)
        slope=base*r.exp()*int(fmpz(modulus).euler_phi())/(modulus*G)
        total+=slope*(A+f*inside/2)+base*K*(-l).exp()*f*z**2*err
        area+=A
    return area,total
