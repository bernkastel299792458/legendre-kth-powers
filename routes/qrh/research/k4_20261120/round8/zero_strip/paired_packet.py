"""A lower bound on a signed, beta-dependent local pair sum at exceptional ordinates."""
from flint import arb,arb_series
from isolated_packet import prime_energy
from strip_boundary import PI,H,T,THETA,S


def paired_ratio(half,d,v,r):
    t=r*r; z=d*d; k=v*v/4
    h=half**2-z
    val=h+t+4*z*t/(h+t)
    slope=1+4*z*h/(h+t)**2
    # The bracket (h+t)+4 z t/(h+t) is concave in t.
    y=(1/k-val/slope).max(0)
    return (-k*(t+y)).exp()*(val+slope*y)/(2*half)


def check(eta,R,U,v,c,multiplier='1',verbose=True,restricted=False,subtraction=None):
    eta,R,U,v,c=map(arb,(eta,R,U,v,c))
    k=lambda a:(-a*U+(a*v)**2/2).exp()
    real=arb(1)/2
    zeta=arb_series([c,1],2).zeta()
    half=c-real
    P=((T+3)/(2*PI)).log()/2-zeta[1]/zeta[0]+arb('1e-8')
    assert 1<c<2 and S>eta>real and U/v**2>THETA and v**2/2>=1/(2-THETA)**2
    assert U>arb('.75')*v*v and R>0
    # Full inner products of two Gaussian packets have decay exp(-v^2 y^2/4).
    low=arb(0);last=paired_ratio(half,arb(0),v,arb(0))
    for i in range(1,17):
        b=real+(eta-real)*i/16
        now=paired_ratio(half,b-real,v,arb(0))
        low=low.max((k(THETA-b)+k(THETA+b-1))*last.max(now))
        last=now
    far=(1+k(2*THETA-1))*paired_ratio(half,eta-real,v,R).max(paired_ratio(half,THETA-real,v,R))
    left=k(THETA+eta-1)*last.max(paired_ratio(half,THETA-real,v,arb(0)))
    removed=(P-2*half/(half**2-(S-real)**2))*low.max(far).max(left)+k(THETA+S-1)
    if subtraction is not None:
        removed=subtraction(eta,R,U,v)
    pad=arb(10)
    mod=(2*PI).sqrt()*v
    poles=(k(THETA)+k(THETA-1))*(-(v*(H-pad))**2/2).exp()
    arch=k(THETA-real)/(2*PI)*((2*PI).sqrt()/v*((T+pad+4).log()+6)+2/v**2)
    negative=3*(-U**2/(2*v*v)).exp()
    if not U/v**2>=2:
        z=arb_series([1-THETA+U/v**2,1],2).zeta()
        negative=(-z[1]/z[0])*(-U**2/(2*v*v)).exp()
    even=arb(2).log()*k(THETA)*(1+(2*PI).sqrt()*v/arb(2).log())
    if restricted:
        even=sum((arb(p).log()+mod)*k(THETA) for p in (2,3,5,7))
    edge=2*(1+THETA)*(-(v*pad)**2/2).exp()/v**2*((((T+2).log()/2+3)/pad)+1)
    single_norm=PI.sqrt()/v
    charge=removed+arb(2).sqrt()*(poles+arch+(negative+even)/mod)+edge/single_norm
    m=k(THETA-S)
    lam=arb(multiplier)
    assert 0<lam<=1 and (2-lam)*m>charge
    per=m*m-2*m*charge/(2-lam)
    S0,S1=(prime_energy(j,U,v) for j in (0,1))
    energy=(T-H+2*pad+arb('4.2'))*S0+arb('4.2')*S1
    if restricted:
        w=arb('.001');padding=arb(10)**9
        mass=1-4/(PI*w*padding)
        K=arb('.915503')+(w/2).exp()*w.expm1()**2/12
        t0=((T+pad+padding)*S0+K*S1)/mass
        t1=((T-H+2*pad+2*padding)*S0+2*K*S1)/mass
        energy=t0.min(t1)
    cost=energy/(mod**2*single_norm*lam*(2-lam))
    gap=per-cost/420071
    if verbose:
        print('threshold',eta.str(6),'radius',R.str(5),'U,v,c',U.str(6),v.str(6),c.str(6),
              'per',per.str(10),'cost',cost.str(10),'isolated cap',(cost/per).str(13),
              'signed weighted deficit per zero',gap.str(13))
    return gap,cost/per


if __name__=='__main__':
    for row,goal,count in [
        (('.70',2,'30.53','2.83','1.39','.88'),'.32930',144452),
        (('.75',2,'30.69','2.42','1.33','.70'),'.22823',178615),
        (('.77','1.5','31.15','2.98','1.26','.70'),'.11332',267151),
        (('.78','1.5','31.22','2.94','1.27','.60'),'.04100',352422),
        (('.784','1.5','31.30','3.01','1.27','.59'),'.00488',410977),
        (('.75','1.1','31.5','3.90','1.27','.64'),'.04878',357604),
    ]:
        gap,cap=check(*row)
        assert gap>arb(goal) and 0<cap<count
