"""Whole verified-height Fejer mean of a true prime row, including its pole."""
from flint import arb,ctx
from actual_split import H,constants
from parity_target import kernel

def envelope():
    z,c,r,I,_,_,_=constants(1732099);K=arb(H);a=(1-arb("1e-12"))*K*(c-116)
    d=arb(".001");cap=arb(".402");eps=arb(".0002")
    # Dilation plus smoothing moves physical t by at most 2 eps*x/H.
    assert -K*(-2*eps*arb(116).exp()/K/(c-2*r).exp()).log1p()<d
    start=a-d;end=2*a+d
    for k in range(256):
        lo=start+(end-start)*k/256;hi=start+(end-start)*(k+1)/256
        den=((hi/2).sinc())**2
        # For v in [a,2a+2d], g(v) decreases; lo-d may dip below a,
        # where g is still positive decreasing, but use a as supported endpoint.
        v=(lo-d).max(a)
        assert kernel(v,a)/den<cap
    # Beyond 2a, use the rational form and the Lipschitz numerator.
    uc=2*a;den=2*((1-d/uc)**2-1/4)
    assert ((1+a.cos())/2+d/(1-a.cos()-d))/den<cap
    return cap*(2*r).exp()

def energy(l,b):
    K=arb(H);T=arb(1000);wmax=arb(20)/T;pi=arb.pi();ll=l.log();lb=b.log()
    assert 599<l and l<=b and b<arb("2.169e25") and b<=2*l
    length=(b/l).log()
    # Sweeping the positive zero Poisson sum at sigma=2 yields N(t-v,t+v)
    # <= c0(v+8) for the finite RH zeros and 0<=v<=2H.
    c0=(5+(3*K+20).log()/2)/(arb(8)*2/3).atan()
    logmoment=2+2*(1+K*length).log()
    zeros=(wmax*wmax/8).exp()*c0*(logmoment+8*length)/l.sqrt()
    power=lb/l*(b.sqrt()-l.sqrt()+1+b**(arb(1)/3)*lb/arb(2).log())
    unit=12+2*(K+5).log();invw=K/20
    high=4*(wmax**2/2-(20*(1-2/T))**2/4).exp()*(unit*(1+pi.sqrt()*invw)+2/K*(2+4*invw**2))
    line=2/l**2*(2*wmax*wmax).exp()/(2*pi)*((10+(K+3).log())*(2*pi).sqrt()*invw+2*invw**2/(K+3))
    far=2*(-(arb(2).log()/wmax)**2/4).exp()*(2+2*arb("2.169e25")*pi.sqrt()*wmax*(wmax*wmax).exp())
    flat=(zeros+power+high+line+far+8*(2*b).log()/l)/ll
    swing=(4*(2*b).log()*(wmax*wmax/2).exp()+2)/ll
    theta=b.sqrt()*lb**2/(8*pi)
    edge=(2*length+2*theta/l)/ll
    err=K.sqrt()*flat+20*swing*(2*(K/T).log()/K).sqrt()+edge*T/K.sqrt()
    main=(2*pi*length/(ll*lb)).sqrt()
    return main+err,err,main

if __name__=="__main__":
    ctx.prec=144
    print("Fejer physical multiplier",envelope().str(13))
    z,c,r,I,A,S,u=constants(1732099);a=(1-arb("1e-12"))*H*(c-116);U=H*r;pi=arb.pi()
    sampling_tail=4*pi*(1+a.cos())*(1/U**2+1/(2*pi*U))/(1-(a/U)**2)
    print("odd-sample mass tail and forced area ratio",sampling_tail.str(13),((I-sampling_tail)/A).str(13))
    assert sampling_tail<arb("6.963e-7") and (I-sampling_tail)/A>arb("1.94489177")
    for j in (48,50,52,55,57):
        l=arb(j).exp();v=energy(l,l*arb(".1").exp())
        print(j,"whole t weighted L2 norm/error/continuous",*(t.str(10) for t in v))
