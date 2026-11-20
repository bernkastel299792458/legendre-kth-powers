"""Gaussian piece of the genuine lcm-phase sum of signed Selberg weights."""
from flint import arb,ctx,fmpz
from bilinear_band import derivative_norm
from selberg_band import band


def dirichlet_masses(s,cap,gcut):
    # F(m)=(m/phi(m))*product_{p|m} (1-p^-s)^-1 for squarefree m.
    factors=[arb(1) for _ in range(cap+1)]
    for p in range(2,cap+1):
        if not fmpz(p).is_prime():continue
        fp=arb(p)/(p-1)/(1-arb(p)**(-s))
        for n in range(p,cap+1,p):factors[n]*=fp
        for n in range(p*p,cap+1,p*p):factors[n]=arb(0)
    hmass=gmass=arb(0)
    for n in range(1,cap+1):
        if factors[n].is_zero():continue
        v=(factors[n]/arb(n)**s)**2
        hmass+=v
        if n<=gcut:gmass+=arb(n).sqrt()*v
    return hmass,gmass


def prime_ratio(z):
    product=1
    rate=arb(1)
    for p in range(2,1000):
        if fmpz(p).is_prime():
            product*=p
            if product>z:return rate
            rate*=arb(p)/(p-1)
    raise ValueError("primorial cutoff")


def gaussian_integral(w):
    return (2*arb.pi()).sqrt()*w*(w*w/2).exp()


def calculate(x,logk,logt,i,k,m,gcut,cap):
    assert 2*gcut<=cap
    width=arb(1)/32
    delta=width/arb(2).sqrt()
    T,K,X=arb(logt).exp(),arb(logk).exp(),arb(x).exp()
    z=X*arb(2).sqrt()
    G=z.log()+arb("1.331")
    assert cap<X
    U=band(x,logt,i,k,m,uniform=True)
    h=arb(2).log()/2
    raw=[2*arb.pi().sqrt()*width*(((j+1)*width)**2).exp()
         +cap*((j*width)**2).exp()/X for j in (0,1)]
    leak=(-(h/(2*width))**2).exp()*((z.log()+3+2*(1+x))*raw[0]+2*raw[1])/G
    hmass,gmass=dirichlet_masses(arb(i)/100,cap,gcut)
    def fourier(kap):
        v=1/(8*delta**2)+kap**2*(1-2*(delta**2).exp()+(4*delta**2).exp())
        return (2*arb.pi().sqrt()*delta*v.sqrt()).sqrt()
    core=(U+leak)**2*fourier(K)*gmass*hmass
    t=T-1000
    order=16
    fourier_tail=derivative_norm(delta,K*gcut,order)*t**(arb(1)/2-order)/(arb.pi()*(2*order-1)).sqrt()
    fourier_tail+=fourier(K*gcut)*(arb(2).sqrt()*delta*1000).erfc()
    high=fourier_tail*(gaussian_integral(width)+cap/X)**2*arb(2).zeta()**2
    eps=(-(h/(2*delta))**2).exp()
    b=prime_ratio(z)/G
    B=b*gaussian_integral(delta)+eps*gaussian_integral(width)
    D=b+eps
    # Absolute tail for g>gcut, followed by g<=gcut but gh>cap.
    harm=1+arb(gcut).log()
    tail=B**2*(1/arb(gcut)+2*harm/cap)
    tail+=2*B*D/X*(1+z.log())*(1+harm)
    tail+=D**2*z/X**2*(1+harm)
    return core+high+tail,core,high,tail


if __name__=="__main__":
    ctx.prec=160;ctx.cap=32
    for a in ((49,19,27,61,245,20,128,8192),(55,15,27,59,245,20,1024,32768),
              (60,16,27,61,245,20,1024,32768),(70,16,27,59,245,20,1024,32768)):
        v=calculate(*a)
        print("signed lcm gaussian",a[:3],*(x.str(12) for x in v),flush=True)
