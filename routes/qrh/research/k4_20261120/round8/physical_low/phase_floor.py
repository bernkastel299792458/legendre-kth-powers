"""Lower bound for taking absolute values on a specific, physically significant phase band."""
from flint import arb,ctx
from actual_split import H,constants
from parity_target import kernel

def run():
    z,c,r,I,A,S,u=constants(1732099);x=arb(116).exp();xh=(c+2*r).exp();h=arb(H)
    q=arb(210);d=arb(int((z/11).floor().unique_fmpz()))
    assert 4*d**2<xh/23 and d**2>arb("70.7").exp() and d>z**2/d**2 and 2*d<z
    a=(1-arb("1e-12"))*h*(c-116);start=h*(c-116);b=2*arb.pi()-a
    step=(b-start)/2048;first=step*sum(kernel(start+step*j,a) for j in range(1,2049))
    w=arb(".0002");delta=w*x/h
    maxmass=xh/h*A+2*delta*S
    core=2*(c-b/h).exp()/h*first
    angle=h/4*(-2*r).exp()*(b/h).expm1()
    fourier=(1+angle.cos())*core-maxmass
    assert fourier>0 and angle<arb.pi()/2
    pi_count=(d/3*arb(4).log()-(2*d).sqrt()*(2*d).log()-(2*d+1).log())/(2*d).log()
    assert pi_count>1
    g=z.log()+arb("1.34")+arb("2.44")/z.sqrt()
    moment=pi_count*(pi_count-1)/(4*d**2*g**2)
    k0=h/(16*arb.pi());ncount=k0*q*d**2/xh-1
    pref=u*h*(-c).exp()
    val=2*pref/q*fourier*moment*ncount
    eps=arb("1e-5");frac=arb(".65")
    assert (c.exp()/(q*4*d**2))>arb(".14") and c.exp()/(q*d**2)<arb(".58")
    bad=c.exp()/(q*d)*2*eps/(arb(1)/4-eps**2)+1
    goodmoment=pi_count*(pi_count-1-bad)/(4*d**2*g**2)
    # Pairing the original two first lobes cancels their sine up to physical curvature.
    tiny=c.exp()/h*(b-start)/2*((2*b/h)*(b/h).exp()+h/4*(b/h)**2*(2*b/h).exp())
    imag=maxmass-core+tiny
    real=frac*fourier-(1-frac**2).sqrt()*imag
    goodn=(ncount*(arb(1)/2-frac**2)-1/(8*eps))/(1-frac**2)
    assert real>0 and goodn>0 and goodmoment>0
    realval=2*pref/q*real*goodmoment*goodn
    return val,realval,k0,2*k0,core*h/x,fourier*h/x,imag*h/x,real*h/x,pi_count/d,ncount
if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser(description=__doc__);cli.add_argument("--lower");cli.add_argument("--real");a=cli.parse_args()
    ctx.prec=160;v=run()
    print("absolute complex and real absolute contributions; phase endpoints; core/Fourier/imaginary cap/real part in units x/H; prime density; modes per q",*(t.str(14) for t in v))
    if a.lower:assert v[0]>arb(a.lower)
    if a.real:assert v[1]>arb(a.real)
