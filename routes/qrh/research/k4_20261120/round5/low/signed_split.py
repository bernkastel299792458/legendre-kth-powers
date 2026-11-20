"""Signed-contour costs after discarding left zeros and high exterior ordinates."""
from flint import arb,ctx


def row(j,k):
    H,N=arb(3000175332800),arb(32768)
    s=arb(j)/1000
    T=H*(arb(k)/4).exp()
    V=T*arb(101)/100
    delta=T/100
    Y=512*V
    u=Y.log()
    eps=1/u
    b2=2*(arb(3)/8)**2
    z=1-s+eps
    # Absolute Gaussian coefficient mass on the eta-line, for eta>s.
    S=Y**z*(z*z/(2*b2)).exp()*(1+u)**2
    A=(2*T).log()/2+3
    omega=N.log()
    assert omega>10
    # The uniform factor 2/[omega(1+lambda^2)] for the Laplace integrals.
    assert 6+10/omega<7 and 1+7/omega<2
    left=4*A*S/(arb.pi()*delta*omega)
    reference=S/(arb.pi()*delta*omega**2)
    trivial=reference*(2-s)/(2*s)
    pole_tail=S*(2-s)/(2*arb.pi()*T)
    remote=14*A*S*(2-s)/(arb.pi()*delta*omega**2)
    border=5*A*S*(2-s)*(1+(2*V+1).log())/(4*arb.pi()*delta)
    # Alternative finite von Mangoldt polynomial with a triangular taper.
    # For m>=2, 1-(1-m/M)_+ <= sqrt(m/M).
    M=2**40
    trunc=5*M**(-arb(1)/2)*reference
    same_line=S*(1+(arb(M)**(1-s)-1)/(1-s))/(4*arb.pi()*delta*omega)
    total=left+reference+trivial+pole_tail+remote+border
    target=6*T.log()*T**(3*(1-s)/(3*s-1))
    return target, (left,reference,trivial,pole_tail,remote,border,trunc,same_line,total)


if __name__=="__main__":
    ctx.prec=192
    maxima=[arb(0) for _ in range(9)]
    maxrel=arb(0)
    for k in (1,4,9,17,30,51):
        for j in (800,820,837,852,865):
            target,terms=row(j,k)
            maxima=[a.max(b) for a,b in zip(maxima,terms,strict=True)]
            maxrel=maxrel.max(terms[-1]/target)
    for name,value in zip(("left","reference","trivial","pole-tail","remote","border",
                           "finite-Von-Mangoldt-tail","same-line-smooth-prime-polynomial","total"),maxima,strict=True):
        print(name,value.str(17))
    print("relative",maxrel.str(17))
    assert maxima[0]<arb(".000255") and maxima[6]<arb("1.64e-12")
    assert arb(2).sqrt()*maxima[6]<arb("2.32e-12")
    assert maxima[-1]<arb(".030834") and maxrel<arb("1.0350e-8")
