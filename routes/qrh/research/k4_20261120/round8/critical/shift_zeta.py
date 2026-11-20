"""Even-strip bound for the true fourth moment to the left of the critical line."""
from math import prod

from flint import arb,ctx

from sweep_boundary import fourth


def gamma_scale(t):
    # See MOVING_LINE.md. Valid also with left real part -eta at the far edge.
    return arb("1.000001")*t.max(arb(10)**9)/(2*arb.pi())


def symmetric_upper(a,b,r):
    assert 0<=r<=1 and b>a>0
    return a*(r*(b/a).acosh()).cosh()


def positive_upper(a,b,h,d):
    ratio=b/a
    best=symmetric_upper(a,b,h/d)
    for z in (-2,-1,0,1,2,3,4,5,6,7):
        X=(ratio.acosh()+z)/(2*d)
        assert 2*d*X>4 and h/d<arb(1)/5
        loss=2*(h*X).sinh()**2
        ex=arb(1).exp()
        t=2*h*X
        tangent=(h*t.sinh()/(ex*(d-h))+4*h**2*t.cosh()/(ex*(d-h))**2+
                 loss*arb.pi()**2/(4*(X*ex*d)**2))
        tail=loss.min(tangent*(1+(-4*d*X).exp()))
        val=a+loss*a/2+tail*b/(2*d*X).cosh()
        best=best.min(val)
    return best


def squared_dirichlet(r,primes):
    assert r>1
    base=r.zeta()**4/(2*r).zeta()
    for k in primes:
        t=arb(k)**(-r)
        base*=(1+k*(k-2)*t)*(1-t)**2/(1+t)
    return base


def far_mean(U,V,p,d,eta,q,primes):
    """Sharp diagonal for zeta(s)^2 E_q(s) E_q(1-s) at sigma=1+eta."""
    D=squared_dirichlet(2+2*eta,primes)
    A=(1+eta).zeta()**2
    for k in primes:
        t=arb(k)**(-1-eta)
        A*=(1-t)*(1+(k-2)*t)
    error=6*(1+1/eta)*squared_dirichlet(1+eta,primes)+2*A**2/arb(2).log()
    v=arb("1.01");T=V.exp()
    assert 2*d*U>4 and arb(".01")<=eta<=arb(".4")
    # Freeze the positive factor T^(2d)/u^4 at V, and 1/T at U.
    a=gamma_scale(v*T)**(2*d)/V**4
    main=a*(D*v*(1/(1+2*d)+1/(p-1-2*d))+2*error/U.exp())
    cap=D*gamma_scale(arb(10)**9)**(2*d)*arb(10)**9/(U.exp()*U**4)
    return (1+arb("1e-9"))*arb(q)**(2*eta)*(main+cap)


def shifted_fourth(U,V,h,c4,q=210,eta=arb(1)/3):
    """Weighted integral / (T log(T)^4), uniformly for U<=log T<=V."""
    assert 29<=U<=V and 0<=h<=arb(".1") and arb(1)/8<=eta<=arb(2)/5
    if U<34:
        # The only height-dependent comparison in the analytic window proof.
        # For |t|>=D/2 the added power has nonnegative real part, and its
        # modulus differs from (|t|/D)^K by at most (1+9/D^2)^(K/2).
        K=2**32;D=arb("1.01")*U.exp()
        assert 3*K/D<arb.pi()/2 and (arb(1)/4+(arb("1.5")/D)**2).sqrt()<arb(".51")
        assert (-2048*arb(2).log()/K-1024*(9/D**2).log1p()).exp()>1-arb("1e-6")
        assert -(arb(1)-arb(".51")**K).log()*2048/K<arb("1e-9").log1p()
    primes=[p for p in (2,3,5,7,11) if q%p==0]
    assert prod(primes)==q
    p=2048-2*h
    v=arb("1.01");d=arb(1)/2+eta
    central=c4*v**(1+4/U)*p/(p-1-4/U)
    if h.is_zero():
        return central
    a=central*(1+arb("1e-9"))
    absolute=(1+eta).zeta()**4*prod(
        ((1-arb(k)**(-1-eta))*(1+arb(k)**eta))**2 for k in primes)
    T=V.exp()
    tail=v*(1/(1+2*d)+1/(p-1-2*d))
    early=arb(10)**9/T*(arb(10)**9/(v*T))**(2*d)
    b=(1+arb("1e-9"))*absolute*gamma_scale(v*T)**(2*d)*(tail+early)/V**4
    assert U>4/(2*d)
    # The early part /u^4 decreases with T. Holding the later cap fixed
    # and freezing just that normalized correction at U is an upper bound.
    b+=(1+arb("1e-9"))*absolute*gamma_scale(arb(10)**9)**(2*d)*arb(10)**9/(
        U.exp()*U**4)
    euler=prod(((1+arb(k)**(-arb(1)/2+h))/(1+arb(k)**(-arb(1)/2-h)))**2
               for k in primes)
    best=positive_upper(a,b,h,d)
    for vfar in (".018",".04",".08",".14",".22"):
        e=arb(vfar);dd=arb(1)/2+e
        bb=far_mean(U,V,p,dd,e,q,primes)
        best=best.min(positive_upper(a,bb,h,dd))
    return best*gamma_scale(v*T)**(2*h)*euler/(1-arb("1e-6"))


if __name__=="__main__":
    ctx.prec=160
    for u in (35,37,40):
        U=arb(u);V=U+arb(1)/2
        c=fourth(U,210,arb(".82"),arb(".34"),384)
        base=shifted_fourth(U,V,arb(0),c)
        for value in (".0025",".005",".01",".02"):
            h=arb(value);b=shifted_fourth(U,V,h,c)
            print(u,value,"normalized fourth upper",b.str(12),
                  "ratio",(b/base).str(10),flush=True)
