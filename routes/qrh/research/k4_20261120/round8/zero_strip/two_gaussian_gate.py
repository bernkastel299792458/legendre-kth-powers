"""Budget test for a two-Gaussian positive strip detector at one parameter point."""
from flint import arb
from isolated_packet import prime_energy
from strip_boundary import PI,H,T,THETA


def run():
    U=arb('35.5'); v=arb(6); a=THETA-arb('.865'); b=THETA-arb(1)/2
    normal=(2*PI).sqrt()*v
    q0=2/normal*(1+(-U*U/(2*v*v)).exp())
    B=q0*(T/(2*PI)).log()/4
    # Grant the arithmetic all deterministic archimedean and endpoint corrections for free.
    # A lower target cost at beta=.865 may be used for a method required to be uniform as beta decreases to s.
    extra=8*a/(normal*(2*b-a)**2)
    # Magnitude lost in extending the positive-frequency high Gaussian to the full line.
    k=(-a*U+(a*v)**2/2).exp()
    extra+=k*((U-a*v*v)/(v*arb(2).sqrt())).erfc()
    top=arb('.4')
    assert (1+k)*(-(v*top)**2/2).exp()+extra+a*v*(2/PI).sqrt()<B
    n=1024
    squares=arb(0)
    for j in range(n):
        lo=top*j/n; hi=top*(j+1)/n
        arg=arb((lo+hi)/2,(hi-lo)/2)
        cos=((U-a*v*v)*arg).cos().upper()
        # E[|Z| cos(yZ)] for a centered real Gaussian; near zero use the
        # positive enclosure via the monotonic primitive of exp(t^2).
        xhi=v*hi/arb(2).sqrt(); xlo=v*lo/arb(2).sqrt()
        upper_dawson=PI.sqrt()/2*(-xlo*xlo).exp()*xhi.erfi()
        correction=-a*v*(2/PI).sqrt()*(1-2*xhi*upper_dawson)+a*a*v*v/2
        val=(-(v*lo)**2/2).exp()*(1+k*cos)+extra+correction-B
        squares+=val.max(0)**2
    area=420070*2*top*squares/n
    S0,S1=(prime_energy(j,U,v) for j in (0,1))
    # Optimistic version of the existing Hilbert envelope, without padding,
    # its positive constants, or the cross-sign real-part endpoint.
    K=arb('.915503')
    current=(T*S0+K*S1).min((T-H)*S0+2*K*S1)/(2*normal**2)
    print('single-root allowance at 420070',area.str(14),
          'length-norm cost even granting half',current.str(14),
          'ratio', (current/area).str(12))
    assert current/area>arb('1.4')


if __name__=='__main__':
    run()
