"""Arb checks for the full square AFE weight replacement."""
from flint import arb, ctx


def scaled_error(t, sigma, x):
    u = t/(2*arb.pi())
    return 3200*arb(1).exp()*x*u**(1-sigma)*(1+u.log())**2/((1-sigma)**2*t**2)


if __name__ == "__main__":
    ctx.prec = 128
    pi = arb.pi()
    h = arb(3*10**12)
    u = h/(2*pi)
    assert (arb("4.01").exp()/(2*pi).sqrt()*(38+16*(2/pi).sqrt())+1) < 1300
    assert 1300*(1+10/h**2)+10*arb(4).exp() < 1850
    assert 1300+1850 < 3200
    assert 2/(arb(1)-arb(7)/8) < u.log()
    low = 20*(-arb(100)).exp()/pi.sqrt()*scaled_error(h, arb(".7"), arb(10**14))
    for s, x, cap in [(arb(".70"), h**(arb(7)/8), ".002204"),
                      (arb(".85"), h**(arb(7)/8), ".000157"),
                      (arb(7)/8, arb(10**10), ".00001388")]:
        total = scaled_error(h, s, x)+low
        assert total < arb(cap)
        print("sigma", s.str(5), "scaled gamma replacement cost", total.str(14))
    s, x = arb(7)/8, arb(10**10)
    crude = 2*arb(1).exp()*x*u**(1-s)*(1+u.log())**2/(1-s)**2
    complex_bound = crude*(pi**2/16+4).exp()
    cutoff = complex_bound*(4*arb(-65).exp()+8*arb(-75).exp()+arb(-400).exp())
    high_t = complex_bound*arb(-395).exp()
    large_product = 4*crude*arb(-60).exp()
    total = scaled_error(h,s,x)+low+cutoff+high_t+large_product
    assert total < arb(".00001390")
    print("frequency cutoff", cutoff.str(14), "height cutoff", high_t.str(8),
          "product cutoff", large_product.str(14), "all", total.str(14))
