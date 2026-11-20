"""Dual exterior mass and necessary frequency reach for signed prime tests."""
from flint import arb, ctx


def capacities(lo, hi, hmin, hmax, eta, log_min):
    a = arb
    radius = a(".0001")
    pi, H = a.pi(), a(3000175332800)
    hmin, hmax = H*a(hmin), H*a(hmax)
    lo,hi = a(lo),a(hi)
    d = lambda L: (4*(-L/4).exp()).log1p()/2
    s_min, s_max = 2*pi-2*hmax*d(lo), 2*pi-2*hmin*d(hi)
    assert 0<s_min and s_max<2*pi
    cmax = hi+d(lo)
    jac = (3*radius/2).exp()/(lo-radius)
    primary = (radius/2+2*pi/hmin).exp()/(lo-radius)*(2*pi/s_min)
    primary *= cmax+radius-hmin.log()+s_max.log()+eta
    repeat = jac*4*pi/(2*pi+s_min)*(cmax+radius+(2*radius).log()+eta)
    clipped = (radius/2).exp()/(lo-radius)*2*pi/s_min*(log_min+eta)
    return primary.max(repeat).max(clipped), s_min, s_max


def box(L, hmin, hmax):
    new, s_min, s_max=capacities(L,L,hmin,hmax,arb("1.1328"),70)
    old, *_=capacities(L,L,hmin,hmax,arb("1.09"),50)
    return new.max(old),s_min,s_max


def verify():
    ctx.prec=192
    for L,lam,reach,reach_lam,sub,sub_lam,tail_min,first_min,sub_first in [
        ("115.1","1.01960","1.0126","1.000015","1.005","1.0116",
         ".0075274",".0125447",".0069"),
        ("115.2","1.05798","1.0381","1.00023","1.025","1.0193",
         ".0222828",".0365645",".0116"),
    ]:
        err=3*(arb(50)+arb("1.1328"))*(-arb(50)).exp()
        for lo,hi,mult in [("1","1",lam),(reach,reach,reach_lam),("1",sub,sub_lam)]:
            cap,s,_=box(L,lo,hi)
            mult=arb(mult)
            assert mult*cap+err<2
            assert mult*(arb(".0001")/2).exp()*2*arb.pi()/(s*(arb(L)-arb(".0001")))<arb(".03")
            deficit=1-1/mult
            hfloor=arb(3000175332800)/2
            distance=arb(".0001")-arb(1000)/(2*hfloor)
            scaled=hfloor*distance
            tail_coeff=4/(scaled*(1-(arb.pi()/scaled)**2))
            tolerance=deficit*s/(2*arb.pi())
            if lo==hi:
                condition=100000 if lo=="1" else 200
                assert condition*tail_coeff < tolerance
            if lo==hi=="1":
                b=arb.pi()-s/2
                escaped=deficit*s/(2*arb.pi())
                first=deficit*s/(4*b.sin())
                assert escaped>arb(tail_min) and first>arb(first_min)
                print(L,"cutoff",hi,"first harmonic",first.str(16),"tail",escaped.str(16))
            if lo!=hi:
                assert deficit*s/4>arb(sub_first)
            print("uniform",lo,hi,"capacity",cap.str(16),"multiplier",mult.str(10))


if __name__=="__main__":
    verify()
