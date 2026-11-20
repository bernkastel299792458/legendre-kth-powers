"""Q-sieved low Selberg norm from Mellin--Plancherel and discrete transfer."""
from flint import acb, arb, ctx

from variance import smooth_values


def _rectangle(a,b):
    return a.union(b)


def _integral(l,u,W,primes):
    # z=(v-1)/2+it. The half-line integral includes its 1/pi factor.
    P0=arb(1)
    for p in primes:
        P0*=1-arb(1)/p
    def box(a,b,depth=0):
        z=acb(_rectangle(l/2,u/2),_rectangle(a,b))
        den=arb(1)
        for p in primes:
            factor = abs(1-(-(1+z)*arb(p).log()).exp()).lower()
            den *= factor.max(arb(0))
        if b<=arb(".25"):
            # Evaluate z*zeta(1+z) at the removable singularity.
            # One Euler--Maclaurin correction bounds the analytic
            # remainder by |z(1+z)|/(12*16^2) times
            # (1+|2+z|/(2+Re z)).
            zreg=(-z*arb(16).log()).exp()
            for n in range(1,16):
                zreg+=z*(-(1+z)*arb(n).log()).exp()
            zreg+=z*(-(1+z)*arb(16).log()).exp()/2
            den*=abs(zreg).lower()-abs(z*(1+z))*(1+abs(2+z)/2)/(12*16**2)
            num=arb(1)
            if a>0:
                num=num.min(abs((-W*z).expm1())/(W*((l/2)**2+a**2).sqrt()))
        else:
            den*=abs((1+z).zeta()).lower()*((l/2)**2+a**2)
            num=abs((-W*z).expm1())/W
        if not den>0:
            if depth>=12:
                raise ArithmeticError("could not enclose the reciprocal zeta")
            m=(a+b)/2
            return box(a,m,depth+1)+box(m,b,depth+1)
        return (b-a)*(num.upper()/den.lower())**2
    total=arb(0)
    for start,end,subdiv in [(0,1,512),(1,4,128),(4,12,32),(12,100,16)]:
        for i in range(start*subdiv,end*subdiv):
            total+=box(arb(i)/subdiv,arb(i+1)/subdiv)
    # Leong, Corollary 4 and Table 5 at 100. Integrate (log t)^2/t^4.
    at=arb(100)
    v=at.log()
    total+=4*(arb("4.339")/(W*P0))**2*(v*v/3+2*v/9+arb(2)/27)/at**3
    if not total.is_finite():
        raise ArithmeticError("finite integral envelope")
    return total/arb.pi()


def mellin_low_rows(U,delta,W,logh,q,cells=4):
    """Tuple of upper bounds for S_Q(1+e)/(Y^-e*log T), one per closed e-cell."""
    e0=2*delta/U
    ly=U+logh
    if not (0<e0 and e0<=arb(".1") and ly>16 and W>0):
        raise ValueError("low norm parameters")
    _,primes=smooth_values(q,1)
    half=arb(1)/2
    eta=arb(1)
    zs=arb(1)
    zx=arb(1)
    xi=1-1/(12*arb(10).log())
    for p in primes:
        eta*=1-arb(1)/p
        zs/=1-arb(p)**(-half)
        zx/=1-arb(p)**(-xi)
    even=2 in primes
    g0=arb(3).sqrt()*(arb(2).sqrt()-1)/2 if even else arb(1)
    g1=arb("1.4378")*(1-arb(2)**(-xi)) if even else arb(1)
    A=arb(".0336")*g1*arb(2)**e0*zx
    H0=(arb("4.86")*g0+arb("2.93")+arb("5.17")*e0)*zs*arb(2)**e0
    H1=arb("2.83")*e0*zs*arb(2)**e0
    jack=arb(2)/5
    S=(1-jack)*ly
    assert S>arb(15).log()
    decay=(-W/2).exp()
    H0=H0*(1+decay)+H1*W*decay
    H1*=1+decay
    v=H0+H1*S
    head=(2*A*(1/S+1/ly**2).sqrt()
          +(-S/2).exp()*(v*v+2*H1*v+2*H1**2).sqrt())**2/W**2
    # On j>Y^jack, bounded interval discrepancy times total variation.
    bmax=1+2/eta
    variation=(bmax**2+2*bmax*(1+1/W))*2**len(primes)
    if not e0-jack*(1+e0)<0:
        raise ValueError("discrete remainder must decay")
    err=variation*((e0-jack*(1+e0))*ly).exp()
    out=[]
    for i in range(cells):
        l,u=e0*i/cells,e0*(i+1)/cells
        moment=_integral(l,u,W,primes)
        prod=arb(1)
        for p in primes:
            prod*=1-arb(p)**(-1-u)
        coeff=prod*(1+u*(arb(1)/2+(1+u)/12))/(2*delta)
        out.append(coeff*(eta*moment+head+err))
    return out


if __name__=="__main__":
    import sys
    ctx.prec=96
    for q in map(int,sys.argv[1:] or [6]):
        rows=mellin_low_rows(arb(49),arb(".9"),arb("10.7"),arb("-4.85"),q)
        print(q,[x.str(12) for x in rows],flush=True)
