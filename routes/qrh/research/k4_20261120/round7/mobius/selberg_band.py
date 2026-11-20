"""A Gaussian subinterval of the actual highest dyadic Selberg coefficient block."""
from functools import lru_cache
from flint import arb,acb,ctx,fmpz
from poisson_power import estimate,right,H


def product(s):
    cutoff=500
    v=arb(1)
    for p in range(2,cutoff+1):
        if fmpz(p).is_prime():
            inv=arb(p)**(-s)
            v*=1+inv/((p-1)*(1-inv))
    tail=arb(cutoff)**(-s)/(s*(1-arb(1)/cutoff)*(1-arb(cutoff)**(-s)))
    return v*tail.exp()


@lru_cache(None)
def low_line(i,prec):
    """Enclose the full left edge of the low-ordinate rectangle."""
    assert prec==ctx.prec and i!=100
    s=arb(i)/100
    stack=[(j,4) for j in range(1600)]
    while stack:
        j,k=stack.pop()
        center=arb(2*j+1)/2**(k+1)
        height=arb(center,arb(1)/2**(k+1))
        if abs(acb(s,height).zeta())>arb(1)/256:continue
        assert k<20
        stack.extend(((2*j,k+1),(2*j+1,k+1)))
    return arb(256)


def band(logX,logt,i,k,m,uniform=False):
    X,T=arb(logX).exp(),arb(logt).exp()
    s=arb(i)/100
    u,euler,_=right(k,ctx.prec)
    width=arb(1)/32
    B=arb(3000)
    assert (uniform or T-B>100) and T+B<arb(H)/2 and T+B>=100
    q=estimate(s,T+B,k,m)
    if uniform:q=q.max(low_line(i,ctx.prec)).max(euler)
    vertical=q*X**(s-1)*((width*s)**2/2).exp()
    sides=2*width*(u-s)*q*X**(u-1)*(width**2*(u*u-B*B)/2).exp()
    tails=euler*X**(u-1)*((width*u)**2/2).exp()*(width*B/arb(2).sqrt()).erfc()
    plain=product(s)*(vertical+sides)+product(u)*tails
    h=arb(2).log()/2
    z=X*arb(2).sqrt()
    G=z.log()+arb("1.331")
    assert arb("2.44")/z.sqrt()<arb(".001")
    # Each sum of a positive unimodal shape costs its integral plus its maximum.
    raw=[2*arb.pi().sqrt()*width*(((j+1)*width)**2).exp()+((j*width)**2).exp()/X
         for j in (0,1)]
    leak=(-(h/(2*width))**2).exp()*((z.log()+3+2*(1+logX))*raw[0]+2*raw[1])
    return (plain+leak)/G


if __name__=="__main__":
    ctx.prec=192
    ctx.cap=32
    for (x,t,i,k,m),cap in zip(((43,26,63,245,20),(55,15,59,215,12),(60,25,61,245,20),(70,25,59,245,20)),
                               (".000152986","1.87876e-7","1.57519e-7","2.49856e-9"),strict=True):
        val=band(x,t,i,k,m)
        print("actual Selberg coefficient band, divided by X",x,t,val.str(14),flush=True)
        assert val<arb(cap)
