"""Parameter-uniform floor for the numerical expression in rStation 168, Theorem 1."""
from flint import arb,ctx


def floor():
    H=arb(3000175332800)
    pi=arb.pi()
    amax=arb("0.708")
    z0=arb(8).log()
    z1=(2*H/(2*pi)).log()
    best=None
    for i in range(200):
        lo,hi=amax*i/200,amax*(i+1)/200
        h=(amax-lo)/2
        for j in range(160):
            left=z0+(z1-z0)*j/160
            right=z0+(z1-z0)*(j+1)/160
            diagonal=(-hi*right).exp()/(1+hi)
            remainder=pi*arb("15.203")**2*(1+left)**2*((1-hi)*left).exp()/H
            val=H*((diagonal.sqrt()+remainder.sqrt())**2).log1p()/(2*pi*h)
            best=val if best is None else best.min(val)
    return best


if __name__=="__main__":
    ctx.prec=160
    lower=floor()
    print("any partition of the first dyadic block, cumulative formula floor",lower.str(17),flush=True)
    assert lower>1082428176
