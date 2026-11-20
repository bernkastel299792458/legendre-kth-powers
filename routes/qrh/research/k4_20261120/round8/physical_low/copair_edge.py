"""Connect the selected true Mellin rows to the round-number RH height."""
import argparse
from flint import arb,ctx
from copair_band import certificate,PHYSICAL_HEIGHT


def upper(gmax,lower_divisor,stop):
    height=arb(PHYSICAL_HEIGHT);start=2880000000000
    assert start<stop<PHYSICAL_HEIGHT-40
    def calc(a,b,j,kap,w,core=False):
        return certificate(i=j,k=55,kap=kap,w=w,h0=10**15 if core else 10**9,
                    gmax=gmax,lower_divisor=lower_divisor,full_square=True,band=(a,b),
                    core=core,spectral=not core)[-1]
    first=calc(0,1,58,6,22,True)+calc(1,start,58,6,22)
    tail=arb(0)
    a=start
    while a<stop:
        b=min(stop,PHYSICAL_HEIGHT-(PHYSICAL_HEIGHT-a)//2)
        margin=height-b
        w=(margin/32).log().min(arb(22))
        best=calc(a,b,58,6,w)
        best=best.min(calc(a,b,61,5,w))
        tail+=best
        a=b
    return first,tail,first+tail


if __name__=="__main__":
    ctx.prec=160
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--gmax",type=int,default=11)
    cli.add_argument("--lower-divisor",type=int,default=11)
    cli.add_argument("--through",type=int,default=3000000000000)
    cli.add_argument("--upper")
    a=cli.parse_args()
    values=upper(a.gmax,a.lower_divisor,a.through)
    print("core and broad band, boundary layers, complete ordinary Mellin contribution",
          *(x.str(15) for x in values),flush=True)
    if a.upper:assert values[-1]<arb(a.upper)
