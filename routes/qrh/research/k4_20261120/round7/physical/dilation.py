"""Choose a Selberg sieve level above sqrt(y) in the location-sensitive estimate."""
import argparse
from fractions import Fraction
from functools import lru_cache
from flint import arb,ctx,fmpz
from bilinear import bounding_sum,groups,lambdas,lower,upper,rational


@lru_cache(maxsize=32)
def frequencies(order,weighted,prec):
    assert prec==ctx.prec
    rows=[]
    n=1
    while n<=order:
        last=min(order,max(n,(9*n)//8 if weighted else (5*n)//4))
        if weighted:
            multiplier=arb(0)
            for k in range(n,last+1):
                r=arb(k)/(order+1)
                omega=r if 2*k==order+1 else arb.pi()*r*(1-r)*(arb.pi()*r).cot()+r
                assert omega>0 and omega<=1
                multiplier+=2*omega/(arb.pi()*k)+2*(1-r)/(order+1)
        else:
            harmonic=arb(last+1).digamma()-arb(n).digamma()
            multiplier=2*harmonic/arb.pi()+arb(2*(last-n+1))/(order+1)
        rows.append((n,last,multiplier))
        n=last+1
    return rows


def denominator(l,h,ratio,order,blocks=34,reciprocal=False,location_hi="115.12",weighted=False):
    c=rational(Fraction(ratio))
    assert c>=1 and order>=32 and 30<=blocks<=40 and 83<=l<h<=89
    trunc=2**24
    zlo=c*(arb(l)/2).exp()
    zhi=c*(arb(h)/2).exp()
    tlo=arb("114.98").exp()
    assert Fraction("115.12")<=Fraction(location_hi)<=116
    thi=arb(location_hi).exp()
    assert zhi<tlo and arb("1.33258")-arb("2.44")/zlo.sqrt()>arb("1.331")
    shift=arb("1.331")+c.log()
    G=arb(l)/2+shift
    gs=groups(trunc)
    lam=lambdas(G,zhi,blocks)
    assert len(gs)**2*blocks*(blocks+1)/2<2**23
    K=arb(1)
    for p in range(2,1001):
        if fmpz(p).is_prime():K*=1+arb(2)/(p*(p-1))
    K*=arb("0.002").exp()
    total=(K/G)**2/(order+1)
    tail=(1+arb(2).zeta())/trunc+2*arb(2).zeta()**2/2**blocks
    method=bounding_sum
    if reciprocal:
        from doublesieve import reciprocal_sum
        assert (arb.pi()/8/(arb.pi()/8).sin())**2<arb("1.06") and arb.pi()<4
        method=reciprocal_sum
    for n,last,multiplier in frequencies(order,weighted,ctx.prec):
        value=method(gs,lam,lower(zlo),upper(zhi),lower(tlo),upper(thi),
                           upper(1+zhi.log()),n,last)
        assert 0<value<1
        upper_value=arb(value)*(1+arb("1e-7"))+tail
        total+=upper_value*multiplier
    normalized=c*c*total
    a=arb(h)/2+shift
    eta=2*shift-2*normalized*a*a/(1+normalized*a)
    print(l,h,"ratio",ratio,"order",order,"relative error",normalized.str(10),
          "eta above",eta.str(14),flush=True)
    return eta


if __name__=="__main__":
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("--ratio",default="2")
    arg.add_argument("--order",type=int,default=512)
    arg.add_argument("--cell",type=int)
    arg.add_argument("--reciprocal",action="store_true")
    arg.add_argument("--location-hi",default="115.12")
    arg.add_argument("--weighted",action="store_true")
    arg.add_argument("--pieces",type=int,default=1)
    a=arg.parse_args()
    ctx.prec=192
    cells=range(83,89) if a.cell is None else [a.cell]
    assert a.pieces in (1,2,4,8,16)
    for p in cells:
        vals=[denominator(p+k/a.pieces,p+(k+1)/a.pieces,a.ratio,a.order,
                          reciprocal=a.reciprocal,location_hi=a.location_hi,weighted=a.weighted)
              for k in range(a.pieces)]
        print("whole cell",p,min(x.lower() for x in vals).str(14),flush=True)
