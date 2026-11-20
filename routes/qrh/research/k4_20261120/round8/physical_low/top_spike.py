"""Handle the actual multiple in a nonempty coprime top block without Fourier summation."""
from flint import arb,ctx,fmpz
from row_inputs import harmonic,PERRON,MEAN

def cover(C,table=(),P=37):
    H=arb(3000175332800);l=arb(116);x=l.exp()
    z=arb(C)*(x/H).sqrt();G=z.log()+arb("1.331")
    r=arb("1e-6");pi=arb.pi();d=(4*(-l/4).exp()).log1p()/2;c=l+d
    a=(1-arb("1e-12"))*H*d;I=pi*a.sin()/a
    # In this block (d,e)=1 and z/2<d,e<=z on both axes, so the only
    # candidate multiple inside the entire near region is de itself.
    low=(c-r).exp();hi=(c+r).exp()
    assert z*z/2>hi and z*z/4<hi
    A=(z/2).max(low/z);B=z.min(2*hi/z)
    assert B>A and A>1
    harmonic_row=(B/A).log()+arb("2.44")*(1/B.sqrt()+1/A.sqrt())
    # Characteristic at small primes has mean 1 and product discrepancy.
    slack=constant=arb(1)
    for p in range(2,1001):
        if not fmpz(p).is_prime():continue
        if p<=P:slack*=2*arb(p)/(p-1)
        else:constant*=1+arb(1)/(p*(p-1))
    constant*=(arb(1)/1000).exp()
    slack*=(1+z.log())**2
    # For all top-row terms divide by the constant lower bound G.
    # The quantity correcting y/[d,e] uses the genuine signed whole-top moment.
    signed=harmonic("116",C,0,table)[0]
    total_area=(1-a/pi)*I
    summed_peaks=a.sin()/a+(1+a.cos())/12
    unit=(c+r)*(r/2).exp()/I
    main=unit*r.exp()*total_area*(constant*harmonic_row/G**2+signed)
    error=unit*H*(-c).exp()*summed_peaks*slack*B*harmonic_row/G**2
    return main+error,main,error

if __name__=="__main__":
    import argparse
    ctx.prec=160;ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--ratio",type=int,default=3000000)
    ap.add_argument("--mean",action="store_true");ap.add_argument("--upper")
    a=ap.parse_args()
    values=cover(a.ratio,MEAN if a.mean else ())
    print("all-frequency top including actual multiples",*(v.str(13) for v in values))
    if a.upper:assert values[0]<arb(a.upper)
