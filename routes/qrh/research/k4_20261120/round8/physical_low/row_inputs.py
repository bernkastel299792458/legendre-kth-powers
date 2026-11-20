"""Feed a positive set of real Mertens bounds to all rows of the coprime top block."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from top_signed import top

PERRON=((43,".00007351"),(47,".00001869"),(48,".00001279"),(49,".000008949"),
        (50,".000006452"),(51,".000004828"),(52,".000003228"),(53,".000002185"),
        (54,".000001507"),(55,".000001066"),(56,".0000007783"),
        (57,".0000005497"),(58,".0000003691"))

MEAN=tuple(zip(range(38,60),(
    ".00001460",".000009635",".000006441",".000004512",".000002938",".000001924",
    ".000001272",".0000008506",".0000005953",".0000003877",".0000002540",
    ".0000001680",".0000001125",".00000007676",".00000005209",".00000003414",
    ".00000002257",".00000001512",".00000001033",".000000006755",".000000004430",
    ".000000002932")))


@lru_cache(None)
def norm(s100,p100,prec):
    assert prec==ctx.prec and s100>0 and p100>100
    s=arb(s100)/100;power=arb(p100)/100;q=2000
    C=arb(1);P=arb(1)
    for p in range(2,q+1):
        if not fmpz(p).is_prime():continue
        x=arb(p);b=x**(-s)
        C*=1+1/((x-1)*(x**s-1))
        rr=1/(1-b+b/(x-1))
        P*=1+(x/(x-1)*rr)**2*x**(-power)
    const=1/((1-arb(1)/q)*(1-arb(q)**(-s)))
    C*=(const*arb(q)**(-s)/s).exp()
    P*=(const**2*arb(q)**(1-power)/(power-1)).exp()
    return C*P.sqrt()


def bound(z,table=()):
    assert z.log()<66
    # RZA applies above 10^16, while Hurst covers the remaining range.
    minlog=16*arb(10).log()
    def classic(t):return arb(".006688")/t
    rows=[(minlog,classic(minlog))]+[(arb(j),classic(arb(j))) for j in range(37,67)]
    for i,(level,cost) in enumerate(rows):
        for start,new in table:
            if level>=start:cost=cost.min(arb(new))
        rows[i]=level,cost
    V=rows[-1][1]*norm(100,200,ctx.prec)
    for k in range(1,len(rows)):
        level,upper=rows[k];delta=rows[k-1][1]-upper
        assert not delta<0
        if delta.is_zero():continue
        base=2*level.exp()/z
        cap=norm(100,200,ctx.prec)
        for a in (10,20,25,30,33,35,37,39,41,43,45,47):
            cap=cap.min(base**(arb(a)/100)*norm(100-a,200-2*a,ctx.prec))
        V+=delta.max(arb(0))*cap
    # All h above the old cutoff are now included. For small Y, use |M(Y)|≤sqrt(Y).
    tail=None
    for a in (5,8,10,12,15,20):
        val=(2/z*z**(arb(a)/100)).sqrt()*norm(50,100+a,ctx.prec)
        tail=val if tail is None else tail.min(val)
    return V+tail


def harmonic(L,C,n,table=(),r=1):
    h=arb(3000175332800);z=arb(C)*(arb(L).exp()/h).sqrt()
    V=bound(z,table)
    k=arb(n)*h/arb(C)**2*arb(".000002").exp()
    br=arb(3)/2 if r==0 else 2+arb(2).log()
    G=z.log()+arb("1.331")
    assert arb("1.33258")-arb("2.44")/z.sqrt()>arb("1.331")
    return (V*br*(1+3*arb.pi()*k)/G)**2,V


if __name__=="__main__":
    ctx.prec=160
    import argparse
    cli=argparse.ArgumentParser()
    cli.add_argument("--mean",action="store_true")
    args=cli.parse_args()
    for C in (3000000,4000000,10000000):
        for table in (((),PERRON,MEAN) if args.mean else ((),PERRON)):
            z=arb(C)*(arb(116).exp()/3000175332800).sqrt()
            vals=[harmonic("116",C,n,table)[0] for n in (0,1,2,4,8)]
            print(C,("mean" if table==MEAN else "Perron") if table else "published","V",bound(z,table).str(12),
                  "n=0,1,2,4,8:",*(v.str(10) for v in vals),flush=True)
