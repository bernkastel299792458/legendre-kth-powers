"""The next conditional coordinate in the radical variance of the detector."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from inner_jordan import responses,response


@lru_cache(None)
def saving(width,prec):
    assert prec==ctx.prec
    W=arb(width);step=32
    primes=[p for p in range(13,48) if fmpz(p).is_prime()]
    by_e=[]
    for start in range(40,100,5):
        elo,ehi=arb(start)/1000,arb(start+5)/1000
        v=1+elo.union(ehi)
        vals=responses(start,start+5,prec)
        density=arb(480)/2310
        total=arb(0)
        for iq,q in enumerate(primes):
            density*=1-arb(1)/q
            lq=arb(q).log()
            for p in primes[:iq]:
                lp=arb(p).log();rho=arb(p)**(-v)
                probability=(1-arb(p)**(-1-elo))*(1-arb(q)**(-1-elo))*arb(q)**(-1-ehi)
                for k in range(16*step):
                    a,b=arb(k)/step,arb(k+1)/step
                    count=density/(p*q)*(1-(a-b).exp())-2**(6+iq)*(a-W-30).exp()
                    if not count>0:continue
                    t=(a+b)/2;acc=arb(0);weight=arb(1)
                    while t>0:
                        acc+=weight*(response(t,vals)-response(t-lq,vals)
                                    -response(t-W,vals)+response(t-W-lq,vals))
                        weight*=rho;t-=lp
                    lip=2*(1+b)/(1-arb(p)**(-1-elo))
                    lower=abs(acc)-lip/(2*step)
                    if lower>0:
                        total+=count*probability*((elo if a>=W else ehi)*(a-W)).exp()*(lower/W)**2
        by_e.append(total.lower())
    return min(by_e)


if __name__=="__main__":
    ctx.prec=160
    for w in ("8.5","9","9.5","10"):
        value=saving(w,ctx.prec)
        assert value>0
        print(w,value.str(14),flush=True)
