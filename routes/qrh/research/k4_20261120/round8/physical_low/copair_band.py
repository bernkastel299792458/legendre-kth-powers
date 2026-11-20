"""Ordinary Mellin band of a complete coprime square of two Selberg rows."""
from pathlib import Path
import sys
from flint import arb,ctx,fmpz
from row_calibration import run as multiplier
from actual_split import constants
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round7"/"mobius"))
from twisted_rms import bound,PHYSICAL_HEIGHT
from odd_sieve import ratio
from bilinear import rational


def euler(s,excluded,corrected):
    # Upper Euler sum for the weighted square in the coprimality inversion.
    P=2000
    result=arb(1)
    tail=(2*s).zeta().log()
    for p in range(2,P+1):
        if not fmpz(p).is_prime():continue
        x=arb(p);r=x**(-s)
        tail+=(-r*r).log1p()
        if excluded%p==0:continue
        w=r*x/(p-1)
        if corrected:w/=1-w
        result*=1+w*w
    amp=arb(P)/(P-1)
    if corrected:amp/=1-amp*arb(P)**(-s)
    return result*(amp**2*tail).exp()


def certificate(i=58,k=55,kap=6,w=22,h0=10**9,gmax=1,full_square=False,lower_divisor=11,band=None,core=False,spectral=False):
    Q=210;z,c,r,*_=constants(1732099);A=z/lower_divisor
    s=arb(i)/100
    length=arb(PHYSICAL_HEIGHT)/8 if band is None else arb(band[1])-arb(band[0])
    es=euler(s,Q,True).sqrt()
    e1=euler(arb(1),Q,False).sqrt()
    small=tail=derivative=arb(0)
    for g in range(1,gmax+1):
        if not fmpz(g).moebius_mu() or fmpz(g).gcd(Q)!=1:continue
        B=z.min((g*(c+2*r).exp()/23).sqrt()) if full_square else 2*A
        assert B>A and A*A/g>arb("70.7").exp()
        args=dict(parts=True,annulus=True,band=band,pointwise_core=core)
        main=bound((A/g).log(),(B/g).log(),i,k,kap,w,Q,True,**args)[0]
        err=bound((A/(g*h0)).log(),(B/g).log(),i,k,kap,w,Q,True,**args)[1]
        def missing(m):
            amp=arb(1)
            for p,_ in fmpz(m).factor():
                x=arb(int(p))
                amp/=1-x/(x-1)*x**(-s)
            return amp
        total=analytic=arb(0)
        for b in range(1,lower_divisor):
            if fmpz(b).gcd(Q*g)!=1 or not fmpz(b).moebius_mu():continue
            weight=arb(1)/int(fmpz(b).euler_phi())
            total+=weight
            analytic+=weight*missing(b)
        small+=(arb(g)/int(fmpz(g).euler_phi()))**2/g*length*(missing(g)*main*es*analytic+err*e1*total)**2
        maxrho=rational(ratio(int(B.upper().ceil().unique_fmpz()),Q))
        if core:
            assert length==1
            absolute=(maxrho*total*(1+(B/g).log()))**2/g
            tail+=absolute/h0
            derivative+=absolute*((c+2*r)-(A*A/g).log())
        else:
            tail+=(1+B/A)*(maxrho*total)**2*((length+2*arb.pi())*(1+(B/g).log())/A
                                       +2*arb.pi()*B/(A*g*h0))
    if core:
        eta=arb(48)/210;sup=small+tail
        assert derivative>sup and 23*(-4*r).exp()>1
        count=0;disc=arb(0)
        for n in range(1,Q+1):
            disc=disc.max(abs(count-eta*n))
            count+=int(fmpz(n).gcd(Q)==1)
            disc=disc.max(abs(count-eta*n))
        # On the line 1, take principal value and charge the remaining half
        # of the residue after subtracting the physical inverse main term.
        pole=eta*sup*(1+(derivative/sup).log())
        raw=eta*sup/2+((eta+disc*arb(2).sqrt())*sup+pole)/arb.pi()
        zmax,cal,*_=multiplier()
        return small,tail,cal*arb.pi()/zmax*raw
    cost=multiplier(band,spectral=spectral)[1]*(small+tail)
    return small,tail,cost


if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lower-divisor",type=int,default=11)
    ap.add_argument("--gmax",type=int)
    ap.add_argument("--upper")
    ap.add_argument("--tmin")
    ap.add_argument("--tmax")
    ap.add_argument("--core",action="store_true")
    ap.add_argument("--spectral",action="store_true")
    a=ap.parse_args()
    ctx.prec=160
    rows=((a.gmax,a.upper),) if a.gmax is not None else (
        (1,".000106770"),(11,".000251405"),(23,".000668104"),(47,".001093473"),(97,".001655551"))
    assert a.lower_divisor>=2 and (a.gmax is not None or a.lower_divisor==11)
    for g,ceiling in rows:
        assert (a.tmin is None)==(a.tmax is None)
        band=None if a.tmin is None else (a.tmin,a.tmax)
        if a.core:band=(0,1)
        values=certificate(gmax=g,full_square=True,lower_divisor=a.lower_divisor,band=band,
                           core=a.core,h0=10**15 if a.core else 10**9,spectral=a.spectral)
        print(g,*(a.str(15) for a in values),flush=True)
        if ceiling:assert values[-1]<arb(ceiling)
