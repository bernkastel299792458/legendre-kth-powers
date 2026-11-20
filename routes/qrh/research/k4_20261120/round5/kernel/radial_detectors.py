"""Certified radial constants for fixed simple- and triple-root detectors."""

from functools import lru_cache
from math import comb
from flint import arb,ctx


# Integer coefficients of z^3,...,z^8 with denominator 10^6. Choose z^2 by
# the exact equation P(-1)=0. Every polynomial has constant 1 and no z term.
NUMS=(
    (77725,-130843,-17639,-1504,1678,348),
    (103752,-159491,-25796,-5157,1936,562),
    (121592,-180776,-30277,-8602,1405,452),
    (154437,-176356,-37109,-14335,1763,1034),
)
DEN=10**6
LOW,HIGH=280,356


def polynomials():
    for words in NUMS:
        w=[DEN,0,0]+list(words)
        w[2]=-sum(((-1)**k)*v for k,v in enumerate(w))
        assert sum(((-1)**k)*v for k,v in enumerate(w))==0
        yield 1,[arb(j)/DEN for j in w]
    # Coefficients of z^5,...,z^15 in units 10^-9. Reconstruct Q from
    # its top down, then set Q(0)=1,Q'(0)=-3 and P=(1+z)^3 Q exactly.
    rows=(
        (-1645429381,-362262463,142549329,-58701038,135866979,-16232461,459504,-2790536,1919657,820013,158103),
        (-1757409715,-293718142,133523964,-49409418,155212049,-26835869,3376324,-1714613,3880101,1371543,255746),
        (-1814783165,-305887036,109095804,-47591195,159911770,-35804567,564750,-3459641,3612178,1198490,236462),
        (-1830244833,-344749928,7156770,-73748632,183939451,-27172173,3338573,-6318180,3663954,1527079,353143),
        (-1736549487,-249401293,-3560424,-115745652,142398014,-55913197,1623738,-2416604,7004101,2374432,471956),
    )
    unit=10**9
    for row in rows:
        q=[unit,-3*unit]+[0]*11
        for j in range(15,4,-1):
            q[j-3]=row[j-5]-sum(comb(3,k)*q[j-k] for k in range(3) if j-k<len(q))
        w=[sum(comb(3,k)*q[j-k] for k in range(4) if 0<=j-k<len(q)) for j in range(16)]
        assert w[:2]==[unit,0] and tuple(w[5:])==row
        yield 3,[arb(j)/unit for j in w]


@lru_cache(maxsize=2)
def caps(precision):
    assert precision==ctx.prec
    div=256
    exps=[arb(k)/200 for k in range(LOW,HIGH+1)]
    rmin,rmax=arb(1)/16,arb(16)
    step=arb(2).log()/32
    powers=[(1+(v*step)**2*(v*step).exp()/8) for v in exps]
    tables=[]
    for multiplicity,coef in polynomials():
        degrees=len(coef)-1
        cosines=[[2*(arb(j*k)*arb.pi()/div).cos() for k in range(1,degrees+1)]
                 for j in range(div+1)]
        assert degrees<=9*multiplicity
        assert all(abs(v)<=comb(degrees,k) for k,v in enumerate(coef))
        small=sum(abs(coef[k])*rmin**(k-2) for k in range(2,degrees+1))
        right=sum(abs(coef[k])*arb(4)**(2-k) for k in range(2,degrees+1))
        assert right/16<arb(1)/2 and right/(1-right/16)<2*multiplicity
        large=sum(abs(v)*rmax**k for k,v in enumerate(coef)).log()
        assert exps[0]*large>degrees
        vals=[arb(0) for v in exps]
        for m in range(257):
            lograd=step*(m-128)
            a=[v*(k*lograd).exp() for k,v in enumerate(coef)]
            h=[sum(a[k]*a[k+j] for k in range(degrees+1-j)) for j in range(degrees+1)]
            angular=(arb.pi()/div)**2*sum(j*j*abs(h[j]) for j in range(1,degrees+1))/4
            peak=arb(0)
            for xx in cosines:
                peak=peak.max(h[0]+sum(z*t for z,t in zip(h[1:],xx,strict=True)))
            logcap=(peak+angular).log()/2
            for j,v in enumerate(exps):
                vals[j]=vals[j].max(logcap*(-v*lograd).exp())
        for j,v in enumerate(exps):
            vals[j]=(vals[j]*powers[j]).max(small*rmin**(2-v)).max(large/rmax**v)
        tables.append([z/multiplicity for z in vals])
    return tables


def bound(lo,hi):
    if not (lo>=arb(LOW)/200 and hi<=arb(HIGH)/200):
        return None
    j=max(LOW,int((lo*200).lower().floor().unique_fmpz()))
    k=min(HIGH,int((hi*200).upper().ceil().unique_fmpz()))
    out=None
    for row in caps(ctx.prec):
        c=row[j-LOW].max(row[k-LOW])
        out=c if out is None else out.min(c)
    return out


if __name__=="__main__":
    ctx.prec=160
    for s in ("1.55","1.65","1.72","1.75"):
        print(s,bound(arb(s),arb(s)).str(14),flush=True)
