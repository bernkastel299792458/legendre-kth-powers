"""Lower the high-frequency Gram charge on actual two- and three-prime coefficients."""
from functools import lru_cache

import numpy as np
from numba import njit
from flint import arb,ctx
from prime_slope import gram_bounds


TICKS=3200


def exact_ticks(value):
    n=(value*TICKS).unique_fmpz()
    assert n is not None and (value*TICKS-int(n)).is_zero()
    return int(n)


@lru_cache(None)
def prime_cells(e_top,step,precision):
    assert ctx.prec==precision and TICKS%step==0
    # e_top represents an outward upper bound on 2*delta/U in 1e-9 ticks.
    e=arb(e_top)/10**9
    lo=7*TICKS;hi=56*TICKS
    assert arb(7).exp()>599 and arb(56).exp()<arb("2.169e25")
    rows=[]
    for i in range(lo,hi,step):
        a,b=arb(i)/TICKS,arb(i+step)/TICKS
        mass=(b.exp()-a.exp()-(a*a*(a/2).exp()+b*b*(b/2).exp())/(8*arb.pi()))
        s=mass.max(arb(0))*(-(1+e)*b).exp()/b
        cap=(-(1+e)*a).exp()
        # Elementary symmetric sums of 1, 2, 3 distinct primes in this cell.
        double=s*(s-cap).max(arb(0))/2
        triple=double*(s-2*cap).max(arb(0))/3
        rows.append([max(0.,float(v.lower())*(1-2**-48)) for v in (s,double,triple)])
    return np.asarray(rows)


@njit
def spectrum(rows,step,ymin,ymax,width):
    n=len(rows)
    first=7*TICKS
    offset=first//step
    assert first%step==0
    spec=np.zeros(3*(n+offset)+1)
    low=np.empty(len(spec),np.int64)
    high=np.empty_like(low)
    # The possible upper argument is separately shifted once for each prime.
    for j in range(len(low)):
        low[j]=min(width,max(0,ymin+width-j*step))
        high[j]=min(width,max(0,ymax+width-j*step))
    for i in range(n):
        a=offset+i
        for j in range(i,n):
            b=offset+j
            s=a+b
            lower=width-high[a]-high[b]+low[s+2]
            upper=width-low[a+1]-low[b+1]+high[s]
            amp=max(0,lower,-upper)/width
            pair=rows[i,1] if i==j else rows[i,0]*rows[j,0]
            spec[s]+=pair*amp*amp
            for k in range(j,n):
                c=offset+k
                lower3=lower-high[c]+low[a+c+2]+low[b+c+2]-high[s+c]
                upper3=upper-low[c+1]+high[a+c]+high[b+c]-low[s+c+3]
                amp=max(0,lower3,-upper3)/width
                if k>j:
                    mass=pair*rows[k,0]
                elif i<j:
                    mass=rows[i,0]*rows[j,1]
                else:
                    mass=rows[i,2]
                spec[s+c]+=mass*amp*amp
    return spec


@lru_cache(maxsize=80)
def coefficient_tail(e_top,step,ymin,ymax,width,precision):
    rows=prime_cells(e_top,step,precision)
    spec=spectrum(rows,step,ymin,ymax,width)
    assert len(rows)<=256
    # At most binomial(258,3)+binomial(257,2) nonnegative terms, followed
    # by fewer than 900 reverse additions. Retain a directed safety margin.
    return np.cumsum(spec[::-1])[::-1]*(1-2.e-8)


def saving(U,V,delta,W,lh,cutoff,q=2310,step=800):
    assert q==2310 and 0<delta and U>=30 and U<=V and step in (800,1600,3200)
    eps=(arb("1.01")*U.exp())**(-arb(1)/5)
    corr=((1+eps)*eps*(2*eps**3).exp()).exp()/(1-4*eps/arb.pi())
    scale=q*arb("1.01")*arb("1.03")*(1+eps)*(eps**3).exp()/arb.pi()
    j=int((scale/cutoff).upper().floor().unique_fmpz())+1
    _,outer=gram_bounds(q,max(32,j))
    e_top=int((2*delta/U*10**9).upper().ceil().unique_fmpz())
    ymin=int(((U+lh)*TICKS).lower().floor().unique_fmpz())
    ymax=int(((V+lh)*TICKS).upper().ceil().unique_fmpz())
    vals=coefficient_tail(e_top,step,ymin,ymax,exact_ticks(W),ctx.prec)
    last=arb(outer[j])/10**6
    credit=arb(0)
    for i in range(j-1,0,-1):
        nxt=last.min(arb(outer[i])/10**6)
        z=(scale/i+arb(".01")).max(arb(cutoff))
        index=int(((V+z.log())*TICKS/step).upper().ceil().unique_fmpz())
        assert 0<=index<len(vals) and scale/z<i
        credit+=(last-nxt)*arb(float(vals[index]))
        last=nxt
    good=1-2*arb("1.03")**(-2048)
    return good*corr*arb.pi()*credit/(q*V)


if __name__=="__main__":
    ctx.prec=160
    for u in (34,37,40):
        U=arb(u);V=U+arb(1)/16
        val=saving(U,V,arb("1.16"),arb(9),arb(-3),320)
        assert val>0
        print("composite Gram deduction",u,val.str(15),flush=True)
