"""Elementary small-modulus tail from the exact oscillation of unit counting."""
from functools import lru_cache
from itertools import combinations
from math import prod
from math import gcd
import numpy as np
from flint import arb,ctx,fmpz
from actual_split import constants,H

@lru_cache(None)
def osc(Q):
    assert Q<10**9
    ps=[int(p) for p,_ in fmpz(Q).factor()];phi=int(fmpz(Q).euler_phi())
    low=high=count=0
    for start in range(0,Q,1<<18):
        end=min(start+(1<<18),Q);units=np.ones(end-start,dtype=np.int64)
        for p in ps:units[(-start)%p::p]=0
        running=np.cumsum(units,dtype=np.int64)+count
        diff=Q*running-phi*np.arange(start,end,dtype=np.int64)
        low=min(low,int(np.min(diff-Q*units)));high=max(high,int(np.max(diff)))
        count=int(running[-1])
    assert count==phi
    return high-low

@lru_cache(None)
def discrepancy(Q,prec):
    assert ctx.prec==prec
    D=arb(2**len(fmpz(Q).factor()))
    for core in (210,2310,30030,510510,9699690,223092870):
        if Q%core==0:
            extra=2**len(fmpz(Q//core).factor())
            D=D.min(arb(extra*osc(core))/core)
    return D

def harmonic(logy,Q):
    eta=arb(int(fmpz(Q).euler_phi()))/Q;ps=[int(p) for p,_ in fmpz(Q).factor()]
    assert logy>arb(Q).log()
    return eta*(logy+arb.const_euler()+sum(arb(p).log()/(p-1) for p in ps))+2**len(ps)*(-logy).exp()

def ordered_count(Q,t,prec):
    assert ctx.prec==prec
    ell=t/3
    eta=arb(int(fmpz(Q).euler_phi()))/Q
    D=arb(osc(Q))/Q if Q<10**9 else arb(2**len(fmpz(Q).factor()))
    A=65536;v=arb(A).log()
    assert ell>v
    units=[n for n in range(1,A+1) if gcd(n,Q)==1]
    harmonic=sum((1/arb(n) for n in units),arb(0))
    # Sum_{a<=A} a^-1 * [H_Q(sqrt(Y/a)) - H_Q(a-)].
    running=arb(0);head=arb(0)
    for n in units:
        a=arb(n)
        head+=(harmonic+eta*((t-a.log())/2-v)+D/A-running)/a
        running+=1/a
    edge=3*eta*(ell-v)/2+D/A
    tail=3*eta**2*(ell-v)**2/4+eta*D/A+D*edge/A
    return 6*(eta+D*(-ell).exp())*(head+tail)

def small(Q,logy,width,degree=64,ordered=False,selberg=False):
    z,c,r,I,A,S,u=constants(1732099);h=arb(H);X=(c+2*r).exp();x=arb(116).exp()
    t=arb(logy);Y=t.exp();delta=arb(width)*x/h;M=X*A/h+2*delta*S;P0=u*h*(-c).exp()
    ps=[int(p) for p,e in fmpz(Q).factor()]
    eta=arb(int(fmpz(Q).euler_phi()))/Q
    count=3*(eta+2**len(ps)*(-t/3).exp())*harmonic(2*t/3,Q)**2
    if ordered:count=count.min(ordered_count(Q,t,ctx.prec))
    if selberg:
        from small_selberg import count as genuine,layers
        for s in (4,6,8):
            if t-s>z.log():count=count.min(genuine(Q,t,s))
        if t>z.log()+6:count=count.min(layers(Q,t))
    def one(core):
        D=arb(osc(core))/core;rest=[p for p in ps if core%p]
        raw=P0*S*D*Y*count
        total=arb(0)
        for j in range(len(rest)+1):
            for sel in combinations(rest,j):
                d=prod(sel)
                smooth=2*P0*M/(core*d)*arb(degree-1).zeta()*(degree*core*d*Y/(2*arb.pi()*delta))**degree*count
                total+=smooth.min(raw)
        return total
    opts=[(core,one(core)) for core in (210,2310,30030,510510,9699690,223092870)
          if core<=Q and Q%core==0]
    return min(opts,key=lambda p:float(p[1].upper()))

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--Q",type=int,default=30030)
    ap.add_argument("--logY",default="70.7");ap.add_argument("--width",default=".0002")
    ap.add_argument("--ordered",action="store_true")
    ap.add_argument("--selberg",action="store_true")
    a=ap.parse_args();ctx.prec=144;c,v=small(a.Q,a.logY,a.width,ordered=a.ordered,selberg=a.selberg)
    print("selected wheel, exact discrepancy numerator, small-modulus cost",c,osc(c),v.str(15))
