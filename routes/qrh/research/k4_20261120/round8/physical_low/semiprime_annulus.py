"""Resum every contributing semiprime modulus in X/end < q <= X/23, or in a subband."""
import argparse
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from compact_spline import run as spline
from odd_sieve import denominator,parameters

def run(cut,end,cells,fejer=False):
    C=1732099;Q=210;eta=arb(48)/Q;z,c,r,I,A,S,u=constants(C);x=arb(116).exp();h=arb(H)
    X=(c+2*r).exp();xl=(c-2*r).exp();pmin=xl/(end*z);gmin=denominator(z,Q)
    density,shift,err=parameters(Q,ctx.prec)
    gmax=eta*(z.log()+arb("1.332583")+shift)+err/z.sqrt().sqrt()
    assert end<=100000 and end>cut>=23 and pmin>1000 and z<arb("2.169e25") and X/end>z
    assert z*z<xl and xl/(cut-1)>X/cut
    pref=u*h*(-c).exp();w=arb(".0002");area=X/h*A+2*w*x/h*S
    amin=(c-r).exp()/h*(A-4/(h*r*(1-((1-arb("1e-12"))*(c-116)/r)**2)))
    coeff=[arb(0)]
    for j in range(1,end+2):
        val=arb(int(fmpz(j).moebius_mu())**2)/int(fmpz(j).euler_phi()) if gcd(j,Q)==1 else 0
        coeff.append(coeff[-1]+val)
    def gs(val,up):
        j=int((val.upper() if up else val.lower()).floor().unique_fmpz())
        return coeff[j]
    def bounds(lo,hi):
        if hi<=lo:return arb(0),arb(0),arb(0)
        assert hi>lo
        E=hi.sqrt()*hi.log()**2/(8*arb.pi())
        d=(hi/lo).log()
        return (d+2*E/lo)/lo.log(),(hi-lo+2*E)/lo.log(),((d-2*E/lo)/hi.log()).max(arb(0))
    rho=(pmin/(pmin-1))**2
    # End at z exactly. The lower edge is below every physical outer prime in the selected k's.
    logcap=arb(end).log();edges=[z*(-logcap*j/cells).exp() for j in range(cells+1)]
    if fejer:
        from fejer_primes import envelope,energy
        assert pmin>arb("40.1").exp()
        major=envelope()*c.exp()/h
        @lru_cache(None)
        def erow(j,k):
            left=(arb(j)/20).exp()
            return energy(left,left*(arb(k)/1024).exp())[0]
        def normrow(a,b):
            j=int((20*a.log()).lower().floor().unique_fmpz())
            k=int((1024*(b/a).log()).upper().ceil().unique_fmpz())
            return erow(j,max(1,k))
    phys=arb(0)
    for k in range(cut,end):
        if gcd(k,Q)>1:continue
        assert xl/k>X/end
        for j in range(cells):
            lo=edges[j+1].max(xl/(k*z));hi=edges[j]
            if hi<lo:continue
            H0,N,_=bounds(lo,hi)
            V=area*H0/(S*k*N);assert V>100
            # Tangent to 2V/log V for V>=exp(2); its intercept dominates all smaller intervals.
            assert 2*V/V.log()**2>10
            factor=gs(z/lo,True)*gs(z*k*hi/xl,True)
            raw=2*area*H0/(k*V.log())
            if fejer:
                rl=xl/(k*hi);rh=z.min(X/(k*lo))
                spec=major/k*normrow(lo,hi)*normrow(rl,rh)
                raw=raw.min(spec)
            phys+=factor*raw
    phys*=pref*rho/gmin**2
    # A positive lower bound for the subtracted mean plus the low Ramanujan modes.
    correction=arb(0)
    for i in range(cells):
        lp,hp=edges[i+1],edges[i];_,_,hp0=bounds(lp,hp)
        for j in range(cells):
            lr=edges[j+1].max(X/(end*lp))
            hr=edges[j].min(X/(cut*hp))
            if hr<=lr:continue
            assert hr>lr
            _,_,hr0=bounds(lr,hr)
            top=int((Q*hp*hr/X).upper().floor().unique_fmpz())
            mul=eta
            for n in range(1,top+1):
                d=gcd(n,Q);cq=int(fmpz(Q//d).moebius_mu())*int(fmpz(d).euler_phi())
                t=(2*arb.pi()*n*xl/(Q*hp*hr)).union(2*arb.pi()*n*X/(Q*lp*lr))
                v=(cq*t.cos()).lower()
                if not (n*X<=Q*lp*lr):v=v.min(arb(0))
                mul+=2*v/Q
            assert mul>0
            correction+=gs(z/hp,False)*gs(z/hr,False)*hp0*hr0*mul
    # Remove p=r once, globally, with a uniform upper on the local correction factor.
    correction-=coeff[end]**2*(eta+1)/(pmin-1)
    assert correction>0
    subtract=pref*amin*correction/gmax**2
    high=spline(C,Q,23,".0002",4*10**18,64)[3]
    return phys,subtract,phys-subtract+high

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--cut",type=int,default=23)
    ap.add_argument("--end",type=int,default=121);ap.add_argument("--cells",type=int,default=64)
    ap.add_argument("--upper");ap.add_argument("--fejer",action="store_true");a=ap.parse_args();ctx.prec=160
    v=run(a.cut,a.end,a.cells,a.fejer)
    print("semiprimes X/end < q <= X/cut",a.end,a.cut,"all actual upper; mean plus low lower; middle upper",*(q.str(15) for q in v))
    if a.upper:assert v[-1]<arb(a.upper)
