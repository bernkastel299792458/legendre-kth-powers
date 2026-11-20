"""Positive physical cost of all semiprimes in a complete range of unit multiplier sizes."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator

def near_cost(Q=223092870,start=2500,end=20000,cells=72,slabs=32):
    assert 2500<=start<end<=1000000 and Q==223092870
    z,c,r,I,A,S,u=constants(1732099)
    K=arb(H);X=(c+2*r).exp();xl=(c-2*r).exp();C=c.exp();x=arb(116).exp()
    P0=u*K/C;area=X*A/K+2*arb(".0002")*x/K*S;den=denominator(z,Q)
    # Class characterized by w=C/q; support is enlarged on both k endpoints.
    kstart=int((arb(start)*(-2*r).exp()).lower().floor().unique_fmpz())
    kend=int((arb(end)*(2*r).exp()).upper().ceil().unique_fmpz())
    imax=int((z*z*kend/xl).upper().ceil().unique_fmpz())
    g=[1]*(imax+1);acc=arb(1)
    for n in range(2,imax+1):
        if gcd(n,Q)==1 and fmpz(n).moebius_mu():acc+=1/arb(int(fmpz(n).euler_phi()))
        g[n]=acc
    def G(y):
        n=int(y.upper().floor().unique_fmpz())
        assert 0<=n<=imax
        return g[n]
    pmin=xl/(kend*z);rho=(pmin/(pmin-1))**2
    ed=[z*(-(z/pmin).log()*n/cells).exp() for n in range(cells+1)]
    bins=[kstart-1]+[kstart+(kend-kstart)*j//slabs for j in range(1,slabs+1)]
    cost=arb(0);assert pmin>599 and z<arb("2.169e25")
    for k0,k1 in zip(bins,bins[1:]):
        kh=sum((1/arb(k) for k in range(k0+1,k1+1) if gcd(k,Q)==1),arb(0))
        if not kh>0:continue
        for lo,h in zip(ed[1:],ed[:-1]):
            l=lo.max(xl/(k1*z))
            if h<l:continue
            h=h.upper();l=l.lower()
            assert l>5000
            E=h.sqrt()*h.log()*(h.log()-2)/(8*arb.pi())
            hp=((h/l).log()+2*E/l)/l.log()+1/l
            count=(h-l+2*E)/l.log()+1
            V=area*hp/(S*k1*count)
            assert V>100 and 2*V/V.log()**2>10
            cost+=kh*G(z/l)*G(z*k1*h/xl)*2*area*hp/V.log()
    return P0*rho*cost/den**2

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--start",type=int,default=2500);ap.add_argument("--end",type=int,default=20000)
    ap.add_argument("--cells",type=int,default=72);ap.add_argument("--slabs",type=int,default=32)
    ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=144
    v=near_cost(start=a.start,end=a.end,cells=a.cells,slabs=a.slabs)
    print("all semiprime physical cost",v.str(15))
    if a.upper:assert v<arb(a.upper)
