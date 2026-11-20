"""All three-prime moduli, no unpriced smallest prime or ratio restriction."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from odd_sieve import denominator
from compact_spline import run as spline

def run(m,cells,cut=23):
    Q=210;eta=arb(48)/Q;z,c,r,I,A,S,u=constants(1732099);h=arb(H);x=arb(116).exp()
    X=(c+2*r).exp();xl=(c-2*r).exp();pref=u*h*(-c).exp();area=X/h*A+2*arb(".0002")*x/h*S
    G=denominator(z,Q);assert z<X/m and 23<=cut<m<100000 and X/(m*z)>599
    # The combined mean and low phases are positive on q<=X/23.
    signed=[0]+[int(fmpz(Q//gcd(i,Q)).moebius_mu())*int(fmpz(gcd(i,Q)).euler_phi()) for i in range(1,10)]
    tab=[arb(0)]
    for j in range(1,m+2):
        w=arb(int(fmpz(j).moebius_mu())**2)/int(fmpz(j).euler_phi()) if gcd(j,Q)==1 else 0
        tab.append(tab[-1]+w)
    def gcap(a):return tab[int((z/a).upper().floor().unique_fmpz())]
    L=(arb(m)).log();edges=[z*(-L*i/cells).exp() for i in range(cells+1)]
    # Group the least prime by integer dyads below 2^16, then by multiplicative cells.
    groups=[]
    for i in range(3,16):
        den=sum((arb(1)/(p-1) for p in range(2**i,2**(i+1)) if gcd(p,Q)==1 and fmpz(p).is_prime()),arb(0))
        groups.append((arb(2**i-1),arb(2**(i+1)-1),den))
    def harm(a,b):
        if b<a:return arb(0)
        error=b.sqrt()*b.log()**2/(8*arb.pi())
        return ((b/a).log().max(arb(0))+2*error/a)/a.log()+1/a
    p=arb(65535)
    while p<z.sqrt():
        b=p*2
        groups.append((p,b,p/(p-1)*harm(p,b)))
        p=b
    @lru_cache(None)
    def two(i):
        a,b=edges[i+1],edges[i]
        val=arb(0)
        for p0,p1,den in groups:
            if p0>b.sqrt():break
            p1=p1.min(b.sqrt())
            # a/p <= s <= b/p. The log span is the same for every fixed p.
            s0=a/p1;rel=(p1*b).sqrt()/a*(b/p0).log()**2/(4*arb.pi())
            assert s0>599 and b/p0<arb("2.169e25")
            cap=s0/(s0-1)*(((b/a).log()+rel)/s0.log()+1/s0)
            val+=den*cap
        return val
    total=arb(0)
    # Each projected semiprime row is used whole, but confine the single prime
    # to its intersection with the two q-boundaries.
    for i in range(cells):
        l0,h0=edges[i+1],edges[i]
        for j in range(cells):
            p0=edges[j+1].max(X/(m*h0));p1=edges[j].min(X/(cut*l0))
            if p1<p0:continue
            hc=harm(p0,p1)*p0/(p0-1)
            if hc.is_zero():continue
            top=min(9,int((Q*h0*p1/X).upper().floor().unique_fmpz()))
            cg=eta
            for n in range(1,top+1):
                ang=(2*arb.pi()*n*xl/(Q*h0*p1)).union(2*arb.pi()*n*X/(Q*l0*p0))
                val=(signed[n]*ang.cos()).upper()
                if not n*X<=Q*l0*p0:val=val.max(arb(0))
                cg+=2*val/Q
            total+=two(i)*gcap(l0)*hc*gcap(p0)*cg
    high=spline(1732099,Q,23,".0002",4*10**18,64)[3]
    return 2*pref*area/G**2*total+high

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--end",type=int,default=400);ap.add_argument("--cells",type=int,default=96)
    ap.add_argument("--cut",type=int,default=23);ap.add_argument("--upper");a=ap.parse_args();ctx.prec=144
    v=run(a.end,a.cells,a.cut)
    print("all triprimes in X/",a.end,"< q <= X/",a.cut,"signed upper",v.str(15))
    if a.upper:assert v<arb(a.upper)
