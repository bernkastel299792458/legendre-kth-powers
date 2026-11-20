"""All remaining semiprimes up to an independent small-modulus cutoff."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from compact_spline import run as spline
from odd_sieve import denominator,parameters

def run(logend,width):
    z,c,r,I,A,S,u=constants(1732099);Q=210;eta=arb(48)/Q;x=arb(116).exp()
    Y=arb("70.7").exp();Z=arb(logend).exp();xmin=Y/z
    assert Y<Z and xmin>599 and z<arb("2.169e25") and Z*Q<(c-2*r).exp()
    G=denominator(z,Q);density,shift,err=parameters(Q,ctx.prec)
    disc0=arb(0);disc1=arb(0);count=0
    for n in range(Q):
        if n and gcd(n,Q)==1:count+=1
        disc0=disc0.min(count-eta*(n+1));disc1=disc1.max(count-eta*n)
    discrepancy=disc1-disc0
    table=[arb(0)]
    for j in range(1,4097):
        part=arb(int(fmpz(j).moebius_mu())**2)/int(fmpz(j).euler_phi()) if gcd(j,Q)==1 else 0
        table.append(table[-1]+part)
    def weight(p):
        t=z/p
        if t<4096:return p/(p-1)*table[int(t.upper().floor().unique_fmpz())]/G
        val=eta*(t.log()+arb("1.332583")+shift)+err/t.sqrt().sqrt()
        return (p/(p-1)*val/G).min(arb(1))
    def countlim(l,r):
        return 1+((r-l).max(arb(0))+r.sqrt()*r.log()**2/(4*arb.pi()))/l.log()
    m=int(((z/xmin).log()/arb(width)).ceil().unique_fmpz())
    cuts=[z*((xmin/z).log()*i/m).exp() for i in range(m+1)];mass=arb(0)
    active=[(cuts[i+1],cuts[i],weight(cuts[i+1])) for i in range(m)]
    for i,(lo,hi,v) in enumerate(active):
        for j in range(i+1):
            a,b,w=active[j]
            if lo*a>Z or hi*b<Y:continue
            p0=lo.max(Y/b);p1=hi.min(Z/a)
            s0=a.max(Y/hi);s1=b.min(Z/lo)
            if p1<p0 or s1<s0:continue

            mass+=(1 if i==j else 2)*v*w*countlim(p0,p1)*countlim(s0,s1)
    pref=u*arb(H)*(-c).exp()
    high=spline(1732099,Q,23,".0002",4*10**18,64)[3]
    return discrepancy,pref*S*discrepancy*mass+high
if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--logend",default="82");ap.add_argument("--width",default=".1");ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=160
    d,v=run(a.logend,a.width)
    print("CRT discrepancy",d.str(13),"semiprime middle upper for logs (70.7,",a.logend,"]",v.str(13))
    if a.upper:assert v<arb(a.upper)
