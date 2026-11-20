"""True signed middle for three-prime moduli with one prescribed small prime."""
import argparse
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from odd_sieve import denominator
from compact_spline import run as spline

def run(m,ells,cells):
    C=1732099;Q=210;z,c,r,I,A,S,u=constants(C);X=(c+2*r).exp();xl=(c-2*r).exp()
    eta=arb(48)/Q;K=arb(H);pref=u*K*(-c).exp();delta=arb(".0002")*arb(116).exp()/K
    area=X/K*A+2*delta*S;G=denominator(z,Q);lmax=max(ells)
    assert all(fmpz(p).is_prime() and gcd(p,Q)==1 for p in ells) and len(ells)==len(set(ells))
    assert X/(m*lmax)>z and X/(m*lmax*z)>lmax and m<100000
    amps=[0]+[int(fmpz(Q//gcd(n,Q)).moebius_mu())*int(fmpz(gcd(n,Q)).euler_phi()) for n in range(1,10)]
    def harmonic(l,h):
        if h<l:return arb(0)
        e=h.sqrt()*h.log()**2/(8*arb.pi())
        return ((h/l).log().max(arb(0))+2*e/l)/l.log()+1/l
    total=arb(0)
    for ell in ells:
        # Arguments of a_p G_Q sums do not exceed m*ell.
        Gs=[arb(0)];Ge=[arb(0)]
        for n in range(1,m*ell+2):
            val=arb(int(fmpz(n).moebius_mu())**2)/int(fmpz(n).euler_phi()) if gcd(n,Q)==1 else 0
            Gs.append(Gs[-1]+val);Ge.append(Ge[-1]+(val if n%ell else 0))
        def weights(p):
            v=z/p
            i=int(v.upper().floor().unique_fmpz());j=int((v/ell).upper().floor().unique_fmpz())
            rp=p/(p-1)
            return rp*Gs[i],rp*arb(ell)/(ell-1)*Ge[j]
        ls=(arb(m)*ell).log()
        pts=[z*(-ls*i/cells).exp() for i in range(cells+1)]
        for i in range(cells):
            l,h=pts[i+1],pts[i]
            for j in range(i+1):
                l2,h2=pts[j+1],pts[j]
                ll=l.max(X/(m*ell*h2));hh=h.min(X/(23*ell*l2))
                ll2=l2.max(X/(m*ell*h));hh2=h2.min(X/(23*ell*l))
                if hh<ll or hh2<ll2:continue
                ap,at=weights(ll);bp,bt=weights(ll2)
                ap=ap.max(at)
                bp=bp.max(bt)
                # Monotone in all four weights on the cone at<=ap, bt<=bp.
                size=at*bp+ap*bt-at*bt
                if size.is_zero():continue
                cap=min(9,int((Q*ell*hh*hh2/X).upper().floor().unique_fmpz()))
                cg=eta
                for n in range(1,cap+1):
                    ang=(2*arb.pi()*n*xl/(Q*ell*hh*hh2)).union(2*arb.pi()*n*X/(Q*ell*ll*ll2))
                    t=(amps[n]*ang.cos()).upper()
                    if not n*X<=Q*ell*ll*ll2:t=t.max(arb(0))
                    cg+=2*t/Q
                total+=(1 if i==j else 2)*size*harmonic(ll,hh)*harmonic(ll2,hh2)*cg/ell
    tail=spline(C,Q,23,".0002",4*10**18,64)[3]
    return pref*area/G**2*total+tail

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--end",type=int,default=400)
    ap.add_argument("--small",type=int,nargs="+",default=[11]);ap.add_argument("--cells",type=int,default=72);ap.add_argument("--upper")
    args=ap.parse_args();ctx.prec=144;v=run(args.end,args.small,args.cells)
    print("small prime",args.small,"q from X /",args.end,"to X/23, true signed middle upper",v.str(16))
    if args.upper:assert v<arb(args.upper)
