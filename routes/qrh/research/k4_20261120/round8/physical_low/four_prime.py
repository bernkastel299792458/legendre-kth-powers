"""Full physical signed band for two specified small and two unrestricted large primes."""
from functools import lru_cache
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants,H
from compact_spline import run as spline
from odd_sieve import denominator,parameters
from fejer_primes import envelope,energy

def run(a,b,end,cells,cut=23):
    assert 23<=cut<end<=100000 and 7<a<b and fmpz(a).is_prime() and fmpz(b).is_prime()
    Q=210; m=a*b; eta=arb(48)/Q
    z,c,r,I,A,S,u=constants(1732099); K=arb(H); x=arb(116).exp(); X=(c+2*r).exp();xl=(c-2*r).exp()
    pmin=xl/(m*end*z); assert pmin>arb("40.1").exp() and X/(m*end)>z and pmin>m*end+1
    pref=u*K*(-c).exp(); area=X*A/K+2*arb(".0002")*x*S/K; major=envelope()*c.exp()/K
    amin=(c-r).exp()/K*(A-4/(K*r*(1-((1-arb("1e-12"))*(c-116)/r)**2)))
    glow=denominator(z,Q);_,shift,err=parameters(Q,ctx.prec)
    gup=eta*(z.log()+arb("1.332583")+shift)+err/z.sqrt().sqrt()
    divs=[1,a,b,m];tab={d:[arb(0)] for d in divs}
    for j in range(1,m*end+2):
        g=arb(int(fmpz(j).moebius_mu())**2)/int(fmpz(j).euler_phi()) if gcd(j,Q)==1 else arb(0)
        for d in divs:
            if j*d>m*end+1:break
            tab[d].append(tab[d][-1]+(g if gcd(j,d)==1 else 0))
    def row(p,upper):
        arg=z/p;out=[]
        for d in divs:
            v=arg/d;j=int((v.upper() if upper else v.lower()).floor().unique_fmpz())
            out.append(arb(d)/int(fmpz(d).euler_phi())*tab[d][j])
        return out
    def coeff(uhi,vhi,ulo,vlo):
        u0,ua,ub,uc=uhi;v0,va,vb,vc=vhi
        return u0*vc+uc*v0+ua*vb+ub*va+uc*vc-ulo[3]*(vlo[1]+vlo[2])-(ulo[1]+ulo[2])*vlo[3]
    def bounds(l,h):
        E=h.sqrt()*h.log()**2/(8*arb.pi())
        d=(h/l).log()
        return (d+2*E/l)/l.log(),(h-l+2*E)/l.log(),((d-2*E/l)/h.log()).max(arb(0))
    @lru_cache(None)
    def erow(j,k):
        l=(arb(j)/20).exp()
        return energy(l,l*(arb(k)/1024).exp())[0]
    def norm(l,h):
        j=int((20*l.log()).lower().floor().unique_fmpz())
        k=int((1024*(h/l).log()).upper().ceil().unique_fmpz())
        return erow(j,max(k,1))
    pts=[z*(-arb(m*end).log()*i/cells).exp() for i in range(cells+1)]
    phys=arb(0)
    for k in range(cut,end):
        if gcd(k,Q)!=1:continue
        for i in range(cells):
            l=pts[i+1].max(xl/(k*m*z));h=pts[i]
            if h<=l:continue
            rl=xl/(m*k*h);rh=z.min(X/(m*k*l))
            if rh<=rl:continue
            mass=coeff(row(l,True),row(rl,True),row(h,False),row(rh,False)).max(arb(0))
            if mass.is_zero():continue
            hp,np,_=bounds(l,h);v=area*hp/(S*m*k*np);assert v>100 and 2*v/v.log()**2>10
            raw=(2*area*hp/(k*m*v.log())).min(major/(k*m)*norm(l,h)*norm(rl,rh))
            phys+=mass*raw
    phys*=pref*(pmin/(pmin-1))**2/glow**2
    sub=arb(0)
    amps=[0]+[int(fmpz(Q//gcd(n,Q)).moebius_mu())*int(fmpz(gcd(n,Q)).euler_phi()) for n in range(1,10)]
    for i in range(cells):
        l,h=pts[i+1],pts[i];_,_,hp=bounds(l,h)
        for j in range(cells):
            rl=pts[j+1].max(X/(m*end*l));rh=pts[j].min(X/(m*cut*h))
            if rh<=rl:continue
            _,_,hr=bounds(rl,rh)
            low=coeff(row(h,False),row(rh,False),row(l,True),row(rl,True)).max(arb(0))
            if low.is_zero():continue
            cap=min(9,int((Q*m*h*rh/X).upper().floor().unique_fmpz()));cg=eta
            for n in range(1,cap+1):
                ang=(2*arb.pi()*n*xl/(Q*m*h*rh)).union(2*arb.pi()*n*X/(Q*m*l*rl))
                val=(amps[n]*ang.cos()).lower()
                if not n*X<=Q*m*l*rl:val=val.min(arb(0))
                cg+=2*val/Q
            assert cg>0
            sub+=hp*hr*low*cg
    # Exclude the artificially retained p=r diagonal from the lower correction.
    sub-=5*(arb(m)/int(fmpz(m).euler_phi())*tab[1][-1])**2*(eta+1)/(pmin-1)
    sub=pref*amin*sub.max(arb(0))/(m*gup**2)
    high=spline(1732099,Q,23,".0002",4*10**18,64)[3]
    return phys,sub,phys-sub+high

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--small",type=int,nargs=2,default=(11,13))
    ap.add_argument("--end",type=int,default=400);ap.add_argument("--cells",type=int,default=72);ap.add_argument("--upper")
    args=ap.parse_args();ctx.prec=144;v=run(*args.small,args.end,args.cells)
    print("fixed small pair",args.small,"X/",args.end,"<q<=X/23 physical, correction, signed upper",*(s.str(14) for s in v))
    if args.upper:assert v[-1]<arb(args.upper)
