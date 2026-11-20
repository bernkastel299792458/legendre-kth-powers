"""True wrong-sign harmonic charge for every modulus with exactly four small primes."""
from itertools import combinations
from math import prod
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator

def run(end,cut=23,cells=24):
    assert 23<=cut<end<=200 and cells>=1
    Q=210;z,c,r,I,A,S0,u=constants(1732099);x=arb(116).exp();X=(c+2*r).exp()
    ymax=z*z*end/X;ymin=z*z*cut/X;assert ymin>19
    P0=u*H*(-c).exp();mass=X/H*A+2*arb(".0002")*x/H*S0
    G=denominator(z,Q);tot=arb(0);count=0
    def rho(d):return arb(d)/int(fmpz(d).euler_phi())
    possible=[p for p in range(11,end+1) if fmpz(p).is_prime() and p<=ymax]
    for a,b,c0,d in combinations(possible,4):
        m=a*b*c0*d;shape=ymax*a/(b*d)
        if shape<=1:continue
        assert shape>1
        count+=1
        # The second row must contain at least five pairs, including one >=bd.
        # All eligible coefficients for its threshold are <=rho(bd)G_Q(V/(bd)):
        # the smallest among the top two available sizes is bounded via exchange.
        wmax=int(shape.upper().floor().unique_fmpz());gsmall=sum(
            (arb(int(fmpz(j).moebius_mu())**2)/int(fmpz(j).euler_phi())
             for j in range(1,wmax+1) if j%2 and j%3 and j%5 and j%7),arb(0))
        weight=rho(b*c0*d)*rho(b*d)*gsmall**2
        # D,E are separately coprime to Q times m and to any small prime <=ymin.
        base=prod(p for p in range(2,end+1) if fmpz(p).is_prime() and (p<=ymin or (Q*m)%p==0))
        eta=1/rho(base);nw=len(fmpz(base).factor());last=end
        Z=arb(1)
        for p in range(2,last+1):
            if fmpz(p).is_prime() and base%p:Z*=1+arb(1)/(p*(p-1))
        Z*=(arb(1)/last).exp()
        def harm(l,h):
            return Z*(eta*(h/l).log()+(2*(1<<nw)+1)*(1+h.log())/l)
        top_u=z/(b*c0*d);top_v=z/(b*d);logspan=shape.log()
        piece=arb(0)
        for i in range(cells):
            dl=top_u*(-logspan*(i+1)/cells).exp();dh=top_u*(-logspan*i/cells).exp()
            el=X/(m*end*dh);eh=top_v.min(X/(m*cut*dl))
            if eh<=el:continue
            assert eh>el and dl>1 and el>1
            # Use the true joint mean-plus-low correction on the projected rectangle.
            top=min(9,int((Q*m*dh*eh/X).upper().floor().unique_fmpz()))
            cap=arb(48)/Q
            for n in range(1,top+1):
                d0=int(fmpz(n).gcd(Q));cn=int(fmpz(Q//d0).moebius_mu())*int(fmpz(d0).euler_phi())
                ang=(2*arb.pi()*n*(c-2*r).exp()/(Q*m*dh*eh)).union(2*arb.pi()*n*X/(Q*m*dl*el))
                bet=(cn*ang.cos()).upper()
                if not n*X<=Q*m*dl*el:bet=bet.max(arb(0))
                cap+=2*bet/Q
            piece+=harm(dl,dh)*harm(el,eh)*cap
        tot+=4*weight*piece/m
    return count,P0*mass*tot/G**2

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--end",type=int,default=30)
    ap.add_argument("--cells",type=int,default=24);ap.add_argument("--upper");args=ap.parse_args();ctx.prec=144
    n,v=run(args.end,cells=args.cells)
    print("X/",args.end,"<q<=X/23, admissible 4-small sets, whole incorrect-sign harmonic upper",n,v.str(15))
    if args.upper:assert v<arb(args.upper)
