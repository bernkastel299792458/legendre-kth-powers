"""Every wrong-sign Selberg contribution to the harmonic mean at an upper annulus."""
import argparse
from bisect import bisect_left,bisect_right
from itertools import combinations
from math import gcd,prod
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator

def table(ps,end):
    m=prod(ps);phi=prod(p-1 for p in ps);subs=sorted(prod(ps[i] for i in range(len(ps)) if j>>i&1)
                                                              for j in range(1<<len(ps)))
    N=len(subs);prev=[0]*N;bad=[]
    for i,a in enumerate(subs):
        acc=0;row=prev.copy()
        for j,b in enumerate(subs):
            if a*b>end*m:break
            p=gcd(a,b)
            if a*b==m*p:
                if p==1:acc+=phi
                elif p in ps:acc-=(phi//(p-1))*(p-2)
                else:
                    common=[r for r in ps if p%r==0]
                    assert len(common)<=2
                    den=prod(r-1 for r in common)
                    acc+=((-1)**len(common))*(phi//den)*prod(r-2 for r in common)
            row[j]+=acc
            if i<=j and row[j]<0:
                bad.append((a,subs[i+1] if i+1<N else 0,b,subs[j+1] if j+1<N else 0,
                            (1 if i==j else 2)*(-row[j])))
        prev=row
    return m,phi,bad

def run(end,cut=23,maxdim=None,physical=False):
    assert 23<=cut<end<=208
    Q=210;z,c,r,I,A,S0,u=constants(1732099);x=arb(116).exp();X=(c+2*r).exp();xl=(c-2*r).exp()
    ymax=z*z*end/X; ymin=z*z*cut/X;assert ymax<209 and 19<ymin
    P0=u*H*(-c).exp();mass=X/H*A+2*arb(".0002")*x/H*S0;G=denominator(z,Q)
    possible=[p for p in range(11,end) if fmpz(p).is_prime() and p<=ymax]
    units=[k for k in range(cut,end) if gcd(k,Q)==1]
    assert xl/(cut-1)>X/cut
    hi=len(possible) if maxdim is None else min(len(possible),maxdim)
    rows=[]
    for dim in range(4,hi+1):
        nset=nc=0;total=arb(0)
        for ps in combinations(possible,dim):
            m,phi,bad=table(ps,end)
            if not bad:continue
            base=prod(p for p in range(2,end+1) if fmpz(p).is_prime() and (p<=ymin or (Q*m)%p==0))
            eta=arb(int(fmpz(base).euler_phi()))/base;ne=2**len(fmpz(base).factor())
            Z=arb(1)
            for p in range(2,end+1):
                if fmpz(p).is_prime() and base%p:Z*=1+arb(1)/(p*(p-1))
            Z*=(arb(1)/end).exp()
            def harmonic(l,h):return Z*(eta*(h/l).log()+(2*ne+1)*(1+h.log())/l)
            accum=arb(0);active=False
            for a,ah,b,bh,neg in bad:
                # u=z/D,v=z/E. The bound uv<=m*ymax also bounds the final unbounded level.
                ulo=arb(a);uhi=(arb(ah) if ah else m*ymax/b).min(m*ymax/b)
                vlo=arb(b);vhi=(arb(bh) if bh else m*ymax/a).min(m*ymax/a)
                if uhi<=ulo or vhi<=vlo:continue
                dl=(z/uhi).max(X/(m*end*(z/vlo)));dh=(z/ulo).min(X/(m*cut*(z/vhi)))
                el=(z/vhi).max(X/(m*end*(z/ulo)));eh=(z/vlo).min(X/(m*cut*(z/uhi)))
                if dh<=dl or eh<=el:continue
                assert dh>dl>1 and eh>el>1
                if physical:
                    ka=int((xl/(m*dh*eh)).lower().floor().unique_fmpz())
                    kb=int((X/(m*dl*el)).upper().ceil().unique_fmpz())
                    for k in units[bisect_left(units,ka):bisect_right(units,kb)]:
                        left=dl.max(xl/(k*m*eh));right=dh.min(X/(k*m*el))
                        if right<=left:continue
                        assert right>left
                        raw=eta*mass/k+m*(ne+1)*(1+eh.log())*S0*right
                        accum+=neg*Z*harmonic(left,right)*raw
                    nc+=1;active=True
                    continue
                cap=min(9,int((Q*m*dh*eh/X).upper().floor().unique_fmpz()));cg=arb(48)/Q
                for n in range(1,cap+1):
                    gg=gcd(n,Q);cn=int(fmpz(Q//gg).moebius_mu())*int(fmpz(gg).euler_phi())
                    ang=(2*arb.pi()*n*xl/(Q*m*dh*eh)).union(2*arb.pi()*n*X/(Q*m*dl*el))
                    v=(cn*ang.cos()).upper()
                    if not n*X<=Q*m*dl*el:v=v.max(arb(0))
                    cg+=2*v/Q
                accum+=neg*cg*harmonic(dl,dh)*harmonic(el,eh);nc+=1;active=True
            total+=accum/phi**2
            nset+=active
        rows.append((dim,nset,nc,P0*(1 if physical else mass)*total/G**2))
    return rows

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--end",type=int,default=30)
    ap.add_argument("--maxdim",type=int);ap.add_argument("--upper");ap.add_argument("--physical",action="store_true")
    a=ap.parse_args();ctx.prec=144;rows=run(a.end,maxdim=a.maxdim,physical=a.physical);total=sum((v for *_,v in rows),arb(0))
    for dim,n,nc,v in rows:print("small dimensions, sets, cells, wrong-sign normalized",dim,n,nc,v.str(14))
    print("total wrong-sign",("actual physical" if a.physical else "harmonic"),total.str(15))
    if a.upper:assert total<arb(a.upper)
