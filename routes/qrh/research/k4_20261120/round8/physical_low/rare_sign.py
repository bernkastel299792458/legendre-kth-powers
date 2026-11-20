"""Harmonic and physical wrong-sign bounds ordered by the number of small prime factors."""
from math import prod,gcd
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator

def run(end,threshold,cut=23,three=False,anchor=0):
    Q=210;z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();x=arb(116).exp()
    R0=z*z*end/X;assert 23<=cut<end<=208 and R0<209 and (z*z*cut/X)>19 and threshold>=4
    assert not(three and anchor) and 0<=anchor<threshold and (not anchor or cut==23)
    mass=X/H*A+2*arb(".0002")*x/H*S;P0=u*H*(-c).exp();G=denominator(z,Q)
    ps=[p for p in range(11,end) if fmpz(p).is_prime() and p<R0];n=len(ps)
    units=[k for k in range(cut,end) if gcd(k,Q)==1];hk=sum((1/arb(k) for k in units),arb(0))
    bases=[1,210,2*3*5*7*11*13*17*19]
    params=[]
    for B in bases:
        eta=arb(int(fmpz(B).euler_phi()))/B;ne=2**len(fmpz(B).factor());Z=(arb(1)/end).exp()
        for p in range(2,end):
            if fmpz(p).is_prime() and B%p:Z*=1+arb(1)/(p*(p-1))
        # Include p=end in the finite Euler product if applicable.
        if fmpz(end).is_prime() and B%end:Z*=1+arb(1)/(end*(end-1))
        params.append((eta,ne,Z))
    def hw(ll,logspan):
        # L may lie below 1, but it can be replaced by 1 on an integer row.
        l=ll.max(arb(1))
        opts=[Z*(eta*logspan+(2*ne+1)*(1+l.log()+logspan)/l) for eta,ne,Z in params]
        return min(opts,key=lambda v:float(v.upper()))
    rows=[[arb(0),arb(0)] for j in range(n+1)]
    for p in ps:
        span=(R0/p).log(); rest=[r for r in ps if r!=p];needed=3 if three else anchor
        smaller=[r for r in rest if r<p]
        if len(smaller)<needed:continue
        coef=[[arb(0)]*(needed+1) for _ in range(n)];coef[0][0]=arb(1)
        sqrtcoef=[x.copy() for x in coef]
        for prime in rest:
            for j in range(len(rest),0,-1):
                for i in range(needed+1):
                    new=min(needed,i+(prime<p))
                    coef[j][new]+=coef[j-1][i]*2/(prime-1)
                    sqrtcoef[j][new]+=sqrtcoef[j-1][i]*2*arb(prime).sqrt()/(prime-1)
        for dim in range(threshold,n+1):
            j=dim-1;must=sorted(smaller,reverse=True)[:needed]
            maxother=prod(must)*prod(sorted(set(rest)-set(must),reverse=True)[:j-needed])
            # Orient A B=S/p so A>=B, hence E>=z/(R0 sqrt(S/p)).
            hd=hw(z/(R0*maxother),span)
            he=hw(z/(R0*arb(maxother).sqrt()),span)
            peak=(arb(48)+40)/Q;w=arb(p-2)/(p-1)**2
            rows[dim][0]+=w*coef[j][needed]*hd*he*peak*P0*mass/G**2
            phys=[Z*(coef[j][needed]*eta*mass*hk+
                     sqrtcoef[j][needed]*(ne+1)*(1+z.log())*S*z*len(units)) for eta,ne,Z in params]
            rows[dim][1]+=w*hd*P0/G**2*min(phys,key=lambda v:float(v.upper()))
    return rows[threshold:]

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--end",type=int,default=100)
    ap.add_argument("--threshold",type=int,default=6);ap.add_argument("--upper",nargs=2)
    ap.add_argument("--three",action="store_true");ap.add_argument("--anchor",type=int,default=0)
    a=ap.parse_args();ctx.prec=144
    rr=run(a.end,a.threshold,three=a.three,anchor=a.anchor);out=[sum((v[j] for v in rr),arb(0)) for j in range(2)]
    print("large-dimensional inverse and physical",*(t.str(14) for t in out))
    if a.upper:assert all(t<arb(v) for t,v in zip(out,a.upper))
