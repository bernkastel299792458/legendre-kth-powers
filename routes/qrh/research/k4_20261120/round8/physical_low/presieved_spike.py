"""First physically attainable odd/presieved multiple: rigorous absolute charge."""
from flint import arb,ctx,fmpz
from actual_split import H,constants
from parity_target import kernel

def run(C,Q,k,P,both):
    assert fmpz(Q).moebius_mu() and fmpz(k).gcd(Q)==1 and P<=997
    assert all(int(p)<=P for p,_ in fmpz(Q).factor())
    z,c,r,I,_,_,_=constants(C);L=arb(116);x=L.exp();K=arb(H)
    start=K*(c-L);a=(1-arb("1e-12"))*start;b=2*arb.pi()-a
    xh=(c+b/K).exp();xl=(c-b/K).exp() if both else x
    A=xh/(k*z);M=xl/(k*z);ell=(z/A).log()
    assert ell>0 and A>1
    eta=arb(int(fmpz(Q).euler_phi()))/Q
    u=d=p0=arb(1);s=arb(1)/1000;m=0;corr=arb(0);min_k=2
    while fmpz(min_k).gcd(Q)>1:min_k+=1
    for p in range(2,1001):
        if not fmpz(p).is_prime():continue
        if p<=P:
            m+=1
            if Q%p:
                u*=arb(p)/(p-1);p0*=1-arb(1)/p**2
            else:corr+=arb(p).log()/p
        else:s+=arb(1)/p**2
    d=u*2**m;p0*=eta**2
    B=z**(arb(1)/3);B0=1000000
    slope=ell*(p0-3*eta*s)-eta*(2**m+z.sqrt()+1+z.log()+s)/A
    slope-=u**2*(arb(1)/B0+(z/M).sqrt()/B)*(ell+1/A)
    E=(z+1)*(u*d*(1+B0+z.log()/arb(2).log())+u**2*(B+z/B**2))
    assert slope>0
    # G_Q(z) upper from the Selberg splitting and G_Q(z/d)>=eta G(z/d).
    gp=eta*(z.log()+arb("1.34"))+corr+arb("2.44")*(1+arb(Q).sqrt())/z.sqrt()
    step=(b-start)/2048
    area=step*sum(kernel(start+step*j,a) for j in range(1,2049))
    w=(L-b/K)*((L-c-b/K)/2-(arb(10000)*b/K)**2).exp()
    charge=(2 if both else 1)*w/(I*gp**2)*(xl/x*slope*area/k-K/x*E*a.sin()/(2*a))
    # If min_k*z^(-2) q>1 throughout, the actual gcd must be one.
    separated=bool(xl*min_k>k*z**2)
    return charge,separated,slope,gp

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=1732099)
    ap.add_argument("--Q",type=int,default=2);ap.add_argument("--k",type=int,nargs="+",default=[3])
    ap.add_argument("--small",type=int,default=23);ap.add_argument("--one",action="store_true");ap.add_argument("--lower")
    a=ap.parse_args();ctx.prec=160
    for k in a.k:
        v,se,s,g=run(a.C,a.Q,k,a.small,not a.one)
        print("Q",a.Q,"k",k,"single-sign after modulus grouping",se,"charge lower",v.str(15),"slope",s.str(12),"G upper",g.str(12))
        if a.lower:assert v>arb(a.lower)
