"""True absolute multiple mass, in the single forward first lobe at L=116."""
from flint import arb,ctx,fmpz
from actual_split import H,constants,costs
from parity_target import kernel

def lower(C=3000000,P=23,both=False):
    z,c,r,I,_,_,_=constants(C);L=arb(116);x=L.exp()
    K=arb(H);a=(1-arb("1e-12"))*K*(c-L);end=2*arb.pi()-a
    xhi=(c+end/K).exp();A=xhi/z;ell=(z/A).log();assert ell>0 and A>1
    xlo=(c-end/K).exp() if both else x;M=xlo/z
    rho=disc=p0=arb(1);m=0;tail=arb(1)/1000
    for p in range(2,1001):
        if not fmpz(p).is_prime():continue
        if p<=P:
            rho*=arb(p)/(p-1);disc*=2*arb(p)/(p-1)
            p0*=1-arb(1)/p**2;m+=1
        else:tail+=arb(1)/p**2
    B=z**(arb(1)/3);B0=1000000;assert B>B0 and B0>P
    slope=ell*(p0-3*tail)-(2**m+z.sqrt()+1+z.log()+tail)/A
    slope-=rho**2*(arb(1)/B0+(z/M).sqrt()/B)*(ell+1/A)
    intercept=(z+1)*(rho*disc*(1+B0+z.log()/arb(2).log())+rho**2*(B+z/B**2))
    assert slope>0
    G=z.log()+arb("1.34")+arb("2.44")/z.sqrt()
    N=2048;start=K*(c-L);step=(end-start)/N
    area=step*sum(kernel(start+step*j,a) for j in range(1,N+1))
    peak=a.sin()/(2*a)
    # Physical envelope log(n)/sqrt(n) and Gaussian on this tiny first lobe.
    # 0<log(n)-c<2*pi/K and normalization D=e^(L/2)*I/K.
    mweight=(L-end/K)*((L-c-end/K)/2-(arb(10000)*end/K)**2).exp()
    charge=(2 if both else 1)*mweight/(I*G**2)*(xlo/x*slope*area-K/x*intercept*peak)
    tail=4/(I*K*r*(1-(a/(K*r))**2))+(start-a)/I
    ordinary_lower=(L-r)*((c-L-r)/2-(arb(10000)*r)**2).exp()*(1-a/arb.pi()-tail)/G
    return charge,slope,area,1-sum(costs(C)),1-ordinary_lower

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=3000000)
    ap.add_argument("--small",type=int,default=23);ap.add_argument("--lower")
    ap.add_argument("--both",action="store_true");a=ap.parse_args();ctx.prec=160
    val=lower(a.C,a.small,a.both)
    print("absolute k=1,g=1,lobe lower bound; harmonic density; one-lobe area; bookkeeping allowance; 1 minus ordinary lower",*(t.str(16) for t in val))
    if a.lower:assert val[0]>arb(a.lower)
