"""Full near-lobe remainder split by actual multiple and by rectangular Fourier estimates."""
from functools import lru_cache
from pathlib import Path
import argparse,sys
from flint import arb,ctx,fmpz
from empty_lcm import region
from row_inputs import MEAN

ROOT=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(ROOT/"round7/physical"))
from parity_target import H
C0=3000000

@lru_cache(None)
def wt(i,g):
    return sum((arb(int(fmpz(b).moebius_mu())**2)/int(fmpz(b).euler_phi())
               for b in range(1,2**(i+1)) if fmpz(b).gcd(g)==1),arb(0))

def constants(C):
    l=arb(116);x=l.exp();h=arb(H);r=arb("1e-6")
    d=(4*(-l/4).exp()).log1p()/2;c=l+d
    z=C*(x/h).sqrt();a=(1-arb("1e-12"))*h*d;I=arb.pi()*a.sin()/a
    mass=(1-a/arb.pi())*I;peaks=a.sin()/a+(1+a.cos())/12
    u=(c+2*r)*r.exp()/I
    return z,c,r,I,mass,peaks,u

def direct(C,R,mean,exact=False):
    z,c,r,I,mass,peaks,u=constants(C);G=z.log()+arb("1.331")
    lo=(c-2*r).exp();hi=(c+2*r).exp()
    cut=C*C*R//H
    assert C*C*R%H and cut<=127
    C1=E1=arb(1)
    for p in range(2,1001):
        if not fmpz(p).is_prime():continue
        if p<=37:E1*=2*arb(p)/(p-1)
        else:C1*=1+arb(1)/(p*(p-1))
    C1*=(arb(1)/1000).exp();E1*=(1+z.log())**2
    slopes=intercepts=arb(0);pairs=0
    for g in range(1,cut+1):
        if not fmpz(g).moebius_mu():continue
        rho=arb(g)/int(fmpz(g).euler_phi())
        imax=(cut//g).bit_length()-1
        for i in range(imax+1):
            for j in range(min(i,imax-i)+1):
                D=z/(g*2**i);F=z/(g*2**j)
                nmax=int((4*hi/(g*D*F)).floor().unique_fmpz())
                fac=(1 if i==j else 2)*(rho/G)**2*wt(i,g)*wt(j,g)
                if exact:nmax=min(nmax,int((hi*R/arb(116).exp()).floor().unique_fmpz()))
                for k in range(1,nmax+1):
                    lower_k=lo.max(k*arb(116).exp()/R) if exact else lo
                    A=(D/2).max(lower_k/(g*k*F));B=D.min(2*hi/(g*k*F))
                    if B<A:continue
                    assert B>A and A>1
                    harm=(B/A).log()+arb("2.44")*(1/A.sqrt()+1/B.sqrt())
                    slopes+=fac*harm*C1/(k*g)
                    intercepts+=fac*harm*E1*B
                    pairs+=(1 if i==j else 2)
    signed=(region("116",C,MEAN if mean else (),True,threshold=arb(116).exp()/R) if exact else region("116",C,MEAN if mean else (),whole_cut=cut))[1]
    return cut,pairs,u*mass*(2*r).exp()*slopes,u*arb(H)*(-c).exp()*peaks*intercepts,u*mass*(2*r).exp()*signed

def costs(C):
    from parity_target import certificate
    z,c,r,I,mass,peaks,u=constants(C);G=z.log()+arb("1.331")
    ordinary=u*(2*r).exp()*mass/G
    upstream=certificate(6,38)[2]
    t=arb(H)*r;R=arb(".01");v=116-arb(H).log()+arb("1.16613")
    J=int((t/(2*arb.pi())).floor().unique_fmpz())-1
    a=(1-arb("1e-12"))*arb(H)*(c-116)
    c2=2*(116+R)*(R/2).exp()/(I*v*v);c1=c2*R.exp()*(v-1)
    return ordinary,upstream,c1*4/(t*(1-(a/t)**2))+c2*(1+a.cos())/(2*arb.pi()**2*(J-1))

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=C0)
    ap.add_argument("--R",type=int,nargs="+",default=[1,2,4,8]);ap.add_argument("--mean",action="store_true")
    ap.add_argument("--exact",action="store_true");args=ap.parse_args();ctx.prec=120
    print("main, upstream, middle tail",*(v.str(13) for v in costs(args.C)),flush=True)
    for R in args.R:
        c,n,*v=direct(args.C,R,args.mean,args.exact)
        print("R",R,"cut",c,"k cells",n,"spike slope/intercept, inverse",*(w.str(14) for w in v),flush=True)
