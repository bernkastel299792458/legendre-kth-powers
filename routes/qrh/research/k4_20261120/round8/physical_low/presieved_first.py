"""Full-frequency upper charge through the first true presieved multiplier."""
import argparse
from flint import arb,ctx,fmpz
from actual_split import H,constants
from empty_lcm import region,MEAN

def run(C,Q,P,mean, count=1):
    z,c,r,I,mass,peaks,u=constants(C);L=arb(116)
    eta=arb(int(fmpz(Q).euler_phi()))/Q
    assert fmpz(Q).moebius_mu() and all(int(p)<=P for p,_ in fmpz(Q).factor())
    G=eta*(z.log()+arb("1.331"));xn=(c-2*r).exp();xh=(c+2*r).exp()
    assert z*z<xn
    valid=[n for n in range(2,256) if fmpz(n).gcd(Q)==1]
    k=valid[0];kn=valid[count]
    assert xn/k>xh/kn and count==1
    A=xn/(k*z);ell=(z/A).log();assert A>z/k and ell>0
    rho=ta=arb(1);prob=eta**2;m=0
    for p in range(2,1001):
        if not fmpz(p).is_prime():continue
        if p<=P:
            m+=1
            if Q%p:
                rho*=arb(p)/(p-1)
                prob*=1-arb(1)/p**2
        else:ta*=1+arb(1)/(p*(p-1))
    ta*=(arb(1)/1000).exp()
    D=2**m*rho;coeff=(1+z.log())**2
    slope=(prob*ta**2*ell+eta*2**m*coeff*ta/A)/(k*G**2)
    err=D*coeff*rho*ta*z/G**2
    s=u*(2*r).exp()*mass*slope
    e=u*arb(H)*(-c).exp()*peaks*err
    _,v,_=region("116",C,MEAN if mean else (),True,threshold=xh/kn,sieve_mod=Q)
    inv=u*(2*r).exp()*mass*v
    return k,kn,s,e,inv,s+e+inv

if __name__=="__main__":
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--C",type=int,default=1732099)
    ap.add_argument("--Q",type=int,nargs="+",default=[2,6,30,210]);ap.add_argument("--small",type=int,default=37)
    ap.add_argument("--mean",action="store_true");ap.add_argument("--upper")
    a=ap.parse_args();ctx.prec=160
    for Q in a.Q:
        k,kn,*v=run(a.C,Q,a.small,a.mean)
        print("Q",Q,"actual k",k,"cut at next k",kn,"slope/edge/inverse/total",*(x.str(13) for x in v))
        if a.upper:assert v[-1]<arb(a.upper)
