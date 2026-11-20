"""Full ordinary cost of signed bandlimited Liouville parity tests at L=116."""
from pathlib import Path
import json
from functools import lru_cache
from flint import arb,ctx,fmpz

H=3000175332800
R=arb
def kernel(u,a):
    return (((a+u)/2).sinc()*((a-u)/2).sinc())/2


def poly(theta,coef):
    x=theta.cos()
    y=z=R(0)
    for b in coef[:0:-1]:
        y,z=b+2*x*y-z,y
    return coef[0]+x*y-z


@lru_cache(None)
def majorant(J,prec):
    assert prec==ctx.prec
    l=R(116);K=R(H);d=(4*(-l/4).exp()).log1p()/2;c=l+d
    a=(1-R("1e-12"))*K*d;pi=R.pi();I=pi*a.sin()/a
    assert a<2
    ff=json.loads(Path(__file__).with_name("majorants.json").read_text(encoding="utf8"))
    coef=list(map(R,ff[str(J)]));N=2048
    B2=sum(i*i*abs(x) for i,x in enumerate(coef))
    lift=R(0)
    for left,right,threshold in ((R(0),a,R(0)),(a,pi,R(1))):
        dw=(right-left)/N
        worst=R(0)
        for j in range(N+1):
            worst=worst.max(threshold-poly(left+j*dw,coef))
        lift=lift.max(worst+B2*dw**2/8)
    coef[0]+=lift
    B0=sum(map(abs,coef));B1=sum(i*abs(x) for i,x in enumerate(coef))
    def f(t):return (2*kernel(t,a)/I-1/pi)*poly(t,coef)
    val=sum((f(a*j/N) for j in range(1,N)),(f(R(0))+f(a))/2)*a/N
    sec=2/I*(B0/12+B1/3+B2/2)+B2/pi
    mass=coef[0]+2*(val+sec*a**3/(12*N**2))
    return mass,4*B0+6*B1,coef,l,c,a,I


def certificate(J,logz):
    p,tv,coef,l,c,a,I=majorant(J,ctx.prec)
    K=R(H);Q=R(10000);r=R(".01");pi=R.pi()
    D=(l/2).exp()*I/K;g0=(1-a.cos())/a**2
    G=R(logz)+R("1.331");z=R(logz).exp()
    assert R("1.33258")-R("2.44")/z.sqrt()>R("1.331") and R(logz)<c-r
    C=R(1)
    for q in range(2,1001):
        if fmpz(q).is_prime():C*=1+R(2)/(q*(q-1))
    C*=R(".002").exp()
    main=c*((1/c+R(1)/2)**2/(4*Q**2)).exp()*p/(2*G)
    err=c*((1/c-R(1)/2)**2/(4*Q**2)).exp()*K*(-c).exp()*z**2*(C/G)**2*tv/(4*I)
    # These separately retained positive terms are from round2/local/check_edge.py.
    powers=g0*r.exp()*(c+r)**2/(2*R(2).log()*D)
    far=4*g0*(3*c/2+R(9)/(8*Q**2)-(Q*r)**2/2).exp()/D
    pole=16*pi.sqrt()*Q/(K*I)
    small=2*K*K.log()*pi/(a*K*D)
    arch=g0*(7+(1+K+2*Q/pi.sqrt()).log())/D
    first=Q/pi.sqrt();second=2*Q**2;third=8*Q**3/pi.sqrt()
    count=((K/(2*pi)).log()/(2*pi)+R(".15")/K)*second/2
    count+=third/(12*pi*K)+(R(".3")*K.log()+6)*first
    edge=pi/(I*K)*(1/(16*Q**2)).exp()*((-l/8).exp()+(-7*l/8).exp())*count
    old=powers+far+pole+small+arch+edge
    return main,err,old,1-main-err-old


if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--degree",type=int);ap.add_argument("--logz",type=int)
    ap.add_argument("--margin");args=ap.parse_args();ctx.prec=160
    cases=[(24,31),(30,31),(12,34),(8,36),(6,38),(4,40),(3,41)] if args.degree is None else [(args.degree,args.logz)]
    for J,z in cases:
        v=certificate(J,z);m=majorant(J,ctx.prec)[0]
        print("J",J,"log z",z,"mass",m.str(12),"main, sieve error, upstream, twist allowance",
              *(x.str(12) for x in v),flush=True)
        if args.margin:assert v[-1]>R(args.margin)
