"""A polynomial majorant of the integrated Poisson kernel in the verified-height strip."""
from functools import lru_cache
from math import comb
import argparse
from flint import arb,acb_series,ctx
from finite_inverse import H,right


@lru_cache(maxsize=256)
def arithmetic(k,m,precision):
    u=arb(1)+arb(k)/100
    assert precision==ctx.prec and ctx.cap>=m+1
    z=acb_series([u,1],m+1).zeta()
    series=-z.derivative()/z
    return [((-1)**j*series[j]).real for j in range(m)]


def estimate(s,t,k,m):
    u,euler,_=right(k,ctx.prec)
    assert arb(1)/2<s<u and 1<u<=6 and 100<=t<=H//2 and 1<=m<=24
    a,b=s-arb(1)/2,u-arb(1)/2
    eta=1-(a/b)**2
    terms=[eta**l/(2*l) for l in range(1,m)]
    terms.append((b/a).log()-sum(terms,arb(0)))
    assert all(x>0 for x in terms)
    inv=[]
    for j in range(1,m+1):
        inv.append(sum((terms[l-1]*arb(2*comb(2*l-j-1,l-j))/2**(2*l-j)
                        for l in range(j,m+1)),arb(0))*b**j)
    h=u-s
    assert inv[0]>h
    primes=arithmetic(k,m,ctx.prec)
    assert all(v>0 for v in primes)
    cost=(inv[0]-h)*(t/(2*arb.pi())).log()/2+arb(".04")*(inv[0]+h)
    cost+=sum((v*w for v,w in zip(inv,primes,strict=True)),arb(0))
    for j,w in enumerate(inv[1:],2):
        cost+=w*(arb(3)/100**j+arb.pi()/(4*100**(j-1)))
    far=96*(arb(H).log()+1)/H
    # For j>=2 both reciprocals have modulus <=2/|gamma|. For j=1
    # their real parts are bounded by 8/gamma^2.
    cost+=(h+sum(inv,arb(0)))*far
    return euler*cost.exp()


def gaussian(x,y,i,k,m):
    T=arb(y).exp()
    X=arb(x).exp()
    width=arb(".1")
    B=arb(1000)
    u,euler,_=right(k,ctx.prec)
    s=arb(i)/100
    assert T-B>100 and T+B<arb(H)/2
    q=estimate(s,T+B,k,m)
    vertical=q*X**(s-1)*((width*s)**2/2).exp()
    sides=2*width*(u-s)*q*X**(u-1)*(width**2*(u*u-B*B)/2).exp()
    tails=euler*X**(u-1)*((width*u)**2/2).exp()*(width*B/arb(2).sqrt()).erfc()
    return vertical+sides+tails


if __name__=="__main__":
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("--complete",action="store_true")
    opts=arg.parse_args()
    ctx.prec=160
    ctx.cap=32
    if opts.complete:
        cases=[(43,26,63,245,20,".001136"),(55,15,59,215,12,".000001544"),
               (60,25,61,245,20,".000001512"),(70,25,59,245,20,".0000000260")]
        for x,y,i,k,m,limit in cases:
            val=gaussian(x,y,i,k,m)
            print("Gaussian divided by X",x,y,val.str(15),"degree",m,flush=True)
            assert val<arb(limit)
        raise SystemExit(0)
    for x,y in ((43,26),(55,15),(60,25)):
        T=arb(y).exp()+1000
        for degree in (1,2,3,4,6,8):
            best=None
            for i in range(58,91):
                s=arb(i)/100
                for k in range(10,91,3):
                    c=estimate(s,T,k,degree)*((s-1)*x).exp()
                    if best is None or c<best[0]:best=c,i,k
            print(x,y,degree,best[0].str(10),best[1],best[2],flush=True)
