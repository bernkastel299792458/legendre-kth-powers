"""All forward/forward and dual/dual pairs separated in logarithmic frequency."""
from math import gcd,prod
from functools import lru_cache

from flint import arb,ctx
from quarter_diagonal import primes,signed
from quarter_signed_block import target,block


@lru_cache(None)
def positive_prefix(q,tag,prec):
    if tag=='direct':
        coeff=[int(gcd(j,q)==1) for j in range(1,q+1)]
        h=arb(3)/4
    else:
        ps=primes(q)
        coeff=[prod((p-1 if j%p==0 else 1) for p in ps) for j in range(1,q+1)]
        h=arb(1)/4
    mean=arb(sum(coeff))/q
    cnt=0;lo=hi=acc=C=arb(0)
    for j,v in enumerate(coeff,1):
        lo=lo.min(cnt-mean*j);cnt+=v;hi=hi.max(cnt-mean*j)
        acc+=v*arb(j)**(-h)
        C=C.max(acc-mean*arb(j)**(1-h)/(1-h))
    C=C.max(acc-mean*arb(q)**(1-h)/(1-h)+2*(hi-lo+1)*arb(q)**(-h))
    return mean,C


def separated(U,alpha,w,gap,q=2310):
    T=U.exp();s=arb(3)/4;a=2*s-1
    Y=(U-3).exp();W=arb('9.5');X=Y*W.exp()
    ts=arb('1.5e12');K=arb('2.25e12');P=128;m=2048
    D=arb('1.01')*T;N=arb(q)*ts/(2*arb.pi())
    eta,C=positive_prefix(q,'direct',ctx.prec)
    ram,Cr=positive_prefix(q,'dual',ctx.prec)
    M1=C+eta*(X**(1-s)-Y**(1-s))/(W*(1-s)**2)
    maxf=alpha*w.exp()*(2*T*q/(2*arb.pi())).sqrt()
    maxr=w.exp()/alpha*(2*T*q/(2*arb.pi())).sqrt()
    direct=1+M1*(C+eta*maxf**(1-s)/(1-s))
    dual=M1/arb(q).sqrt()*N**(-a/2)*(Cr+ram*maxr**s/s)
    def factor(z):
        ends=(ts/K)**(2*P)+(D/(2*T))**m
        diff=3*(2*P/K+(m+z)/D)+1/(w*ts)
        return ends/gap+diff/gap**2
    # Nonstationary part of the genuinely oscillatory cross term. Smooth in
    # log(t/t0), as a sharp edge would charge 1/gap per atom of the AFE.
    slope=2*P/K+(m+a)/D
    Bprime=slope+1/(2*w*ts)
    varprime=3*slope+3/(w*ts)
    edges=(ts/K)**(2*P)+(D/(2*T))**m
    cross=edges/gap+(varprime+4*Bprime)/gap**2+24/(ts*gap**3)
    return factor(arb(0))*direct**2,factor(a)*dual**2,2*direct*dual*cross


if __name__=='__main__':
    ctx.prec=160
    U=arb(37);res=signed(2310,arb(1)/2)
    for alpha_,f in ((64,4),(96,8)):
        alpha=arb(alpha_);w=arb('.75');room=target(U,alpha,w,res)[-1]
        covered=block(f*U.exp(),alpha,w)[-1]
        for g in ('.01','.03','.05','.10'):
            costs=separated(U,alpha,w,arb(g))
            print('alpha',alpha_,'N/T',f,'gap',g,'direct+dual prices and remaining signed allowance',
                  *(x.str(10) for x in (*costs,room-covered-sum(costs))),flush=True)
