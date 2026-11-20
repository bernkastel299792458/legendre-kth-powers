"""A signed all-index Hilbert sweep of the forward branch at sigma=3/4."""
from functools import lru_cache
from fractions import Fraction
from math import gcd,lcm,prod

from flint import arb,ctx

from quarter_diagonal import diagonals,primes,signed,zq


@lru_cache(None)
def periodic(q,precision):
    a=arb(1)/2
    eta=arb(sum(gcd(j,q)==1 for j in range(q)))/q
    count=0;hi=lo=arb(0)
    p=arb(0);ph=pl=arb(0)
    for j in range(1,q+1):
        m=eta*arb(j)**(1-a)/(1-a)
        pl=pl.min(p-m)
        if gcd(j,q)==1:
            count+=1
            p+=arb(j)**(-a)
        ph=ph.max(p-m)
        hi=hi.max(count-eta*j)
        lo=lo.min(count-int(gcd(j,q)==1)-eta*j)
    tail=2*(hi-lo+1)/arb(q)**a
    ph=ph.max(p-eta*arb(q)**(1-a)/(1-a)+tail)
    pl=pl.min(p-eta*arb(q)**(1-a)/(1-a)-tail)
    return eta,ph,ph-pl


@lru_cache(None)
def small_sigma(q):
    # All transitions in Sigma_q up through the published threshold.
    terms=[]
    peak=value=Fraction(0)
    for d in range(1,422):
        if gcd(d,q)>1:continue
        n=d;mu=1
        for p in range(2,d+1):
            if n%p:continue
            n//=p;mu=-mu
            if n%p==0:
                mu=0;break
        if mu:
            value+=Fraction(1,d)+2*sum(Fraction(mu*e,lcm(d,k)) for k,e in terms)
            terms.append((d,mu));peak=max(peak,value)
    return peak


def harmonic(n,q,eta):
    c=arb.const_euler()+sum(arb(p).log()/(p-1) for p in primes(q))
    # |H_floor(x)-log x-gamma| <= 1/x, valid also 0<x<1.
    return eta*(n.log()+c)+2**len(primes(q))/n


def block(N,alpha,w,q=2310,U=arb(37)):
    N=arb(N);T=U.exp();Y=(U-3).exp()
    ts=arb('1.5e12');K=arb('2.25e12');P=128
    eta,C,osc=periodic(q,ctx.prec)
    a=arb(1)/2;W=arb('9.5')
    D=(N*w.exp()/(alpha*(q*ts/(2*arb.pi())).sqrt())).ceil()
    assert D>=1 and D<Y
    # Integrated signed main; valid for all real cutoff thresholds.
    small=small_sigma(q)
    signed_cap=eta*small.numerator/small.denominator
    if D>=422:signed_cap=signed_cap.max(arb('.445'))
    if D>=10**8:signed_cap=signed_cap.max(arb('.6593'))
    numax=eta/(1-a)
    lcm_error=numax**2*D**(2-2*a)*zq(2-a,q)
    lcm_error+=2*numax*C*D**(1-a)*harmonic(D,q,eta)
    lcm_error+=C**2*(numax*D**(1-a)+C)
    Jlost=signed_cap*N**(1-a)/(1-a)+osc*lcm_error
    head=int((N/Y).upper().floor().unique_fmpz())
    runs=[(k,((N/(Y*k)).log()/W).max(arb(0)).min(arb(1))) for k in range(1,head+1) if gcd(k,q)==1]
    Jfull=arb(0)
    for k,v in runs:
        for j,h in runs:
            L=lcm(k,j)
            Jfull+=v*h*(numax*N**(1-a)/L+C/arb(L)**a)
    J=(Jlost.sqrt()+Jfull.sqrt())**2
    const=arb('.915503')+arb('.118')*harmonic(N,q,eta)
    sweep=2+((arb('1.01')*T/K).log()+1/arb(2*P)+1/arb(2048))/(2*w)
    return D,Jlost,Jfull,sweep*const*J


def error_constant_square(q,alpha,w):
    b=alpha*arb(q).sqrt();s=arb(3)/4
    ds=[d for d in range(1,q+1) if q%d==0]
    cuts=[-w]+[(arb(d)/b).log() for d in ds if -w<(arb(d)/b).log()<w]+[w]
    ans=arb(0)
    for l,r in zip(cuts,cuts[1:]):
        mid=b*((l+r)/2).exp()
        f=sum((16*b**(1-s)/d for d in ds if d<mid),arb(0))
        g=sum((11*b**(-s) for d in ds if d>mid),arb(0))
        for c,pow_ in ((f*f,2*(1-s)),(2*f*g,1-2*s),(g*g,-2*s)):
            ans+=c*((r*pow_).exp()-(l*pow_).exp())/pow_
    return (2*arb.pi())**s*ans/(2*w)


def target(U,alpha,w,summary,q=2310):
    eta,_,_=periodic(q,ctx.prec)
    T=U.exp();pi=arb.pi();X=(U+arb('6.5')).exp()
    ts=arb('1.5e12');K=arb('2.25e12');K0=arb(3000175332800)/5
    P=128;m=2048;s=arb(3)/4;a=2*s-1;D=arb('1.01')*T
    assert ts>2*pi*q*(alpha*w.exp()).max(w.exp()/alpha)**2
    norm=arb('1.000000001')
    old=diagonals(U,arb(-3),arb('9.5'),alpha,q,summary=summary)
    def sinc(x):return x.sinh()/x
    full,lead,derr,rerr=old[:4]
    lead*=sinc(a*w);derr*=sinc(2*a*w)
    diag=(full.sqrt()+(lead+derr).sqrt())**2+lead+rerr
    M1=4*X**(1-s);euler=prod(1+arb(p)**(-s) for p in primes(q))
    early=ts*(norm*(ts+2)/K)**(2*P)*(12*(ts+2)**(1-s)*euler*M1+1)**2
    far=2*T*(D/(2*T))**m*norm*(12*(2*T+2)**(1-s)*euler*M1+1)**2/(m-2)
    E=12*(1+X.log())*X.sqrt()+2*M1**2/arb(2).log()
    mean=zq(2*s,q)*D**(1-s)*(1/(1-s)+1/(m+s-1))
    rem=error_constant_square(q,alpha,w)*arb('1.00001')*(mean+2*E*K0**(-s))
    room=((arb('1.75e11')-early-far).sqrt()-rem.sqrt())**2/norm-diag
    assert rem+early+far<arb('1.75e11')
    return diag,rem,early,room


if __name__=='__main__':
    ctx.prec=160
    U=arb(37);summary=signed(2310,arb(1)/2)
    for alpha,w in ((32,'.5'),(32,'.75'),(48,'.75'),(64,'.75'),(96,'.75'),(128,'.75')):
        alpha=arb(alpha);w=arb(w)
        diag,rem,early,room=target(U,alpha,w,summary)
        print('alpha, width, diagonal, AFE remainder square, early, signed room',
              *(v.str(10) for v in (alpha,w,diag,rem,early,room)),flush=True)
        for factor in (1,2,4,8):
            d,j,b,price=block(factor*U.exp(),alpha,w)
            print('  N/T',factor,'D, lost, complete, forward off, remaining',
                  *(v.str(10) for v in (d,j,b,price,room-price)),flush=True)
