"""Upper bound on the undiscounted high Selberg norm after removing Q primes."""
from math import gcd

from flint import arb, ctx

from variance import smooth_values


def direct_high(U, delta, W, logh, q, nmax=768):
    """A drop-in high_base, to be multiplied by Y^-e*zeta(2+l)/zeta(2)."""
    upper_e = 2*delta/U
    y0 = (U+logh).exp()
    if not (0<upper_e and upper_e<=arb(".1") and W>0 and logh<0 and y0>1 and nmax>=16):
        raise ValueError("parameters beyond the high-moment domain")
    _, primes = smooth_values(q, 1)
    eta, product_max = arb(1), arb(1)
    for p in primes:
        eta *= 1-arb(1)/p
        product_max *= 1-arb(p)**(-2-upper_e)
    discrepancy = arb(2**len(primes))
    mu = [1]*(nmax+1)
    prime = [True]*(nmax+1)
    for p in range(2,nmax+1):
        if not prime[p]:
            continue
        for n in range(p,nmax+1,p):
            mu[n] *= -1
            if n>p:
                prime[n]=False
        for n in range(p*p,nmax+1,p*p):
            mu[n]=0
    finite=[(arb(n).log(),mu[n]) for n in range(1,nmax+1) if mu[n] and gcd(n,q)==1]
    nlog=arb(nmax).log()
    log_tail=(1+nlog)/nmax
    S=arb(6)
    head=[-S+S*i/96 for i in range(97)]
    transition=[W*i/192 for i in range(193)]
    best=arb(0)
    for j in range(8):
        l,u=upper_e*j/8,upper_e*(j+1)/8
        ds=[]
        for v in [2+l,2+u]:
            z=v.zeta()
            for p in primes:
                z*=1-arb(p)**(-v)
            ds.append(1/z)
        weights=[]
        flow,fhi=arb(0),arb(0)
        for t,m in finite:
            wlo,whi=(-(2+u)*t).exp(), (-(2+l)*t).exp()
            if m<0:
                wlo,whi=-whi,-wlo
            weights.append((t,wlo,whi,m))
            flow+=wlo*t
            fhi+=whi*t
        flow-=log_tail
        fhi+=log_tail

        def rest(a,b):
            trivial=arb("1.2")*(-(1+l)*a).exp()
            if a>=nlog:
                return -trivial,trivial
            low,high=-log_tail,log_tail
            for t,wlo,whi,m in weights:
                if t<a:
                    continue
                bot,top=(t-b).max(arb(0)),(t-a).max(arb(0))
                low+=wlo*(bot if m>0 else top)
                high+=whi*(top if m>0 else bot)
            return low.max(-trivial),high.min(trivial)

        def mass(a,b):
            factor=(-(2+(u if a<0 else l))*a).exp()
            return (eta*(b.exp()-a.exp())+discrepancy/y0)*factor

        value=arb("1.2")**2*(1+(-W).exp())**2
        value*=(eta+discrepancy*S.exp()/y0)*(-(1+l)*S).exp()
        for a,b in zip(head,head[1:]):
            lo1,hi1=rest(-b,-a)
            lo2,hi2=rest(W-b,W-a)
            amplitude=abs(lo1-hi2).max(abs(hi1-lo2))
            value+=mass(a,b)*amplitude**2
        for a,b in zip(transition,transition[1:]):
            lo,hi=rest(W-b,W-a)
            minimum=a*ds[0]+flow-hi
            maximum=b*ds[1]+fhi-lo
            value+=mass(a,b)*abs(minimum).max(abs(maximum))**2
        value+=(eta/(1+l)+discrepancy/y0)*(-(1+l)*W).exp()*(W*ds[1])**2
        best=best.max(value)
    return arb(2).zeta()*product_max*best/((logh).exp()*W**2)


if __name__=="__main__":
    ctx.prec=160
    for q in [1,2,6,30,210]:
        print(q,direct_high(arb(49),arb(".9"),arb("10.7"),arb("-4.85"),q).str(14),flush=True)
