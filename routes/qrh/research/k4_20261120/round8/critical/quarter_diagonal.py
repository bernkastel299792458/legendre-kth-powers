"""Positive and signed diagonal bounds for the three-quarter-line two-branch AFE."""
from functools import lru_cache
from math import gcd,isqrt,prod

from flint import arb,ctx


def primes(q):
    ps=[p for p in range(2,q+1) if q%p==0 and all(p%a for a in range(2,isqrt(p)+1))]
    assert prod(ps)==q
    return ps


def zq(s,q):
    return s.zeta()*prod(1-arb(p)**(-s) for p in primes(q))


def kernel_product(q,a,eps):
    # gcd is unrestricted; the two coprime quotients have disjoint supports.
    s=1+(a-eps)/2
    assert s>1
    return zq(1+a,q)*zq(s,q)**2/zq(2*s,q)


def full(U,lh,W,q,a):
    Y=(U+lh).exp()
    def pk(b):return (-(b*W).min(arb(2))).exp()*((2/b).min(W)/W)**2
    area=2*(1-(1+a*W)*(-a*W).exp())/(a**3*W**2)
    eta=prod(1-1/arb(p) for p in primes(q))
    pref=0;high=low=arb(0)
    for j in range(q):
        pref+=int(gcd(j+1,q)==1)
        v=pref-eta*(j+1);high=high.max(v);low=low.min(v-eta)
    disc=(high-low+1)
    best=(area+pk(a))*kernel_product(q,a,arb(0))
    for n in range(1,10):
        e=a*n/10
        x=eta*area*kernel_product(q,a,arb(0))
        x+=disc*pk(a)**(1-e)*pk(1+a)**e*Y**(-e)*kernel_product(q,a,e)
        best=best.min(x)
    return best*Y**(-a)


@lru_cache(None)
def prime_divisors_and_mu(q,cut):
    small=list(range(cut+1))
    for p in range(2,isqrt(cut)+1):
        if small[p]!=p:continue
        for n in range(p*p,cut+1,p):
            if small[n]==n:small[n]=p
    return small


def signed(q,a,cut=262144):
    small=prime_divisors_and_mu(q,cut)
    scale=2**96
    cumulative=[0]*(cut+1)
    total=arb(0)
    for k in range(1,cut+1):
        if gcd(k,q)!=1:continue
        n=k;ds=[(1,1)];sgn=1
        while n>1:
            p=small[n];n//=p
            if n%p==0:sgn=0;break
            ds+= [(d*p,ph*(p-1)) for d,ph in ds]
            sgn=-sgn
        if not sgn:continue
        w=(sgn*scale)//k
        pfx=sum(ph*cumulative[d] for d,ph in ds)
        # Truncation error of each prefix is <= cut/scale;
        # sum_{d|k} phi(d)=k.
        total+=arb(2*sgn*pfx+scale)/scale*arb(k)**(-1-a)
        for d,_ in ds:cumulative[d]+=w
    total+=2*arb(cut)**2/scale
    # For max(d,e)>cut bound all gcds g and coprime quotients by positives.
    eta=sum(gcd(i,q)==1 for i in range(q))
    prefix=[0]
    for n in range(1,q+1):prefix.append(prefix[-1]+int(gcd(n,q)==1))
    def units(n):return (n//q)*eta+prefix[n%q]
    count=[];mass=[];H=[]
    NN=70
    for i in range(NN):
        base=2**i
        c=units(2*base-1)-units(base-1)
        count.append(c)
        mass.append(c*arb(base)**(-1-a))
        H.append((H[-1] if H else arb(0))+arb(c)/base)
    tail=arb(0)
    for i,vg in enumerate(mass):
        for j,vy in enumerate(mass):
            if 2**(i+j+2)>cut:tail+=vg*vy*H[j]
    B=arb(2**NN-1)
    tail+=zq(1+a,q)*B**(-a)*((1+B.log())/a+1/a**2)
    tail+=B**(-a)/a*(1+1/a+1/a**2)
    return total,2*tail


def diagonals(U,lh,W,alpha,q=2310,cut=262144,summary=None):
    a=arb(1)/2
    T=U.exp();Y=(U+lh).exp();X=Y*W.exp();pi=arb.pi()
    assert Y>cut
    eta=prod(1-1/arb(p) for p in primes(q))
    s0,tail=signed(q,a,cut) if summary is None else summary
    upper=s0+tail
    y=alpha*(q*T/(2*pi)).sqrt();N=q*T/(2*pi)
    lead=eta/a*upper*y**(-a)/(1-a/2)
    pref=0;disc=arb(0)
    for j in range(q):
        v=pref-eta*j
        disc=disc.max(abs(v)).max(abs(v-eta))
        pref+=int(gcd(j+1,q)==1)
    C=(2*disc).max(zq(1+a,q)+eta/a)
    direct=None
    for k in range(1,20):
        e=a*k/20
        cost=C*y**(-a-e)*kernel_product(q,a,e)/(1-(a+e)/2)
        direct=cost if direct is None else direct.min(cost)
    K=prod(1+(p-2)*arb(p)**a for p in primes(q))/(q*a)
    # Exact short prefix; integral upper for the positive harmonic remainder.
    cap=65536
    harm=sum((1/arb(k) for k in range(1,cap+1) if gcd(k,q)==1),arb(0))
    harm+=eta*(X/cap).log()+2*disc/cap
    ref=K*zq(1+a,q)*harm**2*N**(-a)/(1-a)
    true=full(U,lh,W,q,a)
    ybar=arb("1.01")*2048/2047
    return tuple(ybar*T*v for v in (true,lead,direct,ref,(true.sqrt()+(lead+direct).sqrt())**2,lead+ref))


def signed_target(U,lh,W,alpha,out,q=2310,target=arb("1.75e11")):
    """Sufficient single signed, finite non-diagonal bound at T=exp(U)."""
    T=U.exp();D=arb("1.01")*T;X=T*(lh+W).exp()
    sigma=arb(3)/4;pi=arb.pi();v=arb(q).sqrt()*alpha
    tc=(2*pi*(v.max(q/v))**2).max(arb(1000))+1
    K=arb(3000175332800)/5;m=2048
    assert 1000<=tc<K<D and T>arb(10)**15
    c=arb(0)
    for d in range(1,q+1):
        if q%d==0:
            c+=16*v**(1-sigma)/d if d<v else 11*v**(-sigma)
    c*=(2*pi)**(sigma/2)
    M1=X**(1-sigma)/(1-sigma)
    eprod=prod(1+arb(p)**(-sigma) for p in primes(q))
    small=tc*((1+arb("1e-9"))*(tc+2)**2/K**2)**2*(
          12*(tc+2)**(1-sigma)*eprod*M1+1)**2
    huge=2*T*(D/(2*T))**m*(1+arb("1e-9"))*(
          12*(2*T+2)**(1-sigma)*eprod*M1+1)**2/(m-2)
    E=12*(1+X.log())*X.sqrt()+2*M1**2/arb(2).log()
    mean=zq(2*sigma,q)*D**(1-sigma)*(1/(1-sigma)+1/(m+sigma-1))
    rem=c**2*arb("1.00001")*(mean+2*E*K**(-sigma))
    diagonal=(1+arb("1e-9"))*(out[-2]+out[-1])
    assert target>small+huge+rem
    room=((target-small-huge).sqrt()-rem.sqrt())**2-diagonal
    return small,huge,rem,diagonal,room


if __name__=="__main__":
    ctx.prec=144
    U=arb(37);lh=arb(-3);W=arb("9.5");q=2310
    s=signed(q,arb(1)/2)
    print("finite signed arithmetic form and upper tail",*(v.str(12) for v in s),flush=True)
    for a in (1,4,16,32):
        out=diagonals(U,lh,W,arb(a),q,summary=s)
        print("alpha",a,"full, common, direct and reflected remainders, two totals",
              *(v.str(10) for v in out),flush=True)
        costs=signed_target(U,lh,W,arb(a),out)
        print("  early, remote, AFE squared error, diagonal, admissible signed non-diagonal",
              *(v.str(11) for v in costs),flush=True)
