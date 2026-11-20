"""Space- and time-localized true Mertens estimates on the stationary rows."""
from math import gcd,prod,isqrt
from flint import arb,ctx
from quarter_diagonal import zq,primes
from quarter_weighted_mertens import weighted,bound


def euler(q,s,h):
    u=arb(3)/2;ps=primes(q*s)
    W=zq(u,q*s)/zq(2*u,q*s)
    C=W*prod(1/(1-arb(p)**(-h)) for p in ps)
    cap=1000
    for p in range(2,cap+1):
        if q*s%p and all(p%j for j in range(2,isqrt(p)+1)):
            C*=1+1/((1+arb(p)**u)*(arb(p)**h-1))
    return C*(arb(cap)**(1-u-h)/((u+h-1)*(1-arb(cap)**(-h)))).exp()


def bins(q,maximum):
    ps=primes(q);eta=arb(int(sum(gcd(k,q)==1 for k in range(q))))/q
    c=[prod(p-1 if k%p==0 else -1 for p in ps) for k in range(1,q+1)]
    unit=[int(gcd(k,q)==1) for k in range(1,q+1)]
    def osc(seq):
        pfx=0;lo=hi=arb(0);m=arb(sum(seq))/q
        for i,z in enumerate(seq,1):
            lo=lo.min(pfx-m*i);pfx+=z;hi=hi.max(pfx-m*i)
        return hi-lo+1
    d0=osc(unit);d1=osc([v*v for v in c])/q
    l=1;out=[]
    while l<=maximum:
        r=min(maximum,max(l,(9*l)//8))
        if r<50000:
            x=y=arb(0)
            for k in range(l,r+1):
                if unit[(k-1)%q]:x+=1/arb(k)
                y+=arb(c[(k-1)%q]**2)/(q*arb(k).sqrt())
        else:
            left=arb(l-1)
            x=eta*(arb(r)/left).log()+d0/left
            y=2*eta*(arb(r).sqrt()-left.sqrt())+d1/left.sqrt()
        out.append((arb(l),arb(r),x,y));l=r+1
    return out


def local(s=1,d0=100000,beta=arb('.008191074'),times=32,alphas=8):
    q=2310;U=arb(37);T=U.exp();w=arb('.75');alpha=arb(64)
    a=arb(1)/2;K=arb('2.25e12');ts=arb('1.5e12');D=arb('1.01')*T
    h=arb(10)**16;epsilon=arb('.006688')/h.log()
    sq=euler(q,s,arb('.5'));one=euler(q,s,arb(1));recip=weighted(s)
    # Ranges contain all possible k with s k the short raw index.
    maxk=int(((q*2*T/(2*arb.pi()*d0)).sqrt()/s).upper().ceil().unique_fmpz())
    ranges=bins(q,maxk)
    ucharge=jcharge=arb(0)
    for i in range(times):
        l=ts*(D/ts)**(arb(i)/times);r=ts*(D/ts)**(arb(i+1)/times)
        # Include the tail as its own extraordinarily short effective window.
        for t0,t1 in ((l,r),) if i+1<times else ((l,r),(D,2*T)):
            mass=(t1-t0).min((t1*(t1/K)**256-t0*(t0/K)**256)/257)
            mass=mass.min((t0*(D/t0)**2048-t1*(D/t1)**2048)/2047)
            n0=q*t0/(2*arb.pi());n1=q*t1/(2*arb.pi())
            for j in range(alphas):
                a0=alpha*(-w+2*w*j/alphas).exp();a1=alpha*(-w+2*w*(j+1)/alphas).exp()
                y0=a0*n0.sqrt();y1=a1*n1.sqrt()
                v0=n0.sqrt()/a1;v1=n1.sqrt()/a0
                su=sj=arb(0)
                for k0,k1,H,R in ranges:
                    right=n1/(s*k0**2)
                    if right<s*d0:break
                    if not s*k0>y1:
                        low=(y0/k1).max(arb(s*d0));high=(y1/k0).max(arb(s*d0))
                        if not right<low:
                            err=arb('2.5')*sq/low.sqrt()
                            if not right<h:err+=4*epsilon*one*(high/h).min(arb(1)).sqrt()
                            su+=H*(2*beta).min(2*bound(low,recip)).min(err)*(y1/(s*d0*k0)).sqrt().min(arb(1))
                    if not s*k0>v1:
                        low=(v0/k1).max(arb(s*d0))
                        if not right<low:
                            err=3*sq/low.sqrt()
                            if not right<h:err+=epsilon*one*(2+(right/h).log())
                            sj+=R*(2*beta).min(2*bound(low,recip)).min(err)
                ucharge+=2*mass/alphas*su/(arb(s)**(1+a)*y0**a)
                jcharge+=2*mass/alphas*sj/(s*n0**a)
    return sq,one,ucharge,jcharge


if __name__=='__main__':
    ctx.prec=144
    for s in (1,13,17):
        beta=arb('.008191074') if s==1 else arb('.008191074')*(1+1/arb(s))+arb('1.16')/(s*(s-1))
        print('denominator',s,'half-power and unit Euler mass; true u-short, j-short',
              *(v.str(12) for v in local(s,beta=beta)),flush=True)
