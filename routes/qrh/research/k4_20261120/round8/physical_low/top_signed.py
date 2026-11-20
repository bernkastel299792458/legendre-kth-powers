"""Signed first rectangular top row, including its coprimality restriction."""
from flint import arb,ctx,fmpz
from fractions import Fraction
from math import gcd


def rational(q):
    return arb(q.numerator)/q.denominator


def constants(s,cut=2000):
    # Products C_s for the weighted Mobius convolution and its h dependence.
    one=arb(1)
    c=one; P=one
    for p in range(2,cut+1):
        if not fmpz(p).is_prime():continue
        x=arb(p)
        b=x**(-s)
        w=1+1/((x-1)*(x**s-1))
        ratio=1/(1-b+b/(x-1))
        c*=w
        P*=1+(ratio/(x-1))**2
    # Uniform p>cut; no need for an estimate on the prime counting function.
    ca=1/((one-one/cut)*(1-arb(cut)**(-s)))
    c*=(ca*arb(cut)**(-s)/s).exp()
    cP=1/((one-arb(cut)**(-s))*(1-one/cut))**2
    P*=(cP/cut).exp()
    return c*P.sqrt()


def top(L,C,n,hstar,cut_log,r=1):
    H=arb(3000175332800)
    x=arb(L).exp();z=arb(C)*(x/H).sqrt()
    G=z.log()+arb("1.331")
    assert arb("1.33258")-arb("2.44")/z.sqrt()>arb("1.331")
    T=z/(2*hstar);B=arb(cut_log).exp()
    assert B>1798118 and T>B and r in (0,1) and hstar>=1
    A=arb(".006688")/cut_log
    v=A*constants(arb(1))+(B/T).sqrt()*constants(arb(1)/2)
    rho=Fraction(1);prim=1
    for p in range(2,300):
        if not fmpz(p).is_prime():continue
        prim*=p
        if prim>z:break
        rho*=Fraction(p,p-1)
    assert prim>z
    eps=arb("2e-6");k=arb(n)*H/arb(C)**2*eps.exp()
    br=arb(3)/2 if r==0 else 2+arb(2).log()
    low=(v*br*(1+3*arb.pi()*k))**2
    tail=arb(2)**(2*r)*rational(rho)**2/hstar
    return (low+tail)/G**2,v,tail/G**2


def absolute_lower(L,C):
    H=arb(3000175332800);z=arb(C)*(arb(L).exp()/H).sqrt();b=z/2
    density=arb(1);q=1
    for p in (2,3,5,7):
        density*=(1-arb(1)/p)**2*(1+arb(2)/p);q*=p*p
    prime_tail=sum((arb(1)/p**2 for p in range(11,1001) if fmpz(p).is_prime()),arb(1)/1000)
    small=density*(b-q)**2
    bad=2*(b+1)*(b*prime_tail+z.sqrt()) + b*b*prime_tail+2*b*(1+z.log())+z
    gupper=z.log()+2+arb("2.44")/z.sqrt()
    return (small-bad)/(z*gupper)**2


def first_main_cost(L,C,count):
    H=arb(3000175332800);r=arb("1e-6");l=arb(L)
    c=l+(4*(-l/4).exp()).log1p()/2
    a=(1-arb("1e-12"))*H*(c-l)
    width=2*(arb.pi()-a);I=arb.pi()*a.sin()/a
    N=1024;area=arb(0)
    for j in range(1,N):
        v=width*j/N
        area+=(a.cos()-(a+v).cos())/(v*(2*a+v))
    area=(area+a.sin()/(4*a))*width/N+width**3/(144*N**2)
    factor=4*(c+r)*(3*r/2+c-l).exp()*area/I
    return factor*sum(top(L,C,n,10**7,21,1)[0] for n in range(1,count+1))


def exact_identity(z):
    # Independent exact exercise of the all-row identity on s=0,1,2,3.
    mu=[int(fmpz(k).moebius_mu()) for k in range(z+1)]
    phi=[int(fmpz(k).euler_phi()) for k in range(z+1)]
    G=sum((Fraction(mu[n]**2,phi[n]) for n in range(1,z+1)),Fraction())
    lg=[Fraction(0)]+[Fraction(mu[d]*d,phi[d])*sum((Fraction(mu[n]**2,phi[n]) for n in range(1,z//d+1)
                                                      if gcd(n,d)==1),Fraction()) for d in range(1,z+1)]
    for k in range(1,z+1):
        if not mu[k]:continue
        for s in range(4):
            a=sum((lg[d]/d**s for d in range(k,z+1,k)),Fraction())
            b=Fraction(0)
            for m in range(1,z//k+1):
                if gcd(k,m)>1 or not mu[m]:continue
                v=Fraction(1,phi[m])
                for p,_ in fmpz(m).factor():v*=1-Fraction(int(p))**(1-s)
                b+=v
            assert a==Fraction(mu[k],phi[k])*Fraction(k)**(1-s)*b
    for s in (1,2):
        total=sum((lg[i]*lg[j]*Fraction(gcd(i,j),i*j)**s for i in range(1,z+1)
                   for j in range(1,z+1)),Fraction())
        assert total>0
        if s==1:assert total==G

if __name__=="__main__":
    ctx.prec=160
    exact_identity(64)
    for n in (1,2,4,8,16,32):
        v,m,t=top("116",3000000,n,10**7,21,1)
        print(n,"coprime top primed",v.str(14),"weighted disc",m.str(9),
              "h tail",t.str(9),flush=True)

    absolute=absolute_lower("116",3000000)
    assert absolute>arb("1e-5")
    cost=first_main_cost("116",3000000,4)
    print("absolute top lower",absolute.str(15),"first four cost",cost.str(15),flush=True)
