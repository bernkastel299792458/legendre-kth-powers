"""Stieltjes convolution envelopes for the bulk fourth-moment diagonal."""
from functools import lru_cache
from fractions import Fraction
from itertools import combinations
from math import gcd,prod
from flint import arb,arb_poly,ctx


@lru_cache(maxsize=None)
def envelopes(Z,precision):
    d=arb(1)/3
    c=(arb.const_euler()+arb(2).log()+arb(3).log()/2)/3
    z=arb(Z).log()
    H=d*z+c
    k=arb(4)/3
    error=k*(2*H+k/Z)/Z
    h=m1=m2=arb(0)
    for n in range(1,Z+1):
        if gcd(n,6)==1:
            u=arb(1)/n
            mass=u*(2*h+u)
            t=arb(n).log()
            m1+=mass*t
            m2+=mass*t*t
            h+=u
    actual=h*h
    top,bottom=H*H+error,H*H-error
    assert 0<bottom<=actual<=top
    assert H>d # Error function decreases to the right of the cutoff.
    upper=(top,m1+(top-actual)*z,m2+(top-actual)*z*z)
    lower=(bottom,m1*bottom/actual,m2*bottom/actual)
    return d,H,z,upper,lower


def convolution(ell,d,H,z,masses):
    m0,m1,m2=masses
    l=ell-z
    p=ell-2*z
    mixed=2*(2*H*d*(m0*l-m1)+d*d*(m0*l*l-2*m1*l+m2))
    bulk=2*H*H*d*d*p*p+arb(4)/3*H*d**3*p**3+(d**4/6)*p**4
    return m0*m0+mixed+bulk


def bulk_bound(U,ell,old,Z=48,primes=(5,7,11)):
    d,H,z,upper,lower=envelopes(Z,ctx.prec)
    cut=prod(primes)*Z*Z
    Tcut=2*arb.pi()*cut**2
    if not Tcut < U.exp():
        return old, arb(0)
    replacement=arb_poly()
    for count in range(len(primes)+1):
        sign=(-1)**count
        moments=upper if sign==1 else lower
        for ps in combinations(primes,count):
            m=prod(ps)
            replacement+=(arb(sign)/(m*m))*convolution(ell-arb(m).log(),d,H,z,moments)
    ucut=Tcut.log()
    # Below Tcut we can use a simple harmonic bound for the true bulk and
    # an absolute bound for the continued polynomial eventually integrated.
    original=(1+arb(cut).log()/3)**4
    correction=original+sum(abs(v)*ucut**j for j,v in enumerate(replacement.coeffs()))
    return replacement, correction*Tcut*(-U).exp()


def rational(v):
    return arb(v.numerator)/v.denominator


@lru_cache(maxsize=None)
def tail_integrals(h,mode,R,precision):
    # Every interval [a,b) below belongs to t=y/s.  'cross' additionally
    # multiplies by H_A(t), and begins at t=1.
    from six_energy import R as residues
    bands={1:[],2:[(1,2,-1)],3:[(1,3,-1)],6:[(1,2,-1),(3,6,1)]}
    restricted=mode=="far"
    ranges=[(a,b,s if restricted else 1,r)
            for r in range(1,7) if not restricted or gcd(r,6)==1
            for a,b,s in bands[gcd(h*r,6)]]
    beyond=abs(sum((arb(s)/6*(arb(b)/a).log() for a,b,s,_ in ranges),arb(0)))
    beyond+=sum((arb(1)/(R*a) for a,_,_,_ in ranges),arb(0))
    events={Fraction(1,6):Fraction(0),Fraction(1):Fraction(0),Fraction(R):Fraction(0)}
    for a,b,s,r in ranges:
        for n in range(r,6*R+1,6):
            for t,v in ((Fraction(n,b),Fraction(s,n)),(Fraction(n,a),Fraction(-s,n))):
                if t<=R:
                    events[t]=events.get(t,Fraction(0))+v
    if mode=="cross":
        for n in range(1,R+1):
            if gcd(n,6)==1:
                events.setdefault(Fraction(n),Fraction(0))
    running=harm=Fraction(0)
    I=err=arb(0)
    points=sorted(events)
    for l,u in zip(points,points[1:]):
        running+=events[l]
        if l.denominator==1 and gcd(l.numerator,6)==1:
            harm+=1/l
        if mode=="cross":
            if l<1:
                continue
            val=rational(harm*running)
        else:
            val=rational(running*running)
        assert val>=0
        I+=val*rational(u/l).log()
        # At most two units of counting discrepancy in each residue type.
        err+=2*val*rational(u)
    return beyond,arb(len(residues[h]))/6*I,err


def ratio_bound(U,ell,near,away,R=96):
    from six_energy import R as residues,tails
    cut=10**6
    Tcut=2*arb.pi()*cut**2
    if not Tcut<U.exp():
        return near,away,arb(0)
    z=arb(R).log()
    a6=arb(6).log()
    d=arb(1)/3
    C,_,_,exc=tails(ctx.prec)
    ns=arb_poly()
    fs=arb_poly()
    for h,rs in residues.items():
        offset=sum(arb(1)/a for a in rs)
        total=offset+(arb(len(rs))/6)*(ell-z)
        small,I,error=tail_integrals(h,"near",R,ctx.prec)
        ns+=2*(a6*(small**2*total+I+error/cut)+C[h]**2*exc[False,h])
        if h!=1:
            small,I,error=tail_integrals(h,"far",R,ctx.prec)
            fs+=2*(1+d*(ell+a6))*(small**2*total+I+error/cut)
    small,I,error=tail_integrals(1,"cross",R,ctx.prec)
    masses=(1+d*z)*(1+d*(ell-z))+d*((ell-z)+(d/2)*(ell-z)**2)
    ns+=4*(d*a6*(small*masses+I+error/cut)+C[1]*(1+d*ell)*exc[True,1])
    ucut=Tcut.log()
    diff=near+away-ns-fs
    correction=sum(abs(v)*ucut**j for j,v in enumerate(diff.coeffs()))*Tcut*(-U).exp()
    return ns,fs,correction


def fourth(U):
    from off_fourth import off_bound
    from six_energy import fourth as original_fourth
    return original_fourth(U,off_bound=off_bound,bulk_bound=bulk_bound,ratio_bound=ratio_bound)


if __name__=="__main__":
    ctx.prec=160
    print("complete fourth constant at 40",fourth(arb(40)).str(16),flush=True)
