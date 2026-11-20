"""Centered Barban--Vehov right endpoint and matched critical-line endpoint."""

from pathlib import Path
import argparse
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "upper"))
from verify_far import A, check, detector_constants, height_moment


def mobius_up_to(n):
    primes = [True] * (n + 1)
    mu = [1] * (n + 1)
    for p in range(2, n + 1):
        if primes[p]:
            for k in range(p, n + 1, p):
                mu[k] *= -1
                primes[k] = False
            for k in range(p*p, n + 1, p*p):
                mu[k] = 0
    return mu


def low_head_energy(y0, n=2048):
    """Squared integral majorant for the log-average of the unsigned m envelope."""
    tail = (arb(8)/n).sqrt()
    energy = arb(8)/n
    increments = []
    m = arb(0)
    for j, mu in enumerate(mobius_up_to(n)[1:n], 1):
        m += arb(mu)/j
        increments.append(abs(m)*(arb(1)/j).log1p())
    for j in range(n-1, 0, -1):
        tail += increments[j-1]
        energy += tail**2*((arb(1)/j).log1p() + (j+1)/y0)
    return energy


def endpoints(U, delta, kap, W, logh):
    T, Z = U.exp(), (U-6).exp()
    half, pi = A("1/2"), arb.pi()
    m0 = (1+A("2/3")*A("6/5").sqrt()).sqrt()
    h, xh = logh.exp(), (logh+W).exp()
    y0 = T*h
    ep = 2*delta/U
    check(y0 > 10**12 and logh < 0 and W+logh > 0 and U>40, "height domain")
    # Fixed-square sieve for mu^2. Its count is <= density*t + 16.
    divisors = {1: 1}
    for prime in (2, 3, 5, 7, 11):
        divisors.update({prime*d: -v for d,v in divisors.copy().items()})
    density = sum(arb(v)/d**2 for d,v in divisors.items())
    offset = sum((max(v,0)-2*v*arb(d).log())/d**2 for d,v in divisors.items())
    c1 = density+(density*(W+logh)+offset)/U
    c2 = pi*m0*((2*density*xh/W**2+16/T)/U+c1/(2*T))
    # Uniform right-line mean-square S(1+e) and T*S(2+e), e=2delta/log T.
    energy = low_head_energy(y0)
    shape = 1+(1+y0.log())**-2+1/y0
    head = ((1+ep*W)*energy.sqrt()/W + 2*A(".011")*shape.sqrt())**2
    mid = ep.max(A("1.00303")/W + ep*(A(".00303")+ep/(1+ep)))
    discount = (-2*delta-ep*logh).exp()
    low = discount*((1/U+1/(2*delta))*(head+(W+1/y0)*mid**2)+(1+ep/y0)/U)
    # For v>=2, zeta(v)<=2, and sum(log(m)/m^2,m>=2)<1.
    high = 2*discount/h*(9+5/y0)/W**2
    k3 = pi*m0*low + (pi.sqrt()/(2*(2*kap).sqrt())+pi*m0/(2*T))*high/U
    # CS Corollary 5 and its left boundary proof preceding (42).
    V = U-6
    a1 = Z*(V-arb(2).log())**4/(2*pi**2)+A("34.842")*Z*(V-arb(2).log())**3+A("1.3897e16")
    a2 = (1-arb(2).log()/V)**4/(2*pi**2)+A("34.842")/V*(1-arb(2).log()/V)**3+A("9.5079e15")/(Z*V**4)
    a = 3/(4*kap)
    v = 2/(3*U)
    c = v*a/(1+a)
    check(0<c and c<1 and Z>10**10, "gamma and fourth-moment range")
    D = (v*((1+a).log()-a/(1+a))).exp()
    mass = A("7/6").gamma()/(1-c)**A("7/6")
    mean_root = A("5/3").gamma()/((1-c).sqrt()*A("7/6").gamma())
    integral = D*mass*(c1*a.sqrt()*mean_root+c2)**A("2/3")
    k1 = (2*a2*a.sqrt())**A("1/3")*integral
    k1 += (2*a1/T)**A("1/3")*(c2+Z*c1/T)**A("2/3")/U**A("4/3")
    k2 = A(2)**A("1/3")*(a.sqrt()*pi.sqrt()/2+(Z/T)**3/a)
    H = arb(3*10**12)
    l0 = (kap*(1+((1+2*delta/U)/(4*T))**2)).exp()/(1-1/H)
    check(l0>1 and 9/y0.sqrt()<A("1/100"), "Littlewood right edge")
    return k1, k2, k3, l0, energy, low, high


def verify(anchor, W, logh, delta, kap, U):
    L = arb(anchor)
    k1,k2,k3,l0,energy,low,high = endpoints(U,delta,kap,W,logh)
    bands = detector_constants()
    knots = [arb(i)/1000 for i in range(650, 871)]+[A("7/8")]
    u1 = ((A("16/7"))*(1+(L/4).exp()/4)).log()
    check(u1>U, "moment validity at starting height")
    ratio = (k1+k2/U**2)/k3
    base = 2*((knots[0]-1)*L).exp()*height_moment(u1, arb(1), arb(1))
    check(knots[0]-1+A("1/4")+1/(4*u1)<0, "base decrease")
    jlog = A("15/14").log()
    outer = (11*((logh+W)/2).exp()).log()
    edge = 162*(-logh).exp()/(2*arb.pi()) + 2*(2+(arb(2).log()+6*outer)/jlog)
    edge += 18/jlog*height_moment(u1,arb(0),arb(1))
    previous, zm, ze = arb(0), arb(0), arb(0)
    for s,t in zip(knots,knots[1:]):
        p = 3*(1-s)/(2-s)
        low_nu = (2+4*delta/U)/(2-s+3*delta/U)
        high_nu = 2/(2-s)
        check(bands[0][0]<=low_nu and high_nu<=bands[-1][1], "detector range")
        cd = max(cap for lo,hi,cap in bands if not (hi<low_nu or lo>high_nu))
        k = 3*delta*(2*s-1)/(2-s)**2
        b = cd*l0**high_nu*k3*ratio**p
        b *= (ratio**(k/U)).max(arb(1))*(k*(1+U.log()/U)).exp()/(2*arb.pi())
        slope = ((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        jump = slope-previous
        check(jump>0, "positive slope jump")
        previous=slope
        zm += 2*jump*b*height_moment(u1,p,1+p)
        ze += 2*jump*edge
        check(t-1+2/L+p/4+(1+p)/(4*u1)<0, "main decreases")
        check(t-1+2/L+1/(4*u1)<0, "edges decrease")
    eps=4*(-L/4).exp()
    pp=A("8/7")*(1+eps).sqrt()*(L+eps.log1p())**2*(-L/4).exp()/(8*arb(2).log())
    check(2/L<A("1/4"), "prime powers decrease")
    total=base+zm+ze+pp+(-3*L).exp()/(1-(-2*L).exp())
    return dict(K1=k1,K2=k2,K3=k3,head_energy=energy,S1_over_U=low,T_S2=high,total=total)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",type=int,default=267)
    for name,value in (("width","9.25"),("logh","-2.45"),("delta",".65"),("kappa",".105"),("U","64")):
        cli.add_argument("--"+name,default=value)
    args=cli.parse_args()
    ctx.prec=192
    out=verify(args.anchor,A(args.width),A(args.logh),A(args.delta),A(args.kappa),A(args.U))
    for label,value in out.items():
        print(label,value.str(18))
    check(out["total"]<1,"point budget")
