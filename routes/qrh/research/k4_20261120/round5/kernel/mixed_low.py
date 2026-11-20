"""Mellin certificate for a convex combination of two tapers with the same head Y."""

import argparse
from math import gcd
from pathlib import Path
import sys

from flint import acb, arb, ctx

research = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(research / "round4" / "density"))
from mellin_low import mellin_low_rows
from variance import smooth_values


def _continuous(l, u, pieces, primes, eta, reciprocal_width):
    """A rectangle majorant, including the integral beyond height 100."""
    plogs = [arb(p).log() for p in primes]
    integer_logs = [arb(n).log() for n in range(1,17)]
    def box(a, b, depth=0):
        z = acb((l/2).union(u/2), a.union(b))
        sigma = 1+z
        den = arb(1)
        for lp in plogs:
            den *= abs(1-(-sigma*lp).exp()).lower().max(arb(0))
        # Combine the complex amplitudes before taking the absolute value.
        amplitude = -sum((weight_over_width*(-width*z).expm1()
                          for width,weight_over_width in pieces), acb(0))
        radius2 = (l/2)**2+a*a
        if b <= arb(1)/4:
            regular = (-z*integer_logs[-1]).exp()
            for ln in integer_logs[:-1]:
                regular += z*(-sigma*ln).exp()
            regular += z*(-sigma*integer_logs[-1]).exp()/2
            error = abs(z*sigma)*(1+abs(2+z)/2)/(12*16**2)
            den *= abs(regular).lower()-error
            num = arb(1)
            if radius2 > 0:
                num = num.min(abs(amplitude)/radius2.sqrt())
        else:
            den *= abs(sigma.zeta()).lower()*radius2
            num = abs(amplitude)
        if not den > 0:
            if depth >= 12:
                raise ArithmeticError("could not enclose mixed reciprocal zeta")
            m = (a+b)/2
            return box(a,m,depth+1)+box(m,b,depth+1)
        return (b-a)*(num.upper()/den.lower())**2

    total = arb(0)
    for start,end,subdiv in ((0,1,512),(1,4,128),(4,12,32),(12,100,16)):
        for i in range(start*subdiv, end*subdiv):
            total += box(arb(i)/subdiv,arb(i+1)/subdiv)
    at = arb(100)
    log_at = at.log()
    total += 4*(arb("4.339")*reciprocal_width/eta)**2*(
        log_at**2/3+2*log_at/9+arb(2)/27)/at**3
    if not total.is_finite():
        raise ArithmeticError("nonfinite mixed Mellin integral")
    return total/arb.pi()


def _unit_discrepancy(q):
    """Oscillation of the counting error, using both limits at each unit."""
    units = [n for n in range(1,q+1) if gcd(n,q)==1]
    phi = len(units)
    right = max(q*(j+1)-phi*n for j,n in enumerate(units))
    left = min(q*j-phi*n for j,n in enumerate(units))
    return arb(right-left)/q


def mixed_low_rows(U, delta, W0, W1, theta, logh, q, cells=16, tight=False, first=0):
    """Bound S_Q(1+e)/(Y^-e log T) in cells with indices first,...,cells-1."""
    U,delta,W0,W1,theta,logh = map(arb,(U,delta,W0,W1,theta,logh))
    if not (U>0 and delta>0):
        raise ValueError("the height and shift must be positive")
    e0, ly = 2*delta/U, U+logh
    if not (0 < e0 and e0 <= arb(".1") and ly > 16 and
            W0 > 0 and W1 > 0 and (theta.is_zero() or W1 >= W0) and
            0 <= theta and theta <= 1 and 0 <= first < cells):
        raise ValueError("low norm requires ordered positive widths and a convex combination")
    if not tight and (theta.is_zero() or (W1-W0).is_zero()):
        return mellin_low_rows(U,delta,W0,logh,q,cells)[first:]
    if not tight and (1-theta).is_zero():
        return mellin_low_rows(U,delta,W1,logh,q,cells)[first:]
    pieces = tuple((w,coef/w) for w,coef in ((W0,1-theta),(W1,theta)) if not coef.is_zero())
    reciprocal_width = sum(x for _,x in pieces)
    _,primes = smooth_values(q,1)
    eta,zhalf,zxi = arb(1),arb(1),arb(1)
    xi = 1-1/(12*arb(10).log())
    for p in primes:
        eta *= 1-arb(1)/p
        zhalf /= 1-arb(p)**(-arb(1)/2)
        zxi /= 1-arb(p)**(-xi)
    g0 = arb(3).sqrt()*(arb(2).sqrt()-1)/2 if 2 in primes else arb(1)
    g1 = arb("1.4378")*(1-arb(2)**(-xi)) if 2 in primes else arb(1)
    A = arb(".0336")*g1*arb(2)**e0*zxi
    H0 = (arb("4.86")*g0+arb("2.93")+arb("5.17")*e0)*zhalf*arb(2)**e0
    H1 = arb("2.83")*e0*zhalf*arb(2)**e0
    # The common residual R(s) is shared. Each shifted residual has a
    # different exponential factor e^(-width/2).
    c0 = c1 = arb(0)
    for width, coeff in pieces:
        decay = (-width/2).exp()
        c0 += coeff*(H0*(1+decay)+H1*width*decay)
        c1 += coeff*H1*(1+decay)
    bmax = 1+2/eta
    discrepancy = _unit_discrepancy(q) if tight else arb(2**len(primes))
    variation = discrepancy*(bmax**2+2*bmax*(1+reciprocal_width))
    head_and_error = None
    for j in (range(32,76) if tight else (40,)):
        alpha = arb(j)/100
        S = (1-alpha)*ly
        exponent = e0-alpha*(1+e0)
        if not (S > arb(15).log() and exponent < 0):
            continue
        h = c0+c1*S
        head = (2*A*reciprocal_width*(1/S+1/ly**2).sqrt()
                +(-S/2).exp()*(h*h+2*c1*h+2*c1**2).sqrt())**2
        candidate = head+variation*(exponent*ly).exp()
        head_and_error = candidate if head_and_error is None else head_and_error.min(candidate)
    if head_and_error is None:
        raise ValueError("no admissible splitting index for the discrete transfer")

    out = []
    for i in range(first,cells):
        l,u = e0*i/cells, e0*(i+1)/cells
        moment = _continuous(l,u,pieces,primes,eta,reciprocal_width)
        factor = arb(1)
        for p in primes:
            factor *= 1-arb(p)**(-1-u)
        factor *= (1+u*(arb(1)/2+(1+u)/12))/(2*delta)
        out.append(factor*(eta*moment+head_and_error))
    return out


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--U",default="41")
    cli.add_argument("--delta",default=".92")
    cli.add_argument("--w0",default="8.5")
    cli.add_argument("--w1",default="12")
    cli.add_argument("--theta",default=".3")
    cli.add_argument("--logh",default="-3.5")
    cli.add_argument("--q",type=int,default=210)
    cli.add_argument("--cells",type=int,default=16)
    cli.add_argument("--compare",action="store_true")
    cli.add_argument("--tight",action="store_true")
    args=cli.parse_args()
    ctx.prec=160
    U,delta,w0,w1,theta,logh=map(arb,(args.U,args.delta,args.w0,args.w1,args.theta,args.logh))
    rows=mixed_low_rows(U,delta,w0,w1,theta,logh,args.q,args.cells,tight=args.tight)
    print("mixed low rows",*(x.str(11) for x in rows),flush=True)
    if args.compare:
        first=mellin_low_rows(U,delta,w0,logh,args.q,args.cells)
        second=mellin_low_rows(U,delta,w1,logh,args.q,args.cells)
        separate=[((1-theta)*x.sqrt()+theta*y.sqrt())**2 for x,y in zip(first,second,strict=True)]
        print("mixed / separate Minkowski",*((x/y).str(9) for x,y in zip(rows,separate,strict=True)))
