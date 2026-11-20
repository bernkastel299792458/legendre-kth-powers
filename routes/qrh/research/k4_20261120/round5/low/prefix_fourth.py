"""Fourth norm of a Riemann--Siegel sum between a fixed and a moving endpoint."""
from functools import lru_cache
from flint import arb,ctx


@lru_cache(maxsize=512)
def energy_upper(a,b):
    """Multiplicative energy of integers in [a,b], by counting nontrivial rectangles."""
    n=b-a+1
    if n<=0:
        return 0
    k=n-1
    trivial=2*n*n-n
    if k*k<a:
        return trivial
    extra=0
    for r in range(max(2,(a+k-1)//k),k+1):
        width=k//r
        extra+=(r*k//b)*width*(width+1)
    return trivial+2*extra


def half_cost(a,b,J):
    """Bound the unnormalized fourth integral on one half-window of length J."""
    if a>b:
        return arb(0)
    span=b*b-a*a
    energy=energy_upper(a,b)
    diag=J/a**2
    if not span:
        return diag*energy
    scale=arb(2)*b**2/a**2
    # Time support for each ordered quadruple is one interval. After
    # Cauchy in the product coefficients, only a scalar harmonic sum remains.
    pivot=min(span,int((scale/diag).lower().floor().unique_fmpz()))
    if pivot==span:
        off=pivot*diag
    elif pivot>0:
        off=pivot*diag+scale*(arb(span)/pivot).log()
    else:
        off=scale*(1+arb(span).log())
    return energy*(diag+2*off)


def prefix_norm(C,J):
    """Bound (1/2 integral over [C-J,C+J] of the moving error^4)^(1/4)."""
    if not (C>J and J>0):
        raise ValueError("positive integration window required")
    def cutoff(t):
        return (t/(2*arb.pi())).sqrt()
    center=cutoff(C).floor().unique_fmpz()
    if center is None:
        raise ArithmeticError("fixed cutoff crosses an integer")
    low=int(cutoff(C-J).lower().floor().unique_fmpz())+1
    high=int(cutoff(C+J).upper().floor().unique_fmpz())
    if low<1:
        raise ValueError("shell outside the positive integers")
    lower=half_cost(low,int(center),J)
    upper=half_cost(int(center)+1,high,J)
    return ((lower+upper)/2)**(arb(1)/4)


if __name__=="__main__":
    ctx.prec=192
    H=arb(3000175332800)
    for width in (5*10**7,10**9,10**10,4*10**10):
        C,J=H+arb(width)/2,arb("1.01")*width
        y0=(C/(2*arb.pi())).sqrt()
        l=((C-J)/(2*arb.pi())).sqrt()
        h=((C+J)/(2*arb.pi())).sqrt()
        naive=(1+(h-y0).max(y0-l))/l.sqrt()*J**(arb(1)/4)
        new=prefix_norm(C,J)
        print("width",width,"supremum cost",naive.str(12),"moving fourth norm",new.str(12))
