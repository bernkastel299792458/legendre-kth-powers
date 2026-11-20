"""Explicit fourth moment obtained by expanding the moving Riemann--Siegel sum."""

from pathlib import Path
import sys

from flint import arb, arb_poly, ctx

spectrum = Path(__file__).resolve().parents[2] / "round2" / "spectrum"
sys.path.insert(0, str(spectrum))
from flat_window import A, check


def fourth_constant(U, phased=False, averaged=False, shifted=False):
    """M_2(T) <= constant*T*log(T)^4 for every T>=exp(U), U>=20."""
    check(U >= 20, "fourth moment height")
    # Upper bound on coprime harmonic pairs is b*log(x)^2+c*log(x)+c0.
    divisors = {1: 1}
    for p in (2, 3, 5, 7, 11, 13, 17, 19):
        divisors.update({p*d: -m for d,m in divisors.copy().items()})
    b = sum(arb(m)/d**2 for d,m in divisors.items())
    c = 2*sum((max(m,0)+max(-m,0)*arb(d).log())/d**2 for d,m in divisors.items())
    c0 = sum(arb(max(m,0))/d**2 for d,m in divisors.items())

    # Polynomial in log T, initially written in log sqrt(T/(2*pi)).
    u = arb_poly([0,1])
    ell = (u-(2*arb.pi()).log())*A("1/2")
    diagonal = b*ell**2+c*ell+c0
    diagonal += 2*(b*(ell**3*A("1/3")+ell**4*A("1/12"))
                   +c*(ell**2*A("1/2")+ell**3*A("1/6"))
                   +c0*(ell+ell**2*A("1/2")))
    if phased:
        gamma = arb.const_euler()
        c = 2*sum(m*(gamma-arb(d).log())/d**2 for d,m in divisors.items())
        c0 = sum(m*(gamma-arb(d).log())**2/d**2 for d,m in divisors.items())
        h = sum(arb(1)/d for d in divisors)
        diagonal = gamma**2*(b*ell**2+c*ell+c0)
        diagonal += 2*(b*(gamma*ell**3*A("1/3")+ell**4*A("1/12"))
                       +c*(gamma*ell**2*A("1/2")+ell**3*A("1/6"))
                       +c0*(gamma*ell+ell**2*A("1/2")))
        # Errors for H_{z/d} and for H_{Y/max(r,s)} have separate costs.
        diagonal += gamma**2*h*(2*ell+2*gamma+1)
        diagonal += 2*h*(ell+gamma)*(3+2*gamma)
        diagonal += 2*(1+ell)*(3+2*gamma)
    if averaged:
        # Each diagonal is present on [max(200,2*pi*m^2),T]. Integrate
        # its positive polynomial bound at the actual current height.
        antiderivative = diagonal
        derivative = diagonal
        for k in range(1, 5):
            derivative = derivative.derivative()
            antiderivative += (-1)**k*derivative
        lower = arb(200)*antiderivative(arb(200).log())
        diagonal = antiderivative+(-lower).max(arb(0))*(-U).exp()
    off = (8*(1+ell)*(1+2*ell)+16)*(1/(2*arb.pi()))
    if shifted:
        # If ab-cd=k and g=(a,c), then g divides k. Given a,c the
        # solutions b,d lie on one lattice line with at most
        # 1+Y*g/max(a,c) possible pairs in the box [1,Y]^2.
        off = (4*(1+2*arb.pi()**2/6)*(1+2*ell)+16)*(1/(2*arb.pi()))
    poly = diagonal+off
    # Coefficients of 1/log(T)^j that have negative sign can be omitted.
    d4 = sum(poly[i].max(arb(0))*U**(i-4) for i in range(5))

    # For 0<=t<=200, Euler summation gives |zeta|<=1+2|s|<=403.
    # For 200<=t<=T, the fourth power of the explicit RS remainder
    # is <= 2^4/t. Integrals occupy disjoint supports.
    remainder = 200*arb(403)**4/U.exp() + 16*U/U.exp()
    if phased:
        # Write z=e^{i theta_0(t)}D(t). The derivative bound on z^4
        # gives |integral z^4| <= 64*T, including four identical indices.
        # (2 Re z)^2=2|z|^2+2 Re(z^2); apply Minkowski in L^2.
        phase = 2*(d4.sqrt()+((d4+64/U**4)/2).sqrt())
        remainder = (200*arb(403)**4+81*U)/U.exp()
        return (phase.sqrt()+remainder**A("1/4")/U)**4
    # The original large-t inequality bounds |zeta| by 2|D|+error.
    return (2*d4**A("1/4")+remainder**A("1/4")/U)**4


def left_endpoint(U, W, logh, phased=False, averaged=False, shifted=False):
    """Upper bound for the rational-window integral of |zeta M-1|^(4/3)."""
    T = U.exp()
    order, v = 2048, A("1.01")
    ybar = v*order/(order-1)
    check(v>1 and order>1+4/U, "flat window")
    divisors = {1: 1}
    for p in (2,3,5,7,11):
        divisors.update({p*d:-m for d,m in divisors.copy().items()})
    density = sum(arb(m)/d**2 for d,m in divisors.items())
    offset = sum((max(m,0)-2*m*arb(d).log())/d**2 for d,m in divisors.items())
    cm_offset = density*(W/3+logh)+offset
    check(cm_offset>0 and T*logh.exp()>2310**2, "critical Möbius range")
    c1 = density+cm_offset/U
    taper = 2*(W+logh).exp()/W**2*(1-(1+W)*(-W).exp())
    hilbert = arb.pi()*(1+A("2/3")*A("6/5").sqrt()).sqrt()
    c2 = hilbert*((density*taper+16/T)/U+c1/(2*T))
    cm = c1*ybar+c2
    c4 = fourth_constant(U, phased=phased, averaged=averaged, shifted=shifted)
    c4 *= v**(1+4/U)*order/(order-1-4/U)
    return (c4**A("1/4")*cm.sqrt()+ybar**A("3/4")/U**A("3/2"))**A("4/3")


if __name__ == "__main__":
    ctx.prec=192
    for U in (A(30),A(54),A(56)):
        print(U, "fourth", fourth_constant(U).str(18))
        print(U, "phase fourth",fourth_constant(U,phased=True).str(18))
        print(U, "averaged phase fourth",fourth_constant(U,phased=True,averaged=True).str(18))
        print(U, "shifted correlations",fourth_constant(U,phased=True,averaged=True,shifted=True).str(18))
        print(U, "left", left_endpoint(U,A("10.7"),A("-4.85")).str(18))
