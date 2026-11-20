"""Fourth moment of zeta(s)(1-2**(-s)) on the critical line.

At each Riemann--Siegel cutoff y, the coefficients of the Euler-filtered
main polynomial are 1 on odd n<=y and -1 on even y<n<=2y. Each of these
fixed-index activity sets is one time interval. See SIEVED.md.
"""

from itertools import product
from fractions import Fraction
from math import gcd
from flint import arb, arb_poly, ctx


def _fourth_harmonic(U, primes):
    coefficients = {Fraction(1): arb(1)}
    for p in primes:
        c = 1/arb(p).sqrt()
        factors = [c**2, 2*c*(1+c**2), 1+4*c**2+c**4, 2*c*(1+c**2), c**2]
        coefficients = {r*Fraction(p)**k: a*factors[k+2]
                        for r,a in coefficients.items() for k in range(-2,3)}
    total = arb(0)
    for r, weight in coefficients.items():
        ar = arb(r.numerator)/r.denominator
        if r>=1:
            cost = arb(64)
            if r>1:
                cost = cost.min(16/(arb.pi()*ar.log()))
        else:
            cost = None
            first = r.denominator//r.numerator+1
            for width in range(first,first+5):
                h = sum(arb(1)/k for k in range(1,width))
                log_width = arb(width).log()
                candidate = 16/(arb.pi()*(width*ar).log())
                candidate += 2*h**2*(arb.pi()**2/6+log_width*(1+U/2))
                candidate += (12*(1+U)+16)/(2*arb.pi())
                cost = candidate if cost is None else cost.min(candidate)
        total += weight*cost/U**4
    return total


def _constant(U, diagonal, off, e_bound, phase_primes):
    anti = diagonal
    derivative = diagonal
    for k in range(1, 5):
        derivative = derivative.derivative()
        anti += (-1)**k*derivative
    delta = (-200*anti(arb(200).log())).max(arb(0))*(-U).exp()
    poly = anti+delta+off
    d4 = sum(poly[i].max(arb(0))*U**(i-4) for i in range(5))
    error = e_bound*((200*arb(403)**4+16*U)*(-U).exp())**(arb(1)/4)/U
    ordinary = (2*d4**(arb(1)/4)+error)**4
    if not phase_primes:
        return ordinary
    h4 = _fourth_harmonic(U,phase_primes)
    main = (2*(d4.sqrt()+((d4+h4)/2).sqrt())).sqrt()
    error = e_bound*((200*arb(403)**4+81*U)*(-U).exp())**(arb(1)/4)/U
    return ordinary.min((main+error)**4)


def fourth_two(U, phased=False):
    """Upper coefficient of T*(log T)^4, uniformly for T>=exp(U), U>=20."""
    if not U >= 20:
        raise ValueError("U must be at least 20")
    u = arb_poly([0, 1])
    log2 = arb(2).log()
    ell = (u-(2*arb.pi()).log())*(arb(1)/2)
    hodd = 1+ell*(arb(1)/2)
    odd_energy = 1+2*ell+ell**2+ell**3*(arb(1)/6)+ell**4*(arb(1)/96)
    zeta2 = arb.pi()**2/6
    mixed_energy = hodd*(3*zeta2/4+(log2/2)*hodd)
    even_energy = (zeta2+log2*(1+ell))*(arb(1)/2)
    # Odd-odd products have disjoint support from the other two terms.
    diagonal = odd_energy+arb(14)/3*mixed_energy+7*even_energy
    # The entire support of the four index variables lies below 2Y.
    off = 4/(2*arb.pi())*(4*(1+2*zeta2)*(1+2*ell+2*log2)+16)
    e2 = 1+1/arb(2).sqrt()
    return _constant(U, diagonal, off, e2, [2] if phased else [])


def fourth_six(U, phased=False):
    """Same uniform coefficient for zeta(s)(1-2**(-s))(1-3**(-s))."""
    if not U>=20:
        raise ValueError("U must be at least 20")
    u = arb_poly([0, 1])
    ell = (u-(2*arb.pi()).log())*(arb(1)/2)
    y0 = (U/2).exp()/(2*arb.pi()).sqrt()
    assert y0>36
    zeta2 = arb.pi()**2/6
    d = arb(1)/3
    log6 = arb(6).log()
    h = 1+d*ell
    v = d*ell
    bulk = 1+4*v+4*v**2+arb(4)/3*v**3+arb(1)/6*v**4
    band = sum(arb(1)/j for j in range(1,6))
    mixed = 2*(5*band/6)*h*(4*zeta2/3+d*log6*h)
    tails = 2*band**2*(zeta2+log6*(1+ell+log6))
    # Use the parameter 2/3 in 2ab<=q*a^2+b^2/q.
    diagonal = bulk+arb(20)/3*mixed+arb(5)/2*tails

    densities = {1:d, 2:arb(1), 3:arb(1)/2, 6:arb(1)}
    shift_sum = arb(0)
    for i,j,k,l in product(densities,repeat=4):
        a, b = i*j, k*l
        alpha = densities[i].min(densities[j])
        beta = densities[k].min(densities[l])
        shift_sum += (alpha+1/y0)*(beta+1/y0)/gcd(a,b)
        shift_sum += alpha*beta*(2+abs((arb(a)/b).log()))/max(a,b)
        shift_sum += ((alpha/a+beta/b)*(1+(36*y0).log())+arb(1)/max(a,b))/y0
    e6 = (1+1/arb(2).sqrt())*(1+1/arb(3).sqrt())
    off = (4*shift_sum*(1+2*ell+2*log6)+16*e6**4)*(1/(2*arb.pi()))
    return _constant(U, diagonal, off, e6, [2,3] if phased else [])


if __name__ == "__main__":
    ctx.prec=192
    for height in [30,49,54,56]:
        print(height, fourth_two(arb(height)).str(18))
        print("six",height, fourth_six(arb(height)).str(18))
        print("phased", height, fourth_two(arb(height), phased=True).str(18),
              fourth_six(arb(height), phased=True).str(18))
