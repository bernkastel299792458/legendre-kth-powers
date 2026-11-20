"""Absolute bounds for complete shifted progression families at the AFE sample."""
from fractions import Fraction
from math import gcd
from flint import arb, ctx


T, D, X = arb(3*10**12), arb(3*10**11), arb(10**10)
sigma, r = arb(7)/8, arb(3)/4


def logarithmic_sum(s):
    assert s > 1
    return 1/(s-1)**2+1/(arb(1).exp()*s)


def product_mass(P, alpha, degree, h_exponent):
    q = 210
    rho = arb(8)/35
    density = Fraction(8,35)
    count = 0
    for j in range(q):
        count += gcd(j,q)==1
        assert abs(count-density*j)<2 and abs(count-density*(j+1))<2
    assert P>q**3
    small = [2,3,5,7]
    multiplicity, constant = arb(1), arb.const_euler()
    for p in small:
        multiplicity *= 1+arb(2)/p
        constant += arb(p).log()/(p-1)
    err = (arb(q)/P).sqrt()
    linear = rho**2*alpha/(2*degree)
    absolute = rho/degree*(rho*(P.log()/2+constant)+32*err)
    absolute += 4*rho*err+8*err**2
    return 2*multiplicity*(absolute*h_exponent.zeta()+linear*logarithmic_sum(h_exponent))


def bounds(P, c):
    alpha = arb(4)/3
    pi = arb.pi()
    m = 2*sigma+2*c
    v = m-1
    slope = D-1
    moment = 2**(v-1)*(v/2).gamma()+arb(9).exp()*arb(18).gamma_upper(v)/3**v
    assert m<18
    peak = ((2*m/arb(1).exp())**(m/2)).max(6**m*arb(-9).exp())
    cauchy = ((c**2).exp()/c+((c+r)**2).exp()/(c+r))/(2*pi.sqrt())
    radii = ((c/46)**2+arb(".023")).exp()*(1+(c/46).erf())
    # The integral density part, then the one-maximum cost of the progression.
    head = product_mass(P,alpha,c,r+(2-alpha)*c)
    last = product_mass(P,alpha,c+1,2*sigma+(2-alpha)*c-alpha)
    common = 2*X**r*(2*sigma).zeta()*radii*cauchy
    common *= (P*arb("2.3")*T/(2*pi*slope**2))**c*slope**(1-2*sigma)
    truncated = common*(moment*head+P/slope*peak*last)+arb("1e-18")
    actual = truncated+arb(".00001390")

    # Mellin estimate for the continuous comparison on the same h-dependent set.
    c2 = arb(13)/8
    assert sigma+c2==arb(5)/2 and r+2*c2==4
    assert ((c2*c2).exp()/c2+((c2+r)**2).exp()/(c2+r)) < 128
    assert arb(4)/3*(arb("1.001")/arb(".999"))**2*(arb(3)/4)**(-arb(1)/4) < arb("1.6")
    add = product_mass(P,alpha,c2,r+(2-alpha)*c2)
    # Integral of (1+2|u|)(3+2|u|)^3 exp(-.99 u^2) on the whole axis.
    poly = [27,108,144,80,16]
    # (1+2v)(3+2v)^3 = 27+108v+144v²+80v³+16v⁴.
    integral = sum(co*((arb(j)+1)/2).gamma()/arb(".99")**((arb(j)+1)/2)
                   for j,co in enumerate(poly))
    U = T/(2*pi)
    normalized = arb("1.6")*130*2*integral/(2*pi)**5+1
    continuum = (X/U)**r*(P/U)**c2*(2*sigma).zeta()*add*normalized+arb("1e-18")
    return truncated, actual, continuum, actual+continuum


if __name__ == "__main__":
    ctx.prec = 160
    rows = [(10**7, "2.9", ".00004276", ".000000402", ".00004316"),
            (3*10**7, "2.55", ".00059651", ".000002436", ".00059894"),
            (10**8, "2.15", ".009919", ".00001780", ".009937"),
            (2*10**8, "1.9", ".041345", ".00005609", ".041401")]
    for value, exponent, lattice_bound, continuum_bound, discrepancy_bound in rows:
        p, c = arb(value), arb(exponent)
        result = bounds(p,c)
        assert result[1]<arb(lattice_bound) and result[2]<arb(continuum_bound)
        assert result[3]<arb(discrepancy_bound)
        print("P",p.unique_fmpz(),"S* lattice",result[0].str(12),"true lattice",result[1].str(12),
              "continuous",result[2].str(12),"discrepancy",result[3].str(12))
    assert (10**9)**4 == (10**12)**3 and X**2 == 10**8*10**12
    assert arb(".009937")+arb(".27864") < arb(".28858")
