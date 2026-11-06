"""Separate 512-bit implementation of two round3 trapezoid budgets.

This does not import or call the certificate's analytic functions. It
checks the point used for the infinite theorem and the worst finite cell.
"""
import argparse
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT/'results'/'k4_round3_separate_audit.json'
COEFFICIENTS = (
    ('5.069','9.461','167.8'), ('6.046','9.168','162.6'),
    ('7.077','8.875','157.4'), ('8.185','8.582','152.2'),
    ('9.387','8.290','147.0'), ('10.70','7.997','141.9'),
    ('12.11','7.704','136.7'), ('13.66','7.411','131.5'),
    ('15.35','7.118','126.3'), ('17.21','6.826','121.1'),
    ('19.31','6.533','115.9'), ('21.77','6.240','110.7'),
)


def ball(value):
    value = Fraction(value)
    return arb(value.numerator)/value.denominator


def bound(left, right):
    la, lb = ball(left), ball(right)
    q = 1+(lb/4).exp()/4
    a, b = (q*16/7).log(), (q*16).log()
    assert a > arb('3000000000000').log()

    def integral(p, r):
        # Integrate the tangent majorant as a difference of exponentials.
        mid = (a+b)/2
        slope = p-1+r/mid
        assert not slope.contains(0)
        line = (r*(mid.log()-1)).exp()*((slope*b).exp()-(slope*a).exp())/slope
        decay = 2-p-r/b
        assert decay > 0
        tail = ((p-2)*b+r*b.log()).exp()/decay
        return (32*q/7)*line+(1024*q*q/7)*tail

    parts = [arb(0), arb(0), arb(0)]
    den = 65536
    for row, (c0, d0, e0) in enumerate(COEFFICIENTS):
        c, d, e = arb(c0), arb(d0), arb(e0)
        for i in range((16+row)*den//32, (17+row)*den//32):
            sigma = arb(i)/den
            weight = ((sigma-1)*la).exp()*(la/den).expm1()
            p = 3*(1-sigma)/(2-sigma)
            parts[0] += c*weight*integral(p, p+2)
            parts[1] += weight*d
            parts[2] += weight*e
    dpart, epart = parts[1]*integral(arb(0), arb(2)), parts[2]*integral(arb(0), arb(1))
    base = (-la/2).exp()*integral(arb(1), arb(1))
    eps = 4*(-la/4).exp()
    pp = (1+eps).sqrt()*(lb+(1+eps).log())**2*(-la/4).exp()/(7*arb(2).log())
    trivial = (-3*la).exp()/(1-(-2*la).exp())
    total = parts[0]+dpart+epart+base+pp+trivial
    assert total < 1
    integer = (total*10**24).ceil().unique_fmpz()
    assert integer is not None
    return dict(left=str(Fraction(left)), right=str(Fraction(right)),
                delta_ball=total.str(65),
                upper=str(Fraction(int(integer), 10**24)),
                components={name: value.str(50) for name, value in (
                    ('B1',parts[0]),('B2',dpart),('B3',epart),('baseline',base),
                    ('prime_powers',pp),('trivial',trivial))})


def compute():
    ctx.prec = 512
    point = bound('372','372')
    first = bound('372','5953/16')
    expected = ('991573975668198449189201/1000000000000000000000000',
                '124674249251496611837662/125000000000000000000000')
    # The second rational is the reduced upward rounding of 0.997393994... .
    for actual, target in zip((point, first), expected):
        assert Fraction(actual['upper']) == Fraction(target)
    return dict(status='TWO_BUDGETS_REPRODUCED', precision_bits=512,
                imported_certificate_functions=False, point=point, first_cell=first,
                scope='Separate numeric implementation; analytic validity is reviewed in the proof documents.')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify',action='store_true')
    args = parser.parse_args()
    result = compute()
    if args.verify:
        assert result == json.loads(OUTPUT.read_text(encoding='utf-8'))
    else:
        OUTPUT.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])


if __name__ == '__main__':
    main()
