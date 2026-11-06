"""Historical 512-bit replay of the original 76-cell k=6 certificate; read-only.

Reads the pre-revision archive. For the current 94-cell certificate use
review_smooth_k6_refined.py.

This does not import certify_smooth_k6. It reconstructs source constants,
piecewise kernel, exponential weights, grids and tail from the review formulas.
It checks selected cells, not the entire continuous certificate by itself.
"""
from pathlib import Path
from fractions import Fraction
import json

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
ROWS = [
    ('5.069','9.461','167.8'), ('6.046','9.168','162.6'),
    ('7.077','8.875','157.4'), ('8.185','8.582','152.2'),
    ('9.387','8.290','147.0'), ('10.70','7.997','141.9'),
    ('12.11','7.704','136.7'), ('13.66','7.411','131.5'),
    ('15.35','7.118','126.3'), ('17.21','6.826','121.1'),
    ('19.31','6.533','115.9'), ('21.77','6.240','110.7'),
]


def rational(s):
    f = Fraction(s)
    return arb(f.numerator)/f.denominator


def floor(v):
    z = v.floor().unique_fmpz()
    if z is None:
        raise ValueError('Unresolved floor')
    return int(z)


def ceil(v):
    z = v.ceil().unique_fmpz()
    if z is None:
        raise ValueError('Unresolved ceiling')
    return int(z)


def replay(cell):
    la, lb = rational(cell['left']), rational(cell['right'])
    q = 1+(lb/6).exp()/6
    r1, r2 = arb(64)/31, arb(4096)/31
    H = arb(3000000000000)
    logH = H.log()

    def g(u):
        z = q/u.exp()
        if z >= 1/r1:
            return arb(1)
        if not z < 1/r1:
            raise ValueError('Unresolved first kernel branch')
        if z >= r1/r2:
            return r1*z
        if not z < r1/r2:
            raise ValueError('Unresolved second kernel branch')
        return r2*z*z

    candidate = arb(floor((q*r1).log()*32))/32
    start = candidate if candidate > logH else logH
    low = 2*(-la/2).exp()*H*logH*(1-g(logH))
    ds, es, terms = arb(0), arb(0), []
    for row in range(12):
        c, d, e = map(arb, ROWS[row])
        for j in range(64):
            s = arb((16+row)*64+j)/2048
            # Independent evaluation: expm1 instead of subtracting exponentials.
            w = ((s-1)*la).exp()*(la/2048).expm1()
            p = 3*(1-s)/(2-s)
            terms.append((w*c,p))
            ds += w*d
            es += w*e

    first = floor(32*start)+1
    end = max(ceil(((q*64).log()+12)*32),ceil((logH+12)*32))
    if str(Fraction(end,32)) != cell['height_end']:
        raise ValueError('Different height endpoint')
    prev, total = g(start), arb(0)
    for j in range(first,end+1):
        u = arb(j)/32
        # Independent power evaluation, rather than exp(p*(u+log(u)))*u^2.
        main = sum((co*(p*u).exp()*u**(p+2) for co,p in terms),arb(0))
        cumulative = (-la/2+u).exp()*u+main+ds*u*u+es*u
        cur = g(u)
        mass = prev-cur
        if not mass >= 0:
            raise ValueError('Unresolved positive mass')
        total += 2*cumulative*mass
        prev = cur

    U = arb(end)/32
    main_tail = arb(0)
    for co,p in terms:
        denominator = 2-p-(p+2)/U
        if not denominator > 0:
            raise ValueError('Invalid tail denominator')
        main_tail += co*((p-2)*U).exp()*U**(p+2)/denominator
    baseline = (-la/2-U).exp()*(U+1)
    dterm = ds*(-2*U).exp()*(U*U/2+U/2+arb(1)/4)
    eterm = es*(-2*U).exp()*(U/2+arb(1)/4)
    tail = 4*r2*q*q*(main_tail+baseline+dterm+eterm)
    eps = 6*(-la/6).exp()
    pp = (arb(32)/31)*(1+eps).sqrt()*(lb+(1+eps).log())**2
    pp *= (-la/3).exp()/(12*arb(2).log())
    trivial = 1/((3*la).exp()-la.exp())
    delta = low+total+tail+pp+trivial
    if not delta < rational(cell['delta_upper_rational']):
        raise ValueError('Saved rational bound does not enclose replay')
    if not arb(cell['delta_ball']).contains(delta):
        raise ValueError('Saved display ball does not contain replay')
    return dict(left=cell['left'],right=cell['right'],precision_bits=ctx.prec,
                delta_ball=delta.str(80),passed=True)


def main():
    ctx.prec = 512
    saved = json.loads((ROOT/'archive'/'k6_before_claude_revision_2026-11-06'
                        /'results'/'smooth_k6_certificate.json').read_text())
    if saved['sigma_denominator'] != 2048 or saved['height_denominator'] != 32:
        raise ValueError('This independent replay expects grids 2048 and 32')
    requested = [('167','168'),('178','357/2'),('357/2','179'),
                 ('179','180'),('395','400')]
    cells = {(c['left'],c['right']):c for c in saved['cells']}
    for key in requested:
        print(json.dumps(replay(cells[key])),flush=True)


if __name__ == '__main__':
    main()
