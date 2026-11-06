#!/usr/bin/env python3
"""Arb upper-sum certificate for QRH(7/8), k=4, log(x) in [400,700].

This checks numerical inequalities conditional on the documented analytic
lemmas and published CS v2 density input. It does not certify all n.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import time
from datetime import datetime, timezone, timedelta
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'results' / 'smooth_segment_certificate.json'
SOURCE = 'https://arxiv.org/html/2507.15184v2'
PRECISION = 160
# Corollary 1, Table 1, rows [i/32,(i+1)/32], i=16,...,27.
CS_ROWS = (
    ('5.069','9.461','167.8'), ('6.046','9.168','162.6'),
    ('7.077','8.875','157.4'), ('8.185','8.582','152.2'),
    ('9.387','8.290','147.0'), ('10.70','7.997','141.9'),
    ('12.11','7.704','136.7'), ('13.66','7.411','131.5'),
    ('15.35','7.118','126.3'), ('17.21','6.826','121.1'),
    ('19.31','6.533','115.9'), ('21.77','6.240','110.7'),
)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def a(q):
    q = Fraction(q)
    return arb(q.numerator) / q.denominator


def floor_cert(v):
    z = v.floor().unique_fmpz()
    require(z is not None, 'Arb cannot determine a unique floor')
    return int(z)


def ceil_cert(v):
    z = v.ceil().unique_fmpz()
    require(z is not None, 'Arb cannot determine a unique ceiling')
    return int(z)


def upper_decimal(v, digits=24):
    # The exact rational decimal is at or above the whole ball.
    scale = 10**digits
    n = ceil_cert(v * scale)
    return str(Fraction(n, scale)), format(n / scale, '.12g')


def kernel(q, u):
    z = q * (-u).exp()
    return arb(1).min(arb(15)/4*z).min(24*z*z).min(300*z*z*z)


def sigma_terms(la, denominator):
    require(denominator >= 32 and denominator % 32 == 0,
            'sigma denominator must be a positive multiple of 32')
    terms = []
    bsum = arb(0)
    esum = arb(0)
    width = arb(1)/denominator
    for i in range(denominator//2, 7*denominator//8):
        lo, hi = arb(i)/denominator, arb(i+1)/denominator
        row = (i*32)//denominator - 16
        c,d,e = (arb(v) for v in CS_ROWS[row])
        # sigma interval stays inside its closed source row.
        require(Fraction(i,denominator) >= Fraction(16+row,32), 'row lower')
        require(Fraction(i+1,denominator) <= Fraction(17+row,32), 'row upper')
        p = 3*(1-lo)/(2-lo)
        factor = la*width*((hi-1)*la).exp()
        terms.append((factor*c,p))
        bsum += factor*d
        esum += factor*e
    return terms, bsum, esum


def cumulative(la, u, terms, bsum, esum):
    # Upper bound for the weighted cumulative count at T=exp(u), T>=H.
    total = (-la/2+u).exp()*u
    v = u+u.log()
    main = arb(0)
    for coefficient,p in terms:
        main += coefficient*(p*v).exp()
    return total + u*u*(main+bsum) + u*esum


def certify_cell(left, right, sigma_denominator=1024, height_denominator=8):
    left, right = Fraction(left), Fraction(right)
    require(Fraction(400) <= left < right <= 700, 'L cell outside [400,700]')
    require(height_denominator > 0, 'height denominator must be positive')
    la, lb = a(left), a(right)
    q = 1+(lb/4).exp()/4
    logq = q.log()
    # Safe dyadic/rational start below the first departure from g=1.
    start_i = floor_cert((logq+(arb(15)/4).log())*height_denominator)
    start = arb(start_i)/height_denominator
    require(start > arb('3000000000000').log(), 'density height condition')
    require(kernel(q,start) == 1, 'first kernel value must be exactly 1')
    # The cubic term is active for t/q>=300/24=12.5.
    target = (arb(1800).log()+3*logq-la/8+60)/2
    end_i = max(ceil_cert(target*height_denominator),
                ceil_cert((logq+arb('12.5').log())*height_denominator))
    end = arb(end_i)/height_denominator
    require(end >= logq+arb('12.5').log(), 'tail does not start in cubic segment')
    terms, bsum, esum = sigma_terms(la,sigma_denominator)
    previous = kernel(q,start)
    finite = arb(0)
    for i in range(start_i+1,end_i+1):
        u = arb(i)/height_denominator
        current = kernel(q,u)
        difference = previous-current
        require(difference >= 0, 'unresolved sign of positive kernel mass')
        finite += 2*cumulative(la,u,terms,bsum,esum)*difference
        previous = current
    # Tail of 2*integral A(exp(u))*(-dg), including residual low-zero mass.
    # This uses QRH and N(t)<=t log(t), not a cutoff sum over high zeros.
    tail = 1800*q**3*(-la/8-2*end).exp()*(end/2+arb(1)/4)
    eps = 4*(-la/4).exp()
    logy = lb+(1+eps).log()
    # max(phi)/I=15/8; global psi-theta <=sqrt(Y)log(Y)^2/(2log2).
    pp = (arb(15)/8)*(1+eps).sqrt()*logy**2/(8*arb(2).log())*(-la/4).exp()
    trivial = (-3*la).exp()/(1-(-2*la).exp())
    delta = finite+tail+pp+trivial
    require(delta.is_finite(), 'nonfinite Arb enclosure')
    passed = bool(delta < 1)
    up, approx = upper_decimal(delta)
    return dict(left=str(left),right=str(right),passed=passed,
                delta_ball=delta.str(40),delta_upper_rational=up,
                delta_upper_approx=approx,
                finite_zero_ball=finite.str(35),height_tail_ball=tail.str(35),
                prime_power_ball=pp.str(35),trivial_ball=trivial.str(35),
                height_start=str(Fraction(start_i,height_denominator)),
                height_end=str(Fraction(end_i,height_denominator)),
                height_cells=end_i-start_i,sigma_cells=len(terms))


def verify_certificate(path=OUTPUT):
    """Replay saved cells and exact coverage without writing any file."""
    path = Path(path)
    saved = json.loads(path.read_text(encoding='utf-8'))
    require(saved['status'] == 'ALL_CELLS_PASSED', 'saved status')
    require(saved['k'] == 4 and saved['log_x_interval'] == ['400','700'],
            'saved target interval')
    script_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    require(saved['script_sha256'] == script_hash, 'script SHA256 mismatch')
    require(saved['source']['url'] == SOURCE, 'source version mismatch')
    require(saved['source']['constants'] == [list(row) for row in CS_ROWS],
            'source constants mismatch')
    require(saved['kernel'] == dict(M=2,R=['1','15/4','24','300'],
                                    max_over_mass='15/8'), 'kernel mismatch')
    precision = saved['precision_bits']
    require(isinstance(precision,int) and 100 <= precision <= 4096,
            'saved precision outside supported range')
    sigma_denominator = saved['sigma_denominator']
    height_denominator = saved['height_denominator']
    cells = saved['cells']
    require(cells and len(cells) == saved['number_of_cells'], 'cell count mismatch')
    require(Fraction(cells[0]['left']) == 400, 'left endpoint mismatch')
    require(Fraction(cells[-1]['right']) == 700, 'right endpoint mismatch')
    for previous,current in zip(cells,cells[1:]):
        require(Fraction(previous['right']) == Fraction(current['left']),
                'gap or overlap in saved L coverage')
    previous_precision = ctx.prec
    started = time.monotonic()
    try:
        ctx.prec = precision
        for cell in cells:
            replay = certify_cell(cell['left'],cell['right'],
                                  sigma_denominator,height_denominator)
            require(cell['passed'] is True and replay['passed'], 'cell failed replay')
            upper = Fraction(cell['delta_upper_rational'])
            require(0 < upper < 1, 'saved upper bound is not below one')
            require(Fraction(replay['delta_upper_rational']) <= upper,
                    'saved upper bound does not enclose replay')
            for key in ('height_start','height_end','height_cells','sigma_cells'):
                require(cell[key] == replay[key], f'saved {key} mismatch')
        worst = max(cells,key=lambda c: Fraction(c['delta_upper_rational']))
        require(saved['worst_cell'] == worst, 'worst cell metadata mismatch')
    finally:
        ctx.prec = previous_precision
    return dict(status='VERIFIED',number_of_cells=len(cells),
                log_x_interval=['400','700'],script_sha256=script_hash,
                certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                worst_upper_rational=worst['delta_upper_rational'],
                elapsed_seconds=time.monotonic()-started)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--single', nargs=2, metavar=('LEFT','RIGHT'))
    parser.add_argument('--cell-width', default='5')
    parser.add_argument('--sigma-denominator', type=int, default=1024)
    parser.add_argument('--height-denominator', type=int, default=8)
    parser.add_argument('--precision', type=int, default=PRECISION)
    parser.add_argument('--verify', nargs='?', const=str(OUTPUT), metavar='JSON',
                        help='read-only replay of the saved certificate')
    args = parser.parse_args()
    if args.verify:
        require(not args.single, '--verify and --single are incompatible')
        print(json.dumps(verify_certificate(args.verify),indent=2))
        return
    ctx.prec = args.precision
    require(ctx.prec >= 100, 'Require at least 100-bit working precision')
    started = time.monotonic()
    if args.single:
        cell=certify_cell(*args.single,args.sigma_denominator,args.height_denominator)
        print(json.dumps(cell,indent=2))
        print(f'Elapsed {time.monotonic()-started:.3f} seconds')
        return
    width=Fraction(args.cell_width)
    require(width>0, 'positive L cell width required')
    cells=[]
    left=Fraction(400)
    while left<700:
        right=min(Fraction(700),left+width)
        cell=certify_cell(left,right,args.sigma_denominator,args.height_denominator)
        cells.append(cell)
        print(f'L=[{left},{right}] upper={cell["delta_upper_approx"]} passed={cell["passed"]}',flush=True)
        require(cell['passed'], 'A cell failed; no full certificate is written')
        left=right
    require(Fraction(cells[0]['left'])==400 and Fraction(cells[-1]['right'])==700,'endpoints')
    for p,qcell in zip(cells,cells[1:]):
        require(Fraction(p['right'])==Fraction(qcell['left']),'gap in L coverage')
    worst=max(cells,key=lambda c: Fraction(c['delta_upper_rational']))
    result=dict(status='ALL_CELLS_PASSED',k=4,log_x_interval=['400','700'],
        statement='Under QRH(7/8) and cited inputs, every real x with 400<=log(x)<=700 has a prime in (x,x+4*x^(3/4)).',
        analytic_scope='Numerical inequalities for the analytic reduction in research/SMOOTH_CERTIFICATE.md; no global theorem or Lean claim.',
        source=dict(url=SOURCE,version='2507.15184v2',result='Corollary 1, Table 1, first 12 rows',
            constants=CS_ROWS,required_height='T>=3000000000000',
            p='3*(1-sigma)/(2-sigma)',q='(7-5*sigma)/(2-sigma)=2+p'),
        kernel=dict(M=2,R=['1','15/4','24','300'],max_over_mass='15/8'),
        count_bound='N(t)<=t*log(t) for t>=3000000000000',
        precision_bits=ctx.prec,sigma_denominator=args.sigma_denominator,
        height_denominator=args.height_denominator,L_cell_width=str(width),
        number_of_cells=len(cells),worst_cell=worst,cells=cells,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        python=platform.python_version(),python_flint=flint.__version__,
        created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        elapsed_seconds=time.monotonic()-started)
    OUTPUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(f'Wrote {OUTPUT}; {len(cells)} cells; elapsed {result["elapsed_seconds"]:.3f}s')


if __name__=='__main__':
    main()
