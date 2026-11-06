"""Independent Arb certificate for QRH(7/8), 372 <= log(x) <= 375.

Fixed trapezoid a=1/8, CS v2 Table 1, exact exponential sigma weights,
and analytic logarithmic-tangent height integrals. No k6/old certificate
module is imported. --single and --verify do not write any files.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import time
from datetime import datetime, timedelta, timezone
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'results' / 'k4_round3_certificate.json'
SCHEMA = 'legendre-k4-round3-trapezoid-v1'
TARGET = ('372', '375')
SOURCE = 'https://arxiv.org/html/2507.15184v2'
RH_SOURCE = 'https://arxiv.org/abs/2004.09765'
COUNT_SOURCE = 'https://doi.org/10.2307/2371291'
CS_ROWS = (
    ('5.069','9.461','167.8'), ('6.046','9.168','162.6'),
    ('7.077','8.875','157.4'), ('8.185','8.582','152.2'),
    ('9.387','8.290','147.0'), ('10.70','7.997','141.9'),
    ('12.11','7.704','136.7'), ('13.66','7.411','131.5'),
    ('15.35','7.118','126.3'), ('17.21','6.826','121.1'),
    ('19.31','6.533','115.9'), ('21.77','6.240','110.7'),
)
KERNEL = dict(a='1/8', b='7/8', R1='16/7', R2='256/7', maximum='8/7')
TESTED_SCALE = Fraction(1001, 1000)
# Each row fixes rational L cells and the sigma grid; height is analytic.
SCHEDULE = (('372', '745/2', '1/16', 65536),
            ('745/2', '373', '1/8', 32768),
            ('373', '375', '1/4', 16384))
HEIGHT_METHOD = 'whole-linear-segment-log-tangent-and-quadratic-tail-v1'


def require(condition, message):
    if not condition:
        raise ValueError(message)


def A(value):
    value = Fraction(value)
    return arb(value.numerator) / value.denominator


def integer(value, ceiling=False):
    result = (value.ceil() if ceiling else value.floor()).unique_fmpz()
    require(result is not None, 'Unresolved Arb integer rounding')
    return int(result)


def upper(value):
    return str(Fraction(integer(value * 10**24, True), 10**24))


def rational_interval(value):
    return [str(Fraction(integer(value * 10**24), 10**24)), upper(value)]


def kernel(q, u):
    z = q * (-u).exp()
    return arb(1).min(A(KERNEL['R1']) * z).min(A(KERNEL['R2']) * z*z)


def sigma_terms(la, denominator):
    require(isinstance(denominator, int) and denominator >= 32
            and denominator % 32 == 0, 'Invalid sigma grid')
    terms, dsum, esum = [], arb(0), arb(0)
    for i in range(denominator//2, 7*denominator//8):
        lo, hi = arb(i)/denominator, arb(i+1)/denominator
        row = i*32//denominator - 16
        require(Fraction(i, denominator) >= Fraction(16+row, 32), 'Source row lower')
        require(Fraction(i+1, denominator) <= Fraction(17+row, 32), 'Source row upper')
        c, d, e = (arb(v) for v in CS_ROWS[row])
        weight = ((hi-1)*la).exp() - ((lo-1)*la).exp()
        require(weight > 0, 'Positive sigma weight unresolved')
        p = 3*(1-lo)/(2-lo)
        terms.append((weight*c, p))
        dsum += weight*d
        esum += weight*e
    return terms, dsum, esum


def cumulative_parts(la, u, terms, dsum, esum):
    # Called only for exp(u)>=H. Count N(T)<=T log(T) follows from Rosser.
    main = arb(0)
    v = u + u.log()
    for coefficient, p in terms:
        main += coefficient*(p*v).exp()
    return u*u*main, u*u*dsum+esum*u, (-la/2+u).exp()*u


def height_tail_parts(la, q, U, terms, dsum, esum):
    # Complete Stieltjes tail; lower-height zeros retain their residual g(U).
    main = arb(0)
    logU = U.log()
    for coefficient, p in terms:
        denominator = 2-p-(p+2)/U
        require(denominator > 0, 'Tail logarithmic-tangent denominator')
        main += coefficient*((p-2)*U+(p+2)*logU).exp()/denominator
    baseline = (-la/2-U).exp()*(U+1)
    lower = (-2*U).exp()*(dsum*(U*U/2+U/2+arb(1)/4)
                                    + esum*(U/2+arb(1)/4))
    factor = 4*A(KERNEL['R2'])*q*q
    return factor*main, factor*lower, factor*baseline


def sensitivity(B1, B23, other):
    require(B1 > 0 and B23 >= 0 and other >= 0, 'Sensitivity component signs')
    one, all_three = (1-B23-other)/B1, (1-other)/(B1+B23)
    one_scaled = A(TESTED_SCALE)*B1+B23+other
    all_scaled = A(TESTED_SCALE)*(B1+B23)+other
    return dict(decomposition=dict(B1_ball=B1.str(50), B23_ball=B23.str(50),
                                   other_ball=other.str(50)),
                critical_factor_B1_only=rational_interval(one),
                critical_factor_all_three=rational_interval(all_three),
                tested_scale=str(TESTED_SCALE), B1_only_scaled_upper=upper(one_scaled),
                all_three_scaled_upper=upper(all_scaled),
                B1_only_scaled_passed=bool(one_scaled < 1),
                all_three_scaled_passed=bool(all_scaled < 1))


def certify_cell_upper_sum(left, right, sigma_denominator=16384, height_denominator=128):
    left, right = Fraction(left), Fraction(right)
    require(100 <= left < right <= 400, 'Cell outside analytic implementation domain')
    require(isinstance(height_denominator, int) and height_denominator > 0,
            'Invalid height grid')
    la, lb = A(left), A(right)
    q = 1+(lb/4).exp()/4
    logq, H = q.log(), arb('3000000000000')
    logH = H.log()
    platform_end = logq+A(KERNEL['R1']).log()
    start_index = integer(platform_end*height_denominator)
    candidate = arb(start_index)/height_denominator
    if candidate > logH:
        start = candidate
        require(kernel(q, start) == 1, 'Flat kernel start')
        low, start_tag = arb(0), str(Fraction(start_index, height_denominator))
    else:
        start, start_tag = logH, 'log(3000000000000)'
        low = 2*(-la/2).exp()*H*logH*(1-kernel(q, logH))
        require(low >= 0, 'Low-height contribution sign')
    require(start_tag == 'log(3000000000000)' or start > logH, 'Density height domain')
    quadratic_start = logq+(A(KERNEL['R2'])/A(KERNEL['R1'])).log()
    end_index = max(integer((quadratic_start+12)*height_denominator, True),
                    integer((logH+12)*height_denominator, True))
    end = arb(end_index)/height_denominator
    require(end >= quadratic_start, 'Quadratic kernel tail domain')
    terms, dsum, esum = sigma_terms(la, sigma_denominator)
    first_index = integer(start*height_denominator)+1
    previous = kernel(q, start)
    finite_parts = [arb(0), arb(0), arb(0)]
    for i in range(first_index, end_index+1):
        u = arb(i)/height_denominator
        current = kernel(q, u)
        mass = previous-current
        require(mass >= 0, 'Kernel positive mass unresolved')
        for j, value in enumerate(cumulative_parts(la, u, terms, dsum, esum)):
            finite_parts[j] += 2*value*mass
        previous = current
    tail_parts = height_tail_parts(la, q, end, terms, dsum, esum)
    finite, tail = sum(finite_parts, arb(0)), sum(tail_parts, arb(0))
    eps = 4*(-la/4).exp()
    pp = A(KERNEL['maximum'])*(1+eps).sqrt()*(lb+(1+eps).log())**2
    pp *= (-la/4).exp()/(8*arb(2).log())
    trivial = (-3*la).exp()/(1-(-2*la).exp())
    delta = low+finite+tail+pp+trivial
    analysis = sensitivity(finite_parts[0]+tail_parts[0], finite_parts[1]+tail_parts[1],
                           low+finite_parts[2]+tail_parts[2]+pp+trivial)
    require(delta.is_finite(), 'Nonfinite ball')
    return dict(left=str(left), right=str(right), passed=bool(delta < 1),
                sigma_denominator=sigma_denominator, height_denominator=height_denominator,
                delta_upper_rational=upper(delta), delta_ball=delta.str(40),
                low_zero_ball=low.str(30), finite_zero_ball=finite.str(35),
                height_tail_ball=tail.str(30), prime_power_ball=pp.str(30),
                trivial_ball=trivial.str(30), height_start=start_tag,
                height_end=str(Fraction(end_index, height_denominator)),
                height_cells=end_index-first_index+1, sigma_cells=len(terms), sensitivity=analysis)


def tangent_interval(p, r, j, begin, end):
    """Upper bound for integral exp((p-j)u) u**r du on [begin,end].

    log(u) <= log(v)+(u-v)/v at the midpoint v. The exponential
    of this affine majorant is integrated exactly, with a safe c=0 branch.
    """
    require(begin > 0 and end > begin and r >= 0, 'Tangent interval domain')
    v, width = (begin+end)/2, end-begin
    c = p-j+r/v
    if c.contains(0):
        ratio = width*(c*width).max(arb(0)).exp()
    else:
        ratio = (c*width).expm1()/c
    result = (r*(v.log()-1)+c*begin).exp()*ratio
    require(result > 0, 'Positive tangent integral unresolved')
    return result


def tangent_tail(p, r, j, begin):
    """Upper bound for integral_begin^infinity exp((p-j)u) u**r du."""
    denominator = j-p-r/begin
    require(begin > 0 and r >= 0 and denominator > 0, 'Tail tangent domain')
    return ((p-j)*begin+r*begin.log()).exp()/denominator


def _analytic_bound(left, right, sigma_denominator):
    left, right = Fraction(left), Fraction(right)
    require(100 <= left <= right <= 400, 'Outside analytic implementation domain')
    la, lb = A(left), A(right)
    q, H = 1+(lb/4).exp()/4, arb('3000000000000')
    logq, logH = q.log(), H.log()
    u1 = logq+A(KERNEL['R1']).log()
    u2 = logq+(A(KERNEL['R2'])/A(KERNEL['R1'])).log()
    require(u2 > u1, 'Kernel branch order')
    low = 2*(-la/2).exp()*H*logH*(1-kernel(q, logH))
    require(low >= 0, 'Finite RH piece sign')
    begin, tail_start = u1.max(logH), u2.max(logH)
    if begin < u2:
        has_linear = True
    else:
        require(begin >= u2, 'Linear interval order unresolved')
        has_linear = False
    terms, dsum, esum = sigma_terms(la, sigma_denominator)
    linear, tail = [arb(0), arb(0), arb(0)], [arb(0), arb(0), arb(0)]
    linear_factor, tail_factor = 2*A(KERNEL['R1'])*q, 4*A(KERNEL['R2'])*q*q

    def add(column, coefficient, p, r):
        if has_linear:
            linear[column] += linear_factor*coefficient*tangent_interval(p, r, 1, begin, u2)
        tail[column] += tail_factor*coefficient*tangent_tail(p, r, 2, tail_start)

    for coefficient, p in terms:
        add(0, coefficient, p, p+2)
    add(1, dsum, arb(0), arb(2))
    add(1, esum, arb(0), arb(1))
    add(2, (-la/2).exp(), arb(1), arb(1))
    eps = 4*(-la/4).exp()
    pp = A(KERNEL['maximum'])*(1+eps).sqrt()*(lb+(1+eps).log())**2
    pp *= (-la/4).exp()/(8*arb(2).log())
    trivial = (-3*la).exp()/(1-(-2*la).exp())
    finite, quadratic = sum(linear, arb(0)), sum(tail, arb(0))
    delta = low+finite+quadratic+pp+trivial
    analysis = sensitivity(linear[0]+tail[0], linear[1]+tail[1],
                           low+linear[2]+tail[2]+pp+trivial)
    require(delta.is_finite(), 'Nonfinite analytic ball')
    return dict(kind='point' if left == right else 'closed_cell', left=str(left), right=str(right),
                passed=bool(delta < 1), sigma_denominator=sigma_denominator,
                height_method=HEIGHT_METHOD, delta_upper_rational=upper(delta),
                delta_ball=delta.str(40), low_zero_ball=low.str(30),
                finite_zero_ball=finite.str(35), height_tail_ball=quadratic.str(35),
                prime_power_ball=pp.str(30), trivial_ball=trivial.str(30),
                linear_interval_ball=[begin.str(40), u2.str(40)] if has_linear else None,
                tail_start_ball=tail_start.str(40), sigma_cells=len(terms), sensitivity=analysis)


def certify_cell(left, right, sigma_denominator=65536):
    require(Fraction(left) < Fraction(right), 'Closed cell must have positive width')
    return _analytic_bound(left, right, sigma_denominator)


def certify_point(L, sigma_denominator=65536):
    return _analytic_bound(L, L, sigma_denominator)


def sensitivity_summary(cells):
    result = dict(tested_scale=str(TESTED_SCALE),
                  scope='Uniform CS Table 1 coefficient changes with all exponents, domains and envelope parameters fixed.')
    for mode, key in [('B1_only', 'critical_factor_B1_only'),
                      ('all_three', 'critical_factor_all_three')]:
        result[f'{mode}_critical_factor_interval'] = [
            str(min(Fraction(c['sensitivity'][key][j]) for c in cells)) for j in (0, 1)]
        result[f'{mode}_scaled_maximum_upper'] = str(max(
            Fraction(c['sensitivity'][f'{mode}_scaled_upper']) for c in cells))
        result[f'{mode}_all_passed'] = all(c['sensitivity'][f'{mode}_scaled_passed'] for c in cells)
    return result


def source_metadata():
    return dict(url=SOURCE, constants=[list(r) for r in CS_ROWS], finite_rh=RH_SOURCE,
                H='3000000000000', total_count=COUNT_SOURCE,
                total_count_bound='N(T)<=T log(T), T>=H')


def scheduled_cells():
    cells = []
    for left, right, width, sd in SCHEDULE:
        current, end, width = Fraction(left), Fraction(right), Fraction(width)
        while current < end:
            following = min(current+width, end)
            cells.append((current, following, sd))
            current = following
    require(str(cells[0][0]) == TARGET[0] and str(cells[-1][1]) == TARGET[1], 'Schedule endpoints')
    for old, new in zip(cells, cells[1:]):
        require(old[1] == new[0], 'Schedule gap or overlap')
    return cells


def verify_certificate(path=OUTPUT):
    saved = json.loads(Path(path).read_text(encoding='utf-8'))
    require(saved['schema'] == SCHEMA and saved['status'] == 'ALL_CELLS_PASSED', 'Schema/status')
    require(saved['k'] == 4 and saved['log_x_interval'] == list(TARGET), 'Target')
    require(saved['script_sha256'] == hashlib.sha256(Path(__file__).read_bytes()).hexdigest(), 'Script hash')
    require(saved['source'] == source_metadata() and saved['kernel'] == KERNEL, 'Sources/kernel')
    require(saved['source_publication_status'] == 'CS v2 preprint explicitly assumed', 'CS premise status')
    require(saved['schedule'] == [list(row) for row in SCHEDULE], 'Schedule')
    require(saved['height_method'] == HEIGHT_METHOD, 'Height method')
    require(isinstance(saved['precision_bits'], int) and 128 <= saved['precision_bits'] <= 4096, 'Precision')
    ctx.prec = saved['precision_bits']
    cells, expected = saved['cells'], scheduled_cells()
    require(len(cells) == saved['number_of_cells'] == len(expected), 'Cell count')
    for index, (cell, specification) in enumerate(zip(cells, expected), 1):
        left, right, sd = specification
        require((Fraction(cell['left']), Fraction(cell['right']), cell['sigma_denominator'])
                == specification, 'Cell schedule mismatch')
        require(cell['kind'] == 'closed_cell' and cell['height_method'] == HEIGHT_METHOD, 'Cell method')
        replay = certify_cell(left, right, sd)
        bound = Fraction(cell['delta_upper_rational'])
        require(cell['passed'] is True and replay['passed'] and 0 < bound < 1, 'Failed cell')
        require(Fraction(replay['delta_upper_rational']) <= bound, 'Saved bound too small')
        for key in ('delta_ball', 'low_zero_ball', 'finite_zero_ball', 'height_tail_ball',
                    'prime_power_ball', 'trivial_ball', 'linear_interval_ball',
                    'tail_start_ball', 'sigma_cells', 'sensitivity'):
            require(cell[key] == replay[key], f'Metadata replay mismatch: {key}')
        if index % 8 == 0:
            print(f'Verified {index}/{len(cells)}', flush=True)
    worst = max(cells, key=lambda c: Fraction(c['delta_upper_rational']))
    require(saved['worst_cell'] == worst, 'Worst cell metadata')
    require(saved['sensitivity_summary'] == sensitivity_summary(cells), 'Sensitivity summary')
    return dict(status='VERIFIED', k=4, number_of_cells=len(cells), log_x_interval=list(TARGET),
                worst_upper_rational=worst['delta_upper_rational'],
                minimum_margin_rational=str(1-Fraction(worst['delta_upper_rational'])),
                sensitivity_summary=saved['sensitivity_summary'], script_sha256=saved['script_sha256'],
                certificate_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--single', nargs=2)
    parser.add_argument('--point')
    parser.add_argument('--upper-sum', action='store_true', help='Comparison method; requires --single')
    parser.add_argument('--verify', nargs='?', const=str(OUTPUT))
    parser.add_argument('--precision', type=int, default=256)
    parser.add_argument('--sigma-denominator', type=int, default=65536)
    parser.add_argument('--height-denominator', type=int, default=128)
    args = parser.parse_args()
    if args.verify:
        print(json.dumps(verify_certificate(args.verify), indent=2))
        return
    require(128 <= args.precision <= 4096, 'Precision outside permitted range')
    ctx.prec = args.precision
    if args.point:
        require(not args.single and not args.upper_sum, 'Choose a single evaluation mode')
        print(json.dumps(certify_point(args.point, args.sigma_denominator), indent=2))
        return
    if args.single:
        result = (certify_cell_upper_sum(*args.single, args.sigma_denominator, args.height_denominator)
                  if args.upper_sum else certify_cell(*args.single, args.sigma_denominator))
        print(json.dumps(result, indent=2))
        return
    require(not args.upper_sum, '--upper-sum requires --single')
    started, cells = time.monotonic(), []
    for left, right, sd in scheduled_cells():
        cell = certify_cell(left, right, sd)
        require(cell['passed'] and Fraction(cell['delta_upper_rational']) < 1,
                f'Failed cell [{left},{right}]; no certificate written')
        cells.append(cell)
        print(f'PASS [{left},{right}] {cell["delta_ball"]}', flush=True)
    worst = max(cells, key=lambda c: Fraction(c['delta_upper_rational']))
    saved = dict(schema=SCHEMA, status='ALL_CELLS_PASSED', k=4, log_x_interval=list(TARGET),
                 created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
                 conditional_inputs=['QRH(7/8)', 'CS v2 Corollary 1 / Table 1', 'Platt-Trudgian finite RH'],
                 source_publication_status='CS v2 preprint explicitly assumed', source=source_metadata(),
                 kernel=KERNEL, precision_bits=args.precision, schedule=[list(row) for row in SCHEDULE],
                 height_method=HEIGHT_METHOD,
                 python_flint=flint.__version__, number_of_cells=len(cells), cells=cells,
                 worst_cell=worst, sensitivity_summary=sensitivity_summary(cells),
                 script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                 elapsed_seconds=time.monotonic()-started,
                 scope='Continuous real-x segment only; proof in research/K4_ROUND3_CERTIFICATE.md')
    OUTPUT.write_text(json.dumps(saved, indent=2)+'\n', encoding='utf-8')
    print(f'Saved {OUTPUT}; {len(cells)} cells; worst {worst["delta_ball"]}')


if __name__ == '__main__':
    main()
