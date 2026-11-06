"""Independent read-only audit of the refined k=6 certificate.

Uses no import from the author certificate program. Rebuilds selected cells at
512 bits with expm1 sigma weights and a different power evaluation. Checks the
saved affine sensitivity decomposition and global summaries for every cell.
The selected analytic replay is not a replacement for full author replay.
"""
from fractions import Fraction
from pathlib import Path
import hashlib
import json
import time

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
CERTIFICATE = ROOT / 'results' / 'smooth_k6_certificate.json'
ROWS = [
    ('5.069', '9.461', '167.8'), ('6.046', '9.168', '162.6'),
    ('7.077', '8.875', '157.4'), ('8.185', '8.582', '152.2'),
    ('9.387', '8.290', '147.0'), ('10.70', '7.997', '141.9'),
    ('12.11', '7.704', '136.7'), ('13.66', '7.411', '131.5'),
    ('15.35', '7.118', '126.3'), ('17.21', '6.826', '121.1'),
    ('19.31', '6.533', '115.9'), ('21.77', '6.240', '110.7'),
]


def rational(value):
    f = Fraction(value)
    return arb(f.numerator) / f.denominator


def integer(value, ceiling=False):
    out = (value.ceil() if ceiling else value.floor()).unique_fmpz()
    if out is None:
        raise ValueError('Unresolved integer rounding')
    return int(out)


def require(test, message):
    if not test:
        raise ValueError(message)


def inside(value, pair):
    return value >= rational(pair[0]) and value <= rational(pair[1])


def check_affine(cell, parts):
    b1, b23, other = parts
    sens = cell['sensitivity']
    require(b1 > 0 and b23 >= 0 and other >= 0, 'Component positivity')
    require(sens['tested_scale'] == '53/50', 'Saved test multiplier')
    require(sum(parts, arb(0)) < rational(cell['delta_upper_rational']),
            'Affine decomposition does not obey saved upper bound')
    factor1 = (1 - b23 - other) / b1
    factor_all = (1 - other) / (b1 + b23)
    require(inside(factor1, sens['critical_factor_B1_only']), 'B1 threshold enclosure')
    require(inside(factor_all, sens['critical_factor_all_three']), 'All-column threshold enclosure')
    require(factor1 > rational('53/50') and factor_all > rational('53/50'),
            'Multiplier 1.06 not strictly below threshold')
    scale = rational('53/50')
    for name, value in [('B1_only', scale * b1 + b23 + other),
                        ('all_three', scale * (b1 + b23) + other)]:
        require(value < rational(sens[name + '_scaled_upper']) < 1,
                'Scaled affine upper bound')
        require(sens[name + '_scaled_passed'] is True, 'Saved scaling status')
    return dict(critical_B1=factor1.str(60), critical_all=factor_all.str(60),
                scaled_all=(scale * (b1 + b23) + other).str(60))


def check_all_saved(saved):
    cells = saved['cells']
    require(saved['schema'] == 'legendre-k6-smooth-v2-refined', 'Schema')
    require(saved['source']['constants'] == [list(r) for r in ROWS], 'Source constants')
    require(saved['source']['url'] == 'https://arxiv.org/html/2507.15184v2', 'CS version')
    require(saved['sigma_denominator'] == 4096 and saved['height_denominator'] == 64,
            'Refined grids')
    require(saved['number_of_cells'] == len(cells) == 94, 'Cell count')
    require(cells[0]['left'] == '167' and cells[-1]['right'] == '400', 'Target endpoints')
    for index, cell in enumerate(cells):
        left, right = Fraction(cell['left']), Fraction(cell['right'])
        require(left < right, 'Cell ordering')
        if index:
            require(Fraction(cells[index - 1]['right']) == left, 'Coverage adjacency')
        if left < 182 and right > 176:
            require(right - left <= Fraction(1, 4), 'Critical-region width')
        require(Fraction(cell['delta_upper_rational']) < Fraction(47, 50), 'Six-percent margin')
        part = cell['sensitivity']['decomposition']
        check_affine(cell, [arb(part[name]) for name in ['B1_ball', 'B23_ball', 'other_ball']])
    summary = saved['sensitivity_summary']
    for mode, key in [('B1_only', 'critical_factor_B1_only'),
                      ('all_three', 'critical_factor_all_three')]:
        expected = [min(Fraction(c['sensitivity'][key][j]) for c in cells) for j in [0, 1]]
        require(expected == [Fraction(x) for x in summary[mode + '_critical_factor_interval']],
                'Global critical-factor interval')
        maximum = max(Fraction(c['sensitivity'][mode + '_scaled_upper']) for c in cells)
        require(maximum == Fraction(summary[mode + '_scaled_maximum_upper']),
                'Global scaled maximum')
        require(summary[mode + '_all_passed'] is True, 'Global scaled status')
    require(saved['worst_cell'] == max(cells, key=lambda c: Fraction(c['delta_upper_rational'])),
            'Worst-cell identification')


def replay(cell):
    la, lb = rational(cell['left']), rational(cell['right'])
    q = 1 + (lb / 6).exp() / 6
    r1, r2 = arb(64) / 31, arb(4096) / 31
    H, sd, hd = arb(3000000000000), 4096, 64
    logH = H.log()

    def kernel(u):
        z = q / u.exp()
        if z >= 1 / r1:
            return arb(1)
        require(z < 1 / r1, 'Unresolved plateau branch')
        if z >= r1 / r2:
            return r1 * z
        require(z < r1 / r2, 'Unresolved quadratic branch')
        return r2 * z * z

    candidate_index = integer((q * r1).log() * hd)
    candidate = arb(candidate_index) / hd
    if candidate > logH:
        start = candidate
        start_tag = str(Fraction(candidate_index, hd))
        require(kernel(start) == 1, 'Plateau start')
    else:
        start = logH
        start_tag = 'log(3000000000000)'
    require(cell['height_start'] == start_tag, 'Start metadata')
    low = 2 * (-la / 2).exp() * H * logH * (1 - kernel(logH))
    terms, ds, es = [], arb(0), arb(0)
    for row, numbers in enumerate(ROWS):
        c, d, e = [rational(v) for v in numbers]
        for j in range(sd // 32):
            s = arb((16 + row) * (sd // 32) + j) / sd
            weight = ((s - 1) * la).exp() * (la / sd).expm1()
            p = 3 * (1 - s) / (2 - s)
            terms.append((weight * c, p))
            ds += weight * d
            es += weight * e
    first = integer(start * hd) + 1
    end = max(integer(((q * 64).log() + 12) * hd, True),
              integer((logH + 12) * hd, True))
    require(str(Fraction(end, hd)) == cell['height_end'], 'End metadata')
    require(end - first + 1 == cell['height_cells'] and len(terms) == cell['sigma_cells'],
            'Grid counts')
    previous, finite = kernel(start), [arb(0), arb(0), arb(0)]
    for j in range(first, end + 1):
        u = arb(j) / hd
        main = sum((co * (p * u).exp() * u ** (p + 2) for co, p in terms), arb(0))
        lower = ds * u * u + es * u
        baseline = (-la / 2 + u).exp() * u
        current = kernel(u)
        mass = previous - current
        require(mass >= 0, 'Positive Stieltjes mass')
        for index, cumulative in enumerate([main, lower, baseline]):
            finite[index] += 2 * cumulative * mass
        previous = current
    U, main_tail = arb(end) / hd, arb(0)
    for co, p in terms:
        denominator = 2 - p - (p + 2) / U
        require(denominator > 0, 'Tail tangent denominator')
        main_tail += co * ((p - 2) * U).exp() * U ** (p + 2) / denominator
    baseline_tail = (-la / 2 - U).exp() * (U + 1)
    lower_tail = ds * (-2 * U).exp() * (U * U / 2 + U / 2 + arb(1) / 4)
    lower_tail += es * (-2 * U).exp() * (U / 2 + arb(1) / 4)
    factor = 4 * r2 * q * q
    tail = [factor * main_tail, factor * lower_tail, factor * baseline_tail]
    eps = 6 * (-la / 6).exp()
    pp = (arb(32) / 31) * (1 + eps).sqrt() * (lb + (1 + eps).log()) ** 2
    pp *= (-la / 3).exp() / (12 * arb(2).log())
    trivial = 1 / ((3 * la).exp() - la.exp())
    parts = [finite[0] + tail[0], finite[1] + tail[1], low + finite[2] + tail[2] + pp + trivial]
    delta = sum(parts, arb(0))
    require(arb(cell['delta_ball']).contains(delta), 'Delta display ball containment')
    for label, part in zip(['B1_ball', 'B23_ball', 'other_ball'], parts):
        require(arb(cell['sensitivity']['decomposition'][label]).contains(part),
                'Independent affine component containment: ' + label)
    affine = check_affine(cell, parts)
    return dict(left=cell['left'], right=cell['right'], height_start=start_tag,
                delta=delta.str(75), low=low.str(50), precision_bits=ctx.prec,
                affine=affine, passed=True)


def main():
    started = time.monotonic()
    ctx.prec = 512
    raw = CERTIFICATE.read_bytes()
    saved = json.loads(raw)
    check_all_saved(saved)
    print(json.dumps(dict(saved_affine_and_coverage_cells=94, passed=True)), flush=True)
    by_cell = {(c['left'], c['right']): c for c in saved['cells']}
    selected = [('167', '168'), ('1429/8', '715/4'), ('715/4', '179'),
                ('179', '717/4'), ('395', '400')]
    results = []
    for key in selected:
        result = replay(by_cell[key])
        results.append(result)
        print(json.dumps(result), flush=True)
    require(raw == CERTIFICATE.read_bytes(), 'Certificate changed during audit')
    print(json.dumps(dict(status='INDEPENDENT_SELECTED_REPLAY_PASSED',
                          certificate_sha256=hashlib.sha256(raw).hexdigest(),
                          reviewed_author_script_sha256=saved['script_sha256'],
                          audit_script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                          selected_cells=len(results), saved_affine_cells=94,
                          elapsed_seconds=time.monotonic()-started)), flush=True)


if __name__ == '__main__':
    main()
