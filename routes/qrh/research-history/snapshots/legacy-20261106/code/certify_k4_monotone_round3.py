"""One-point Arb checks for the analytic k4 theorem log(x) >= 372.

The extension to infinity is proved in K4_MONOTONE_ROUND3.md, not inferred
from samples. The point budget comes from the independently documented
trapezoid module. QRH and the fixed CS v2 density estimate remain inputs.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import runpy
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
HELPER = ROOT / 'code' / 'certify_k4_round3.py'
PROOF = ROOT / 'research' / 'K4_MONOTONE_ROUND3.md'
OUTPUT = ROOT / 'results' / 'k4_monotone_round3_certificate.json'
SCHEMA = 'legendre-k4-monotone-round3-v1'
L0 = 372
SIGMA_DENOMINATOR = 65536


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(value, message):
    if not value:
        raise ValueError(message)


def compute():
    ctx.prec = 256
    helper = runpy.run_path(str(HELPER))
    require(helper['KERNEL'] == dict(a='1/8', b='7/8', R1='16/7',
                                   R2='256/7', maximum='8/7'), 'Kernel changed')
    l0 = arb(L0)
    q0 = 1+(l0/4).exp()/4
    u0 = (arb(16)/7*q0).log()
    logH = arb('3000000000000').log()
    # Positive decay rates for the exact continuous density budget.
    rates = {
        'B1': arb(1)/24-arb(3)/(4*u0)-1/l0,
        'B2': arb(1)/8-arb(2)/(4*u0)-1/l0,
        'B3': arb(1)/8-arb(1)/(4*u0)-1/l0,
        'baseline': arb(1)/4-arb(1)/(4*u0),
        'prime_powers': arb(1)/4-2/l0,
    }
    require(u0 > logH, 'Density applies to all nonflat kernel heights')
    for name, rate in rates.items():
        require(rate > 0, 'Nonpositive decay rate: '+name)
    point = helper['certify_point'](L0, SIGMA_DENOMINATOR)
    require(point['passed'] and point['kind'] == 'point', 'Point budget failed')
    require(point['low_zero_ball'] == '0', 'Unexpected low-height term')
    bound = Fraction(point['delta_upper_rational'])
    require(0 < bound < Fraction(124, 125), 'Point target 0.992 not attained')
    return dict(
        schema=SCHEMA, status='VERIFIED_ANALYTIC_TAIL', k=4,
        full_k4_proved=False, log_x_lower=str(L0),
        precision_bits=256, sigma_denominator=SIGMA_DENOMINATOR,
        conditional_inputs=['QRH(7/8)', 'CS arXiv:2507.15184v2 Corollary 1 / Table 1',
                            'Rosser total zero count', 'Integrated zeta explicit formula'],
        finite_RH_used_in_this_tail=False,
        u0_ball=u0.str(50), logH_ball=logH.str(50),
        decay_rate_balls={name: value.str(50) for name, value in rates.items()},
        point=point, bound_rational=str(bound),
        scope='One numerical point plus an analytic comparison for every real L >= 372; not a sampling extrapolation or Lean proof.',
        helper_sha256=digest(HELPER), proof_sha256=digest(PROOF),
        script_sha256=digest(Path(__file__)))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    fresh = compute()
    if args.verify:
        saved = json.loads(OUTPUT.read_text(encoding='utf-8'))
        require(saved == fresh, 'Certificate differs from exact replay')
        print('VERIFIED_ANALYTIC_TAIL: L >= 372; upper = '+fresh['bound_rational'])
    else:
        OUTPUT.write_text(json.dumps(fresh, indent=2)+'\n', encoding='utf-8')
        print('SAVED '+str(OUTPUT))


if __name__ == '__main__':
    main()
