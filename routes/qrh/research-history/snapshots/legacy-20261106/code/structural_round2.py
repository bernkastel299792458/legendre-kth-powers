#!/usr/bin/env python3
"""Finite Arb checks for the model-zero diagnostic in STRUCTURAL_ROUND2.md.

This is not a prime-existence certificate and does not construct zeta zeros.
The countable model is defined implicitly in the accompanying proof.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / 'results' / 'structural_round2_model.json'


def ratio(n, d=1):
    return arb(n) / d


def run_checks():
    ctx.prec = 256
    H, W, K = arb(3 * 10**12), arb(10**8), arb(10**8)
    G = H + W
    beta, alpha = ratio(8749, 10000), ratio(1251, 10000)
    pi = arb.pi()
    checks = {}

    def check(name, statement):
        checks[name] = bool(statement)
        if not checks[name]:
            raise ValueError(name)

    def P(t):
        return t/(2*pi)*(t/(2*pi*arb(1).exp())).log() + ratio(7, 8)

    def R(t):
        u = t.log()
        return ratio(137,1000)*u + ratio(443,1000)*u.log() + ratio(1588,1000)

    def derivative_P(t):
        return (t/(2*pi)).log()/(2*pi)

    def BW_error(t):
        u = t.log()
        return (ratio(10076,100000)*u+ratio(24460,100000)*u.log()
                +ratio(808344,100000)).min(
                ratio(112,1000)*u+ratio(12567,100000)*u.log()
                +ratio(377417,100000))

    def quantities(n):
        L = arb(n)
        eps = 4*(-L/4).exp()
        ell = (1+eps).log()
        phase = G*ell
        coherent = 2*K*(-alpha*(L+ell)).exp()*(phase/2).cos()
        q = 1+(L/4).exp()/4
        t0 = arb(24).sqrt()*q
        background = 4*arb(24).sqrt()*q*(-L/2).exp()*(t0.log()+1)
        single = (-alpha*(L+ell)).exp()*(phase/2).cos()
        return phase, coherent, background, single, t0

    u = H.log()
    # Lower bound on every published upper-bound expression for sigma>1/2,
    # sigma<=7/8. This establishes model feasibility, NOT an actual count.
    permitted_capacity_floor = ratio(5069,1000)*(u/3+ratio(7,3)*u.log()).exp()
    appendix_capacity_floor = ratio(29,10)*(u/3+ratio(5,2)*u.log()).exp()
    check('CS_all_rows_allow_K', permitted_capacity_floor > K)
    check('CS_119_all_rows_allow_K', appendix_capacity_floor > K)
    check('beta_below_QRH', beta < ratio(7,8))
    check('beta_below_34999_over_40000', beta < ratio(34999,40000))
    check('Rosser_error_exceeds_four', R(H) > 4)
    check('CS_total_count_error_allows_model', ratio(43,100)*u > ratio(7,8)+4)
    check('BW_error_allows_modified_model_above_H', BW_error(H) > ratio(7,8)+4)
    check('BW_error_allows_baseline_below_H', BW_error(arb(1).exp()) > ratio(7,8)+2)
    check('pair_spacing_derivative_lower', derivative_P(H) > 4)
    check('pair_spacing_derivative_upper', derivative_P(G) < 5)
    check('maximum_resonance_shift_below_point03', pi/116 < ratio(3,100))
    check('shift_intervals_are_disjoint', 2*pi/116 < ratio(2,5))
    m0_ball = (P(H+1)/2).ceil()
    m0 = m0_ball.unique_fmpz()
    check('first_pair_index_is_unique', m0 is not None)
    m0 = int(m0)
    check('first_pair_after_H_plus_one', 2*arb(m0) >= P(H+1))
    check('last_pair_before_G_minus_one', 2*arb(m0+10**8-1) < P(G-1))
    # These endpoint facts combine with the analytic concavity/monotonicity
    # arguments in the document to cover every real L in [116,150].
    phase116, lower116, background116, _, t0116 = quantities(116)
    phase150, lower150, _, _, _ = quantities(150)
    check('phase_arc_below_pi_on_whole_L_interval', phase116 < pi)
    check('positive_phase_at_L150', phase150 > 0)
    check('coherent_endpoint_116_exceeds_seven_fifths', lower116 > ratio(7,5))
    check('coherent_endpoint_150_exceeds_seven_fifths', lower150 > ratio(7,5))
    check('quadratic_background_cutoff_above_H', t0116 > H)
    check('whole_background_below_1e_minus10', background116 < ratio(1,10**10))
    check('net_model_real_error_exceeds_one', ratio(7,5)-ratio(1,10**10) > 1)
    # Optional global completion of N0(t)=2 max(0,floor(P(t)/2)), t>=2.
    check('Rosser_error_above_two_after_exp2', R(arb(2).exp()) > 2)
    check('small_height_P_two_below_quarter', P(arb(2)) < ratio(1,4))
    check('small_height_P_exp2_below_quarter', P(arb(2).exp()) < ratio(1,4))
    check('small_height_R_two_above_quarter', R(arb(2)) > ratio(1,4))
    points = []
    for n in (116,117,120,125,130,140,150):
        phase, coherent, background, single, _ = quantities(n)
        points.append(dict(L=n, phase_arc=phase.str(55),
                           coherent_batch_lower=coherent.str(55),
                           M2_critical_background_upper=background.str(55),
                           inverse_pair_weight=(1/(2*single)).str(55)))
    local_cap = (P(G)+R(G)-P(H)+R(H))/2
    last_row_density = ratio(2177,100)*(u/3+ratio(7,3)*u.log()).exp()
    last_row_density += ratio(156,25)*u*u+ratio(1107,10)*u
    _, _, _, single120, _ = quantities(120)
    target_count120 = 1/(2*single120)
    L120 = arb(120)
    ell120 = (1+4*(-L120/4).exp()).log()
    signed_m120 = (-alpha*ell120).exp()*((H+W)*ell120/2).cos()
    signed_L1_threshold = ((1+signed_m120)-1/(K*(-alpha*L120).exp()))/(1-signed_m120)
    check('signed_L1_threshold_exceeds_eleven', signed_L1_threshold > 11)
    return dict(
        status='FINITE_CHECKS_FOR_MODEL_CONSTRUCTION_PASSED',
        meaning='For each real L in [116,150], a different allowed model may be chosen. This is not a zeta-zero or prime-existence certificate.',
        precision_bits=ctx.prec, H='3000000000000', W='100000000', K='100000000',
        beta='8749/10000', interval=['116','150'],
        model_inputs=['QRH(7/8)', 'critical-line location below H',
                      'CS v2 Corollary 1 Table 1 cumulative density',
                      'CS v2 Eq(119) Table 4 cumulative density',
                      'Rosser total-count two-sided bound', 'CS v2 Eq(11) total-count upper bound',
                      'BW v2 Theorem 1.1 total-count two-sided bound and derived local caps',
                      'lower-sigma endpoint monotone envelopes of these bounds',
                      'conjugation and beta-to-1-minus-beta symmetry'],
        excluded_claims=['not actual zero existence', 'not an Euler product or zeta explicit formula',
                         'not a match to the actual low-zero ordinate list',
                         'not a single common model for all L', 'not a limitation of all methods'],
        first_pair_index=m0, checks=checks,
        CS_uniform_allowed_capacity_floor=permitted_capacity_floor.str(55),
        CS_119_uniform_allowed_capacity_floor=appendix_capacity_floor.str(55),
        BW_error_H=BW_error(H).str(55),
        Rosser_R_H=R(H).str(55), local_right_count_cap=local_cap.str(55),
        CS_last_row_density_H=last_row_density.str(55),
        L120_pair_count_comparison=target_count120.str(55),
        L120_local_cap_over_comparison=(local_cap/target_count120).str(55),
        L120_CS_last_row_over_comparison=(last_row_density/target_count120).str(55),
        L120_signed_kernel_L1_threshold=signed_L1_threshold.str(55),
        points=points,
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    result = run_checks()
    if args.verify:
        saved = json.loads(OUTPUT.read_text(encoding='utf-8'))
        if saved != result:
            raise ValueError('Saved diagnostic does not match read-only replay')
    else:
        OUTPUT.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(json.dumps(dict(status=result['status'],checked=len(result['checks']),
                         read_only=args.verify,interval=result['interval'],
                         coherent_uniform_lower='7/5',
                         M2_background_uniform_upper='1/10000000000',
                         output=str(OUTPUT)),indent=2))


if __name__ == '__main__':
    main()
