"""Independent scalar and point audit; no author/generator module is imported.

Reads the round-five certificate as data.  All writes stay in this audit folder.
Analytic formulas and the limitations of the check are recorded in REVIEW.md.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from fractions import Fraction
from pathlib import Path

from flint import arb, ctx

AUDIT = Path(__file__).resolve().parent
ROUND = AUDIT.parent


def q(s):
    f = Fraction(s)
    return arb(f.numerator) / f.denominator


def check(condition, message):
    if not condition:
        raise ValueError(message)


def power(x, exponent):
    return (x.log() * exponent).exp()


def product(items):
    out = arb(1)
    for item in items:
        out *= item
    return out


def constants():
    # Direct transcription of CS v2 Lemmas 5--9 and Theorem 1, h=1.
    u, v, h0 = arb(80), arb(75), arb(3000000000000)
    t0, a0 = u.exp(), v.exp()
    d, delta, kappa = q('3/10'), q('1/5'), q('3/20')
    check(t0 > h0 >= 1002, 'height domain')
    check(u > 2*d and u > arb(1).exp(), 'T0 domain')
    check(t0 > 3*10**10 and 0 < delta <= u/20, 'h and delta domains')
    check(a0 > 10**10, 'Corollary 5 A0 domain')
    check(q('17/32') > q('1/2') + d/u, 'sigma domain for all new rows')
    pi, log2, euler = arb.pi(), arb(2).log(), arb.const_euler()
    m = (1 + q('2/3') * q('6/5').sqrt()).sqrt()
    c1 = 6/pi**2 + q('1.048')/u
    c2 = pi*m*q('.62')/u + 6*m/(pi*t0) + pi*m*q('1.048')/(t0*u)
    c3 = pi*m*q('.54')/(2*delta) * (2*delta*euler/u).exp()
    c4 = q('.54')/(5*delta*delta.exp()) + q('.605')*(-2*delta).exp()/u
    s = 1+(2+euler+7/(36*t0))/u
    z = 9*s*s*u*u/t0
    check(0 < z < 1, 'C5/C6 logarithm domain')
    log_part = -(-z).log1p()
    c5 = log_part*(3+8*pi*m)*(1+q('3.31')/u)*u/(9*s*s)
    c6 = 220 + pi/log2*(-3*u/2).exp().log1p()
    c6 += 4/log2*(((q('5/2')/h0)**2+(1+2/h0)**2).sqrt()/(2*pi)).log()
    c6 += 2*pi/log2*log_part
    moment1 = a0*(v-log2)**4/(2*pi*pi) + q('34.842')*a0*(v-log2)**3 + q('1.3897e16')
    moment2 = (1-log2/v)**4/(2*pi*pi) + q('34.842')/v*(1-log2/v)**3
    moment2 += q('9.5079e15')/(a0*v**4)
    a = 3/(4*kappa)
    nu = 2/(3*u)
    slope = nu*a/(1+a)
    intercept = (nu*((1+a).log()-a/(1+a))).exp()
    rate = 1-slope
    check(0 < rate < 1, 'Gamma decay domain')
    leading = power(c1*a.sqrt(), q('2/3'))*arb.pi().sqrt()/2 / power(rate, q('3/2'))
    remainder = power(c2, q('2/3'))*q('7/6').gamma()/power(rate, q('7/6'))
    k1_finite = power(2*moment1, q('1/3'))*power(c2+a0*c1/t0, q('2/3'))
    k1_finite /= power(t0, q('1/3'))*power(u, q('4/3'))
    k1_multiplier = power(2*moment2*a.sqrt(), q('1/3'))*intercept
    k1 = k1_multiplier*(leading+remainder)+k1_finite
    # An additional mathematically valid improvement, not used for this certificate.
    remainder_tangent = q('2/3')*c2*power(c1*a.sqrt(), q('-1/3'))/rate
    k1_tangent = k1_multiplier*(leading+remainder_tangent)+k1_finite
    k2 = power(arb(2), q('1/3'))*(a.sqrt()*pi.sqrt()/2 + (a0/t0)**3/a)
    k3 = c3+c4*(pi.sqrt()/(2*(2*kappa).sqrt())+pi*m/t0)
    ell0 = (kappa*(1+((1+2*delta/u)/(4*t0))**2)).exp()/(1-1/h0)
    check(ell0 > 1 and k3 > 1, 'negative-power maxima equal one')
    ell1 = arb(1).max(power(k1, 3*delta/u))*(3*delta+4*delta*u.log()/u).exp()
    ell2 = arb(1).max(power(k2, 3*delta/u))*(3*delta).exp()
    rows = []
    for i in range(17, 28):
        left, right = arb(i)/32, arb(i+1)/32
        # Keep all endpoint maxima as in the source rather than assuming their location.
        shared = product([
            power(ell0, 2/(2-left)).max(power(ell0, 2/(2-right))),
            power(k3, (2*left-1)/(2-left)).max(power(k3, (2*right-1)/(2-right)))])
        aa = []
        for k, ell, extra in [(k1, ell1, (d*(3+4*u.log()/u)).exp()), (k2, ell2, (3*d).exp())]:
            aa.append(product([ell, extra, shared, arb(1).max(power(k, 3*d/u)),
                power(k, 3*(1-left)/(2-left)).max(power(k, 3*(1-right)/(2-right)))]))
        bracket = (3-2*left)/(2*d)+1/u
        a3, a4 = bracket/(pi*log2), 3*bracket/(2*log2)
        a5 = c6*bracket/(2*pi)+c5/(2*pi*d)
        rows.append([(aa[0]+aa[1]*power(u, -6*(1-right)/(2-right)))/(2*pi*d),
                     a3+a4, a3*h0.log()+a5])
    return rows, dict(C1=c1,C2=c2,C3=c3,C4=c4,C5=c5,C6=c6,a1=moment1,a2=moment2,
        L0=ell0,K1_upper=k1,K2=k2,K3=k3,L1_upper=ell1,L2=ell2,gamma_decay=rate), k1_tangent


def height_integral(p, r, u1, u2, scale1, scale2):
    # 2 integral t^p log(t)^r (-dg(t)); one affine majorant of r log u.
    middle = (u1+u2)/2
    b = p-1+r/middle
    width = u2-u1
    check(not b.contains(0), 'nonzero linear exponential slope')
    finite = (r*middle.log()-r+b*u1).exp()*(b*width).expm1()/b
    denominator = 2-p-r/u2
    check(denominator > 0, 'tail decay')
    infinite = ((p-2)*u2+r*u2.log()).exp()/denominator
    return scale1*finite+scale2*infinite


def point_bound(L, rows, sd):
    ell = q(L)
    check(sd % 32 == 0 and sd >= 32, 'aligned sigma grid')
    qq = 1+(ell/4).exp()/4
    u1, u2 = (q('16/7')*qq).log(), (16*qq).log()
    check(u1 > 80, 'all Stieltjes mass above rebased density height')
    scale1, scale2 = q('32/7')*qq, q('1024/7')*qq*qq
    main, lower_d, lower_e = arb(0), arb(0), arb(0)
    for i in range(sd//2, 7*sd//8):
        sigma = arb(i)/sd
        p = 3*(1-sigma)/(2-sigma)
        # Exact integral of L exp((sigma-1)L) across each sigma cell.
        w = ((sigma-1)*ell).exp()*(ell/sd).expm1()
        row = [q(x) for x in rows[i*32//sd-16]]
        main += w*row[0]*height_integral(p,p+2,u1,u2,scale1,scale2)
        lower_d += w*row[1]
        lower_e += w*row[2]
    # Independent exact elementary integrals for the auxiliary height terms.
    j02 = scale1*((-u1).exp()*(u1*u1+2*u1+2)-(-u2).exp()*(u2*u2+2*u2+2))
    j02 += scale2*(-2*u2).exp()*(u2*u2/2+u2/2+q('1/4'))
    j01 = scale1*((-u1).exp()*(u1+1)-(-u2).exp()*(u2+1))
    j01 += scale2*(-2*u2).exp()*(u2/2+q('1/4'))
    baseline = (-ell/2).exp()*(scale1*(u2*u2-u1*u1)/2+scale2*(-u2).exp()*(u2+1))
    aux = lower_d*j02+lower_e*j01
    eps = 4*(-ell/4).exp()
    pp = (1+eps).sqrt()*(ell+eps.log1p())**2*(-ell/4).exp()/(7*arb(2).log())
    trivial = (-3*ell).exp()/(1-(-2*ell).exp())
    total = main+aux+baseline+pp+trivial
    rates = dict(main=q('1/24')-3/(4*u1)-1/ell, baseline=q('1/4')-1/(4*u1),
        second=q('1/8')-2/(4*u1)-1/ell, third=q('1/8')-1/(4*u1)-1/ell,
        prime_powers=q('1/4')-2/ell,
        sharper_main=q('1/24')-7/(12*u1)-1/ell)
    check(all(rate > 0 for rate in rates.values()), 'positive analytic rates')
    return dict(total=total,main=main,auxiliary=aux,baseline=baseline,prime_powers=pp,
                trivial=trivial,u0=u1), rates


def additional_bounds():
    result = {}
    # Safe upper bound on the gain from restoring the exact symmetry subtraction
    # in the old Table 1 envelope. Valid here since u1 > log H and u1 > 0.
    for value in [120,372]:
        ell = arb(value)
        qq = 1+(ell/4).exp()/4
        u1, u2 = (q('16/7')*qq).log(), (16*qq).log()
        check(u1 > arb(3000000000000).log(), 'symmetry envelope domain')
        s1, s2 = q('32/7')*qq,q('1024/7')*qq*qq
        bound = q('21.77')*height_integral(arb(1),arb(3),u1,u2,s1,s2)
        bound += q('9.461')*height_integral(arb(0),arb(2),u1,u2,s1,s2)
        bound += q('167.8')*height_integral(arb(0),arb(1),u1,u2,s1,s2)
        result[f'old_symmetry_gain_upper_at_{value}'] = ((-ell/2).exp()*bound).str(50)
    K = arb(3000000000000-128)
    d = (4*(-arb(120)/4).exp()).log1p()/2
    mass = 2*d-2*arb.pi()/K
    compensation = q('32/3')*d**3+128/(K*K)
    check(mass+compensation < 0, 'fixed eta=1 Selberg family obstruction at L120')
    result['selberg_L120_unregularized_mass'] = mass.str(50)
    result['selberg_eta1_compensation_upper'] = compensation.str(50)
    result['selberg_eta1_pole_transform_upper'] = (mass+compensation).str(50)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true', help='Recompute and compare without writing')
    args = parser.parse_args()
    ctx.prec = 512
    certificate_path = ROUND/'rebased_density_certificate.json'
    saved = json.loads(certificate_path.read_text(encoding='utf-8'))
    check(saved['schema'] == 'k4-rebased-cs-round5-v1', 'schema')
    check(saved['L0'] == '362' and saved['full_k4_proved'] is False, 'claimed range and scope')
    check(saved['n_lower_log'] == '181/2', 'integer exponent translation')
    check(saved['status'] == 'POINT_AND_ANALYTIC_RATES_CHECKED', 'status')
    for field, name in [('script_sha256','rebase_density.py'),('proof_sha256','PROOF.md')]:
        check(saved[field] == hashlib.sha256((ROUND/name).read_bytes()).hexdigest(), field)
    rows, scalars, k1_tangent = constants()
    check(saved['rows'][0] == ['5.069','9.461','167.8'], 'unchanged first published row')
    check(len(saved['rows']) == 12, 'row count')
    for i, derived in enumerate(rows,1):
        for j, exact in enumerate(derived):
            check(q(saved['rows'][i][j]) > exact, f'rounded row {i} column {j} is an upper bound')
            check(q(saved['rows'][i][j])-exact < q('1e-12'), 'twelve-place ceiling width')
    for name, ball in scalars.items():
        check(arb(saved['derivation']['scalars'][name]).contains(ball), f'saved scalar contains independent {name}')
    point, rates = point_bound(saved['L0'], saved['rows'], saved['point']['sigma_denominator'])
    claimed = q(saved['point']['delta_upper_rational'])
    check(point['total'] < claimed < 1, 'independent total under saved rational bound and one')
    for key, rate in rates.items():
        if key != 'sharper_main':
            check(arb(saved['decay_rates'][key]).contains(rate), f'decay rate {key}')
    report = dict(status='INDEPENDENT_SCALARS_ROWS_POINT_AND_RATES_PASSED', precision_bits=512,
        L0='362', n_lower_log='181/2', full_k4_proved=False,
        source='https://arxiv.org/html/2507.15184v2',
        scope='Independent numerical reimplementation plus separate written analytic review; not end-to-end formalization.',
        imports_author_code=False, scalar_checks=len(scalars), rounded_row_checks=33,
        sigma_cells=3*saved['point']['sigma_denominator']//8,
        point={key:ball.str(50) for key,ball in point.items()},
        decay_rates={key:ball.str(50) for key,ball in rates.items()},
        original_K1_upper=scalars['K1_upper'].str(50), unused_improved_K1_upper=k1_tangent.str(50),
        additional_audit_bounds=additional_bounds(),
        input_sha256={name:hashlib.sha256((ROUND/name).read_bytes()).hexdigest()
            for name in ['rebase_density.py','PROOF.md','rebased_density_certificate.json']},
        checker_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    output = AUDIT/'independent_replay.json'
    if args.verify:
        check(json.loads(output.read_text(encoding='utf-8')) == report, 'independent replay report differs')
    else:
        output.write_text(json.dumps(report,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
    print(report['status'])
    print('Independent point total:', point['total'].str(50))
    print('Unused sharper K1:', k1_tangent.str(40))


if __name__ == '__main__':
    main()
