"""Independent Arb scalar certificate for the round5 Selberg overshoot lemma.

All writes remain beside this script; --verify writes nothing.
Analytic proof: SELBERG_OVERSHOOT.md. This is not end-to-end formalization.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import flint
from flint import arb, ctx

HERE = Path(__file__).resolve().parent


def certify():
    ctx.prec = 256
    pi = arb.pi()
    q = lambda n, d=1: arb(n) / d
    lo, hi = q(1131, 10), q(1131124367, 10000000)
    H = arb(3000175332799)  # One below the published RH verification height.
    w = arb(320000)
    K, T = H + w, H + w + 64
    d = lambda L: (4 * (-L / 4).exp()).log1p() / 2
    dlo, dhi = d(lo), d(hi)
    clo, chi = lo + dlo, hi + dhi
    m = 2 * dhi - 2 * pi / K
    U = 2 * dlo + 2 * pi / K
    V = 2 * K * U
    M = 2 * (clo / 2).cosh() * (m - 2 * dlo**3)
    Zlow = 2 * H * H.log() * U
    arch = V / (2 * pi) * (7 + (1 + K).log() + 2 / pi.sqrt())
    pp = dlo.exp() * (hi + 2 * dlo)**2 / (2 * arb(2).log())

    R = lambda t: q(137, 1000) * t.log() + q(443, 1000) * t.log().log() + q(1588, 1000)
    a = (T / (2 * pi)).log() / (2 * pi)
    b = R(T) + R(H)
    A, B = 2 * pi / K**2, 8 * pi**2 / (9 * K**3)
    I1 = w + 1 / pi.sqrt()
    I2 = w**2 + 2 + w / pi.sqrt()
    I3 = w**3 + 6 * w + (w**2 + 4) / pi.sqrt()
    edge_integral = a * (A * I2 / 2 + B * I3 / 3)
    endpoint_error = b * (A * I1 + B * I2)
    deep_and_tail = V / (2 * pi.sqrt()) * T**2 * (2 + q(4, 64**2)) * arb(-1024).exp()
    amplification = 2 * (3 * chi / 8).cosh() * q(9, 256).exp()
    Zhigh = amplification * (edge_integral + endpoint_error + deep_and_tail)
    cost = Zlow + Zhigh + arch + pp
    Lcrit = -4 * ((2 * pi / H).expm1() / 4).log()

    vals = dict(Lcrit=Lcrit, overshoot_in_L=hi-Lcrit, bandwidth_excess=w,
                mass_min=m, U=U, V=V, local_density_slope=a, count_remainder=b,
                pole_lower=M, low_zeros_upper=Zlow, high_zeros_upper=Zhigh,
                archimedean_upper=arch, positive_prime_powers_upper=pp,
                all_costs_upper=cost, strict_margin_lower=M-cost,
                relative_cost_upper=cost/M, edge_integral=edge_integral,
                endpoint_error=endpoint_error, deep_and_tail=deep_and_tail)
    checks = dict(interval=hi-lo, inside_verified_RH=arb(3000175332800)-H,
                  positive_bandwidth=K, half_band_clearance=H-K/2-64,
                  positive_mass=m, positive_regularized_mass=m-2*dlo**3,
                  above_finite_RH_positive_mass_threshold=hi-Lcrit,
                  source_height=H-2, count_relaxation=H/2-q(3043,1000),
                  count_log_positive=H.log()-1, monotone_half_width=dlo-dhi,
                  monotone_center=chi-clo, prime_extraction_margin=M-cost,
                  relative_cost_less_than_four_fifths=q(4,5)-cost/M,
                  negligible_far_tail=arb(10)**(-300)-amplification*deep_and_tail)
    nmin = int((lo/4).exp().floor().unique_fmpz()) + 1
    nmax = int((hi/4).exp().floor().unique_fmpz())
    checks.update(first_integer=4*arb(nmin).log()-lo,
                  preceding_integer=lo-4*arb(nmin-1).log(),
                  last_integer=hi-4*arb(nmax).log(),
                  following_integer=4*arb(nmax+1).log()-hi)
    for name, value in checks.items():
        if not value > 0:
            raise ValueError(f"Failed strict scalar premise {name}: {value}")
    show = lambda x: x.str(55, radius=True, more=True)
    return dict(status="CANDIDATE: scalar checks PASS; pending independent analytic review and second implementation; not merged into formal coverage",
                precision_bits=256, python_flint=flint.__version__,
                QRH_7_over_8_assumed=True, CS_density_used=False,
                L_interval=["1131/10", "1131124367/10000000"],
                H=str(H.unique_fmpz()), K=str(K.unique_fmpz()), T=str(T.unique_fmpz()),
                n_interval_inclusive=[str(nmin), str(nmax)],
                values={k:show(v) for k,v in vals.items()},
                checks={k:dict(ball=show(v), passed=True) for k,v in checks.items()},
                proof_sha256=hashlib.sha256((HERE/'SELBERG_OVERSHOOT.md').read_bytes()).hexdigest(),
                script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify', action='store_true')
    args = parser.parse_args()
    result = certify()
    out = HERE / 'selberg_overshoot.json'
    if args.verify:
        if json.loads(out.read_text(encoding='utf-8')) != result:
            raise ValueError('Saved output differs from read-only recomputation')
        print('VERIFIED:', len(result['checks']), 'strict scalar premises')
    else:
        out.write_text(json.dumps(result, ensure_ascii=False, indent=2)+'\n', encoding='utf-8')
        print('WROTE', out)
    for k in ('pole_lower','high_zeros_upper','all_costs_upper','strict_margin_lower','relative_cost_upper'):
        print(k, result['values'][k])
    print('n interval', result['n_interval_inclusive'])
