"""Recompute the first CHJII Table 1 row and scalar rounding bounds.

Original verifier transcribed from the displayed mathematical formulas after
inspection of the authors' notebook. No third-party code is executed.
This verifies scalar inequalities using Arb; it does not prove the analytic
theorem, the uniform endpoint reduction, or the journal/arXiv correspondence.

Run: python routes/qrh/audit/verify_input6_constant.py
Requires python-flint 0.9.0 and mpmath. Output is a JSON audit record beside
this file; no Lean files, paper files, or proof certificates are modified.
"""

from pathlib import Path
import hashlib
import json
import platform

import flint
from flint import arb, ctx
import mpmath as mp


def evaluate(F, exp, log, pi):
    """F(n,d) denotes the exact rational n/d, enclosed by the backend."""
    z = F(40)
    alpha = F(1, 2)
    lam = F(43, 100)
    theta_lower = F(8029, 10000)
    theta_upper = F(803, 1000)
    K = F(2033, 1000)
    M = F(1447, 500)
    q = F(357, 200)
    # The notebook's coefficient is slightly larger than the printed paper's.
    a1 = F(1) + F(1933784, 10**14)
    a2 = F(652, 625)
    c0 = F(1) + (exp(lam) - F(1)) / lam
    e1 = (2 * z + 2 * lam) / ((1 - alpha) * z)
    e2 = (a1 * exp((alpha - F(1, 2)) * z + lam / 2) / z
          + a2 * exp((alpha - F(2, 3)) * z + lam / 3) / z
          + exp((alpha - 1) * z))
    first = q * exp(F(1)) / (2 * lam**2 * z**2)
    common = q * exp((1 + 1 / z) * lam)
    second_e1 = common * c0 * e1 / (theta_lower * z)
    second_e2 = common * e2 / (2 * theta_lower**2)
    total = K + first + second_e1 + second_e2
    N = (9 - 18 * (log(F(4, 3)) - log(F(3, 2)))
         - 12 * log(F(2))) / (2 * pi)
    L = F(3) / (2 * pi)
    def theta_equation(y):
        return 2 * N / y**2 - 1 - L * y
    ksmall = (exp((alpha - 1) * z) * log(2 * pi) / z
              + exp((2 * alpha - 2) * z) * (9 + alpha * z) / (2 * pi * z))
    tmin = F(51)  # max(51, z) at z=40 for Appendix B, not Table 1's z^2.
    knonzf = exp(F(1)) / (pi * (1 - 1 / tmin)) * (1 + alpha**2 + 21 * alpha / z)
    kzf = 2 * alpha * exp(-1 / (F(5558691, 10**6) * alpha))
    ktotal = ksmall + knonzf + kzf
    return {
        'z': z, 'lambda': lam, 'a1': a1, 'c0': c0,
        'E1_normalized': e1, 'E2_normalized': e2,
        'K_rounded_input': K, 'first_Perron_term': first,
        'second_Perron_E1_term': second_e1, 'second_Perron_E2_term': second_e2,
        'M_reconstructed': total, 'M_margin': M - total,
        'N': N, 'four_N': 4 * N, 'N_rounding_margin': F(4461, 10000) - N,
        'four_N_rounding_margin': q - 4 * N,
        'theta_equation_at_lower': theta_equation(theta_lower),
        'theta_equation_at_upper': theta_equation(theta_upper),
        'K_small': ksmall, 'K_non_zero_free': knonzf, 'K_zero_free': kzf,
        'K_reconstructed': ktotal, 'K_margin': K - ktotal,
        'c0_theta_lower_minus_one': c0 * theta_lower - 1,
        'lambda_minus_theta_upper_over_min_T': lam - theta_upper / z**2,
        'upper_T_at_base_minus_lower_T': (exp(z / 2) - 2) / 4 - z**2,
    }


def main():
    ctx.prec = 256
    certified = evaluate(lambda n, d=1: arb(n) / d,
                         lambda x: x.exp(), lambda x: x.log(), arb.pi())
    mp.mp.dps = 80
    numerical = evaluate(lambda n, d=1: mp.mpf(n) / d, mp.exp, mp.log, mp.pi)
    positive = [
        'M_margin', 'K_margin', 'N_rounding_margin', 'four_N_rounding_margin',
        'theta_equation_at_lower', 'c0_theta_lower_minus_one',
        'lambda_minus_theta_upper_over_min_T', 'upper_T_at_base_minus_lower_T',
    ]
    checks = {name + '_positive': bool(certified[name] > 0) for name in positive}
    checks['theta_equation_at_upper_negative'] = bool(certified['theta_equation_at_upper'] < 0)
    assert all(checks.values()), checks
    script = Path(__file__).resolve()
    root = script.parents[3]
    download = root / 'routes/qrh/tmp/input_review_6/notebook_acquisition.json'
    # Record the pinned public source even when the ignored download is absent.
    source = {
        'url': 'https://raw.githubusercontent.com/DJmath1729/Riemann-von-Mangoldt-estimates/60a723c24f094c890c03ab1f7f48f3811e0277e5/RVM%20II%20Sections%203%2C4%20and%20Appendix%20B.nb',
        'commit': '60a723c24f094c890c03ab1f7f48f3811e0277e5',
        'sha256': 'eceec0f0cf038b14c2980907b90e89c3cd4c44b6acb969d898df6d7ac5c5e6b8',
    }
    if download.is_file():
        source = json.loads(download.read_text(encoding='utf-8'))
    result = {
        'scope': 'First row of CHJII Table 1; scalar formulas only; no optimization performed',
        'method': '80-decimal-digit mpmath recomputation plus 256-bit Arb interval comparisons',
        'limits': [
            'Scalar certification is not an interval proof over all x,T.',
            'Uniform validity also requires the analytic estimates and monotonic endpoint reductions.',
            'No formal Lean proof of the external theorem is supplied.',
            'The journal-to-arXiv text comparison remains incomplete.',
        ],
        'python': platform.python_version(), 'python_flint': flint.__version__,
        'mpmath': mp.__version__, 'arb_precision_bits': ctx.prec,
        'source_notebook': source,
        'script_sha256': hashlib.sha256(script.read_bytes()).hexdigest(),
        'mpmath_values': {k: mp.nstr(v, 70) for k, v in numerical.items()},
        'arb_enclosures': {k: str(v) for k, v in certified.items()},
        'certified_scalar_checks': checks,
    }
    output = script.with_name('input6_constant_check_2026-11-06.json')
    output.write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8', newline='\n')
    for name in ['M_reconstructed', 'M_margin', 'K_reconstructed', 'K_margin']:
        print(name, certified[name])
    print('Certified scalar checks:', len(checks), '/', len(checks))
    print('Output:', output)


if __name__ == '__main__':
    main()
