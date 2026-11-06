"""Check a sufficient condition for k=4, NOT the proposed density lemma D8.

This script proves no new zero-density bound and adds no certified coverage.
It performs only the scalar Arb checks used in K4_DENSITY_TARGET_ROUND5.md.
It reads no other project code or data and writes no files.
"""

import argparse

from flint import arb, ctx


def evaluate(precision=256):
    ctx.prec = precision
    L = arb(1131) / 10
    H = arb(3000000000000)
    A, B, zc = arb(16) / 7, arb(256) / 7, arb(16)
    q = 1 + (L / 4).exp() / 4
    lam = L - arb(8) / 3 * q.log()
    J1 = A * ((zc / A).log() + 2)
    p = arb(2) / 3
    J23 = (A * (zc ** (p - 1) - A ** (p - 1)) / (p - 1)
           + 2 * B * zc ** (p - 2) / (2 - p))
    J1_log = A * ((zc.log() ** 2 - A.log() ** 2) / 2
                  + 2 * (zc.log() + 1))
    baseline = 2 * (-3 * L / 8).exp() * q * (q.log() * J1 + J1_log)
    density = 16 * L / lam * (
        J23 * ((-lam / 8).exp() - (-lam / 4).exp())
        + J1 * ((-lam / 4).exp() - (-3 * lam / 8).exp())
    )
    eps = 4 * (-L / 4).exp()
    prime_powers = (arb(8) / 7 / (8 * arb(2).log())
                    * (1 + eps).sqrt() * (L + (1 + eps).log()) ** 2
                    * (-L / 4).exp())
    trivial_zeros = (-3 * L).exp() / (1 - (-2 * L).exp())
    total = baseline + density + prime_powers + trivial_zeros
    density_decay = arb(1) / 24 - 1 / L
    baseline_decay = arb(1) / 8 - 1 / (4 * (A * q).log())
    checks = {
        "height_domain_for_total_count": A * q > arb(10) ** 12,
        "positive_lambda": lam > 0,
        "positive_density_decay": density_decay > 0,
        "positive_baseline_decay": baseline_decay > 0,
        "prime_power_monotonicity": 2 / L < arb(1) / 4,
        "uniform_budget_below_0959": total < arb(959) / 1000,
        "uniform_budget_below_one": total < 1,
        "D8_at_sigma_5_8_is_below_total_cap": H.log() > 8,
    }
    values = {
        "L0": L, "H": H, "q0": q, "first_height_Aq0": A * q,
        "lambda0": lam, "J_1": J1, "J_2_3": J23,
        "J_1_log": J1_log, "baseline": baseline,
        "hypothetical_D8_density": density, "prime_powers": prime_powers,
        "trivial_zeros": trivial_zeros, "conditional_total": total,
        "density_decay": density_decay, "baseline_decay": baseline_decay,
    }
    if not all(checks.values()):
        raise AssertionError(checks)
    return values, checks


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=256)
    args = parser.parse_args()
    values, checks = evaluate(args.precision)
    print("CONDITIONAL REDUCTION ONLY: D8 REMAINS UNPROVED; NO NEW COVERAGE.")
    print(f"Arb precision: {args.precision} bits")
    for name, value in values.items():
        print(f"{name}: {value.str(30)}")
    for name, passed in checks.items():
        print(f"{name}: {passed}")
