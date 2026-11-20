"""Arb scalar certificate for the Selberg + Gaussian k=4 segment.

The complete analytic connections are in research/K4_SELBERG_ROUND4.md.
This script checks uniform bounds for every real 112.5<=log(x)<=113.1.
It imports no previous project code and never touches computation_branch.
--verify is read-only; use python -B to avoid writing bytecode.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import flint
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
PROOF = ROOT / "research" / "K4_SELBERG_ROUND4.md"
OUTPUT = ROOT / "results" / "k4_selberg_round4.json"
PRECISION = 256


def q(n: int, d: int = 1) -> arb:
    return arb(n) / d


def show(value: arb) -> str:
    return value.str(55, radius=True, more=True)


def half_width(L: arb) -> arb:
    return (4 * (-L / 4).exp()).log1p() / 2


def certificate() -> dict:
    ctx.prec = PRECISION
    lo, hi = q(225, 2), q(1131, 10)
    H, pi = arb(3 * 10**12), arb.pi()
    K = H - 128
    d_lo, d_hi = half_width(lo), half_width(hi)
    c_lo, c_hi = lo + d_lo, hi + d_hi
    mass_min = 2 * d_hi - 2 * pi / K
    spatial_L1_max = 2 * d_lo + 2 * pi / K
    spectral_L1_max = 2 * K * spatial_L1_max
    gaussian_mass_min = mass_min - 2 * d_lo**3

    pole_lower = 2 * (c_lo / 2).cosh() * gaussian_mass_min
    low_upper = 2 * H * H.log() * spatial_L1_max
    arch_upper = spectral_L1_max / (2 * pi) * (
        7 + (1 + K).log() + 2 / pi.sqrt()
    )
    pp_upper = d_lo.exp() * (hi + 2 * d_lo)**2 / (2 * arb(2).log())
    # The actual spectral clearance is 128; conservatively reuse clearance 64.
    # Full critical strip |beta-1/2|<1/2, without QRH or zero-density bounds.
    high_upper = (
        2 * (c_hi / 2).cosh() * spectral_L1_max / (2 * pi.sqrt())
        * q(1, 16).exp() * H**2 * (1 + q(4, 64**2)) * arb(-1024).exp()
    )
    all_costs = low_upper + high_upper + arch_upper + pp_upper
    relative_cost = all_costs / pole_lower
    floor_lo = (lo / 4).exp().floor().unique_fmpz()
    floor_hi = (hi / 4).exp().floor().unique_fmpz()
    if floor_lo is None or floor_hi is None:
        raise ValueError("Could not isolate unique integer floors")
    n_min, n_max = int(floor_lo) + 1, int(floor_hi)
    checks = {}

    def positive(name: str, expression: arb, reason: str) -> None:
        passed = bool(expression > 0)
        checks[name] = {"expression_ball": show(expression),
                        "passed": passed, "reason": reason}
        if not passed:
            raise ValueError(f"Unproved premise {name}: {expression}")

    positive("positive_L_interval", hi - lo, "Exact closed interval.")
    positive("d_decreases", d_lo - d_hi, "d'(L)=-epsilon/[8(1+epsilon)]<0.")
    positive("c_increases", c_hi - c_lo, "c'(L)>7/8 for all real L.")
    positive("center_exceeds_half_width", c_lo - d_lo,
             "For u>=0 the reflected term f(u+c) is nonpositive.")
    positive("positive_bandwidth", K, "Selberg frequency parameter K/(2*pi)>0.")
    positive("clearance_above_64", H - K - 64,
             "Constant bandwidth K=H-128; Gaussian high tail uses clearance 64.")
    positive("Selberg_mass_min_positive", mass_min,
             "Exact Selberg mass 2d-2*pi/K is minimized at L_max.")
    positive("spatial_L1_upper_positive", spatial_L1_max,
             "||f||1<=2d+2*pi/K, maximized at L_min.")
    positive("spectral_L1_upper_positive", spectral_L1_max,
             "Support[-K,K] and |G0|<=||f||1 imply ||G0||1<=2K||f||1.")
    positive("regularized_pole_mass_positive", gaussian_mass_min,
             "Only the positive part loses mass under exp(-v^2)cosh(v/2); loss<=2d^3.")
    positive("counting_relaxation", H / 2 - q(3043, 1000),
             "Classical Rosser bound implies N(T)<T*log(T) for every T>=H.")
    positive("counting_height_above_e", H.log() - 1,
             "All high-tail uses of log(T)<=T occur in the source domain T>=H.")
    positive("high_tail_below_1e_minus_300", arb(10)**(-300) - high_upper,
             "Full Gaussian/Stieltjes tail over gamma>H.")
    positive("prime_extraction_margin", pole_lower - all_costs,
             "Includes low/high zeros, absolute archimedean term and positive prime powers.")
    positive("relative_cost_below_1e_minus_6", q(1, 10**6) - relative_cost,
             "Strict convenient rational envelope; no claim of optimality.")
    positive("integer_min_in_interval", 4 * arb(n_min).log() - lo,
             "Independent logarithmic check of the first included integer.")
    positive("preceding_integer_below_interval", lo - 4 * arb(n_min - 1).log(),
             "Independent logarithmic check of the preceding integer.")
    positive("integer_max_in_interval", hi - 4 * arb(n_max).log(),
             "Independent logarithmic check of the last included integer.")
    positive("following_integer_above_interval", 4 * arb(n_max + 1).log() - hi,
             "Independent logarithmic check of the following integer.")

    return {
        "schema": "k4-selberg-gaussian-round4-v1",
        "status": "PASS: uniform scalar premises of the documented analytic segment proof",
        "statement": "For every real x with 112.5<=log(x)<=113.1, the open interval (x,x+4*x^(3/4)) contains a prime, using the stated classical and published literature inputs.",
        "scope": "This local certificate makes no claim for log(x)>113.1; scalar verification is not a formalization of Selberg or Guinand-Weil.",
        "precision_bits": PRECISION,
        "python_flint": flint.__version__,
        "exact_parameters": {
            "L_min": "225/2", "L_max": "1131/10", "H": "3000000000000",
            "K": "2999999999872", "Selberg_cycle_frequency": "K/(2*pi)",
            "Gaussian_eta": "1", "spectral_clearance": "128", "clearance_used": "64",
            "off_line_bound_used": "1/2", "n_min_inclusive": str(n_min),
            "n_max_inclusive": str(n_max), "rational_relative_cost_upper": "1/1000000",
        },
        "auxiliary_balls": {
            "d_at_L_min": show(d_lo), "d_at_L_max": show(d_hi),
            "c_at_L_min": show(c_lo), "c_at_L_max": show(c_hi),
            "Selberg_mass_min": show(mass_min), "spatial_L1_max": show(spatial_L1_max),
            "spectral_L1_max": show(spectral_L1_max),
            "Gaussian_pole_mass_min": show(gaussian_mass_min),
        },
        "uniform_budget_balls": {
            "pole_lower": show(pole_lower), "low_zeros_upper": show(low_upper),
            "high_zeros_upper": show(high_upper), "archimedean_absolute_upper": show(arch_upper),
            "positive_prime_powers_upper": show(pp_upper), "all_costs_upper": show(all_costs),
            "positive_margin_lower": show(pole_lower-all_costs),
            "relative_cost_upper": show(relative_cost),
        },
        "checks": checks,
        "sources": [
            {"url": "https://arxiv.org/pdf/1309.1506v1", "name": "Le-Vaaler, Sums of products of fractional parts", "location": "Equations (3.1)-(3.7), Lemma 3.1, pp.6-7", "use": "Selberg real entire L1 minorant, exact mass and Fourier support for every positive bandwidth; no integer-length assumption."},
            {"url": "https://arxiv.org/pdf/1708.04122v2", "location": "CMS Lemma 6, p.17", "use": "Guinand-Weil with angular Fourier normalization stated in the proof."},
            {"url": "https://arxiv.org/pdf/2004.09765v1", "location": "Platt-Trudgian Theorem 1", "use": "Finite RH beyond H=3e12."},
            {"url": "https://arxiv.org/html/2204.02588v3", "location": "FKS Lemma 2.1, Remark 2.2", "use": "Classical Rosser total-count constants only; no density estimate."},
        ],
        "QRH_assumption_used": False,
        "CS_density_assumption_used": False,
        "literature_inputs_independently_reproved": False,
        "proof_document": "research/K4_SELBERG_ROUND4.md",
        "proof_sha256": hashlib.sha256(PROOF.read_bytes()).hexdigest(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="Read-only recomputation and comparison")
    parser.add_argument("--output", type=Path, default=OUTPUT)
    args = parser.parse_args()
    data = certificate()
    if args.verify:
        saved = json.loads(args.output.read_text(encoding="utf-8"))
        if saved != data:
            raise ValueError("Saved certificate differs from recomputation")
        print("VERIFIED (read-only):", len(data["checks"]), "strict scalar checks")
    else:
        args.output.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
        print(data["status"])
    print(json.dumps(data["uniform_budget_balls"], indent=2))


if __name__ == "__main__":
    main()
