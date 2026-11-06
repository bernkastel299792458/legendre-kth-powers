"""Scalar Arb certificate for a Gaussian-regularized bandlimited minorant.

The proof and exact normalization are in research/K4_BANDLIMITED_ROUND3.md.
This is a new local interval, not a certificate for the unresolved k=4 gap.
No QRH or zero-density hypothesis is needed for the certified short segment:
finite-height RH, a classical total zero count, and Guinand--Weil suffice.
--verify is read-only. Run with python -B to avoid bytecode files.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import flint
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "k4_bandlimited_round3.json"
PROOF = ROOT / "research" / "K4_BANDLIMITED_ROUND3.md"
PRECISION = 256


def q(n: int, d: int = 1) -> arb:
    return arb(n) / d


def show(v: arb) -> str:
    return v.str(55, radius=True, more=True)


def half_width(L: arb) -> arb:
    return (4 * (-L / 4).exp()).log1p() / 2


def certificate() -> dict:
    ctx.prec = PRECISION
    lo, hi = q(5473, 50), q(225, 2)
    H, r, pi = arb(3 * 10**12), q(9, 10), arb.pi()
    d_lo, d_hi = half_width(lo), half_width(hi)
    c_lo, c_hi = lo + d_lo, hi + d_hi
    # d decreases and c=L+d increases for all real L.
    K_max = 4 * r / d_hi
    gap = H - K_max
    mass_coefficient = pi * (2 / (3 * r) - 1 / (2 * r**3))
    absolute_mass_coefficient = pi * (2 / (3 * r) + 1 / (2 * r**3))
    spectral_L1 = 2 * pi + 4 * pi / (3 * r**2)

    # All five are simultaneous uniform bounds on the complete closed L interval.
    pole_lower = 2 * (c_lo / 2).cosh() * (
        mass_coefficient * d_hi - 2 * d_lo**3
    )
    low_upper = 2 * H * H.log() * absolute_mass_coefficient * d_lo
    arch_upper = spectral_L1 / (2 * pi) * (
        7 + (1 + K_max).log() + 2 / pi.sqrt()
    )
    pp_upper = d_lo.exp() * (hi + 2 * d_lo)**2 / (2 * arb(2).log())
    # Use the full unconditional strip |beta-1/2|<1/2, not QRH.
    # gap>=64 gives exp(-gap^2/4)<=exp(-1024).
    high_upper = (
        2 * (c_hi / 2).cosh()
        * spectral_L1 / (2 * pi.sqrt()) * q(1, 16).exp()
        * H**2 * (1 + q(4, 64**2)) * arb(-1024).exp()
    )
    total_upper = low_upper + arch_upper + pp_upper + high_upper
    n_floor_lo = (lo / 4).exp().floor().unique_fmpz()
    n_floor_hi = (hi / 4).exp().floor().unique_fmpz()
    if n_floor_lo is None or n_floor_hi is None:
        raise ValueError("Arb failed to isolate unique integer floors")
    n_min, n_max = int(n_floor_lo) + 1, int(n_floor_hi)
    checks = {}

    def positive(name: str, value: arb, reason: str) -> None:
        passed = bool(value > 0)
        checks[name] = {"expression_ball": show(value), "passed": passed,
                        "reason": reason}
        if not passed:
            raise ValueError(f"Failed premise {name}: {value}")

    positive("positive_interval_width", hi - lo, "Exact closed L interval.")
    positive("positive_minorant_mass", mass_coefficient,
             "Equivalent to r^2>3/4; exact r=9/10.")
    positive("decreasing_d", d_lo - d_hi, "d'(L)=-epsilon/[8(1+epsilon)]<0.")
    positive("increasing_c", c_hi - c_lo, "c'(L)=1+d'(L)>7/8.")
    positive("center_outside_negative_reflection", c_lo - d_lo,
             "For u>=0, u+c>d; the reflected prime weight is nonpositive.")
    positive("spectral_support_below_verified_RH_by_64", gap - 64,
             "K increases with L; whole support has at least 64 height clearance.")
    positive("gaussian_pole_lower_positive", mass_coefficient * d_hi - 2 * d_lo**3,
             "exp(-v^2)cosh(v/2)<=1 and its loss inside |v|<d is at most 2d^3.")
    positive("counting_relaxation", H / 2 - q(3043, 1000),
             "Rosser implies N(T)<(T/2+3.043)log(T)<Tlog(T), T>=H.")
    positive("H_above_e", H.log() - 1,
             "log(T)<=T used only for T>=H.")
    positive("high_tail_below_1e_minus_300", arb(10)**(-300) - high_upper,
             "Analytic Stieltjes tail includes every positive-height zero above H.")
    positive("prime_extraction_margin", pole_lower - total_upper,
             "S>=pole-low-high-|arch|>positive prime-power contribution.")
    positive("total_relative_error_below_1e_minus_6", q(1, 10**6) - total_upper / pole_lower,
             "Convenient strict rational envelope, not an optimal bound.")
    positive("integer_min_in_interval", 4 * arb(n_min).log() - lo,
             "Checks the lower included integer independently of the exp floor.")
    positive("preceding_integer_below_interval", lo - 4 * arb(n_min - 1).log(),
             "Checks that the preceding integer lies strictly below the segment.")
    positive("integer_max_in_interval", hi - 4 * arb(n_max).log(),
             "Checks the upper included integer independently of the exp floor.")
    positive("following_integer_above_interval", 4 * arb(n_max + 1).log() - hi,
             "Checks that the following integer lies strictly above the segment.")

    # A separate, negative diagnostic at L=120. This reuses only the explicitly
    # stated admissible model from STRUCTURAL_ROUND2, not actual zeta zeros.
    L_model, W_model, delta_model = arb(120), arb(10**8), q(3749, 10000)
    d_model = half_width(L_model)
    c_model = L_model + d_model
    w_model = H * d_model
    base_at_H = pi * d_model * (
        ((4 * r - w_model)**3 - 4 * (2 * r - w_model)**3) / (48 * r**4)
        + (3 * w_model - 4 * r) / (8 * r**4)
    )
    lip_model = pi * d_model**2 * (1 / (3 * r**2) + 3 / (8 * r**4))
    complex_move_error = (delta_model**2 / 4).exp() * 2 / pi.sqrt() * lip_model
    model_transform_lower = base_at_H - lip_model * W_model - complex_move_error
    pole_model_upper = 2 * (c_model / 2).cosh() * absolute_mass_coefficient * d_model
    model_batch_ratio = (
        4 * 10**8 * (c_model * delta_model).cosh()
        * model_transform_lower / pole_model_upper
    )
    positive("model_B_spline_inner_piece", 2 * r - w_model,
             "At L=120, H is in the |t|<2a piece used to evaluate h0(H).")
    positive("model_complex_transform_real_positive", model_transform_lower,
             "Uniform over H<gamma<H+1e8 and |beta-1/2|=0.3749.")
    positive("model_batch_ratio_above_twelve", model_batch_ratio - 12,
             "Admissible model quartets force this particular kernel's absolute-value budget above 12; not a statement about actual zeta zeros.")

    # Pure scale diagnostics; these are not additional covered L intervals.
    critical_L = 4 * (4 / ((2 * pi / H).exp() - 1)).log()
    return {
        "schema": "k4-gaussian-bandlimited-minorant-round3-v1",
        "status": "PASS: scalar premises for the documented continuous-interval argument",
        "statement": "For every real x with 109.46<=log(x)<=112.5, (x,x+4*x^(3/4)) contains a prime, subject to the named classical/literature inputs and the accompanying analytic proof.",
        "scope": "New local segment only; this certificate makes no claim for log(x)>112.5 and is not an end-to-end formalization.",
        "precision_bits": PRECISION,
        "python_flint": flint.__version__,
        "exact_parameters": {"L_min": "5473/50", "L_max": "225/2",
                             "r": "9/10", "eta": "1", "H": "3000000000000",
                             "clearance_used": "64", "off_line_bound_used": "1/2",
                             "n_min_inclusive": str(n_min), "n_max_inclusive": str(n_max)},
        "auxiliary_balls": {
            "d_at_L_min": show(d_lo), "d_at_L_max": show(d_hi),
            "c_at_L_min": show(c_lo), "c_at_L_max": show(c_hi),
            "K_max": show(K_max), "H_minus_K_max": show(gap),
            "mass_coefficient": show(mass_coefficient),
            "absolute_mass_coefficient": show(absolute_mass_coefficient),
            "spectral_L1_upper": show(spectral_L1),
        },
        "uniform_budget_balls": {
            "pole_lower": show(pole_lower), "low_zeros_upper": show(low_upper),
            "high_zeros_upper": show(high_upper), "archimedean_absolute_upper": show(arch_upper),
            "positive_prime_powers_upper": show(pp_upper),
            "all_costs_upper": show(total_upper), "positive_margin_lower": show(pole_lower-total_upper),
            "relative_cost_upper": show(total_upper/pole_lower),
        },
        "scale_diagnostics": {
            "Selberg_bandwidth_H_times_log_interval_equal_2pi_L": show(critical_L),
            "meaning": "Positive mass of a genuinely bandlimited interval minorant requires H*ell>2*pi under the stated Poisson summation hypotheses; this is not an impossibility theorem for all regularized kernels.",
            "H_times_half_width_at_L_120": show(H * half_width(arb(120))),
        },
        "structural_model_diagnostic": {
            "L": "120", "beta_right": "8749/10000", "positive_right_count": "100000000",
            "height_width": "100000000", "unregularized_transform_at_H": show(base_at_H),
            "global_spectral_Lipschitz_upper": show(lip_model),
            "complex_move_error_upper": show(complex_move_error),
            "transform_real_lower_over_window": show(model_transform_lower),
            "pole_upper": show(pole_model_upper), "normalized_quartet_batch_lower": show(model_batch_ratio),
            "scope": "Extends the existing model diagnostic to this specific noncompact regularized minorant family at r=9/10. Does not exclude other minorants or use the model as actual zeta data.",
        },
        "checks": checks,
        "sources": [
            {"url": "https://arxiv.org/pdf/1708.04122v2", "location": "Lemma 6, p.17", "use": "Guinand-Weil formula; angular Fourier normalization rederived in the document."},
            {"url": "https://arxiv.org/pdf/2004.09765v1", "location": "Theorem 1", "use": "RH verified beyond H=3e12."},
            {"url": "https://arxiv.org/html/2204.02588v3", "location": "Lemma 2.1, Remark 2.2", "use": "Classical Rosser total count constants only; no FKS density estimate."},
        ],
        "QRH_assumption_used": False,
        "CS_density_assumption_used": False,
        "literature_inputs_independently_reproved": False,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "proof_document": "research/K4_BANDLIMITED_ROUND3.md",
        "proof_sha256": hashlib.sha256(PROOF.read_bytes()).hexdigest(),
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="Read-only recomputation and exact comparison")
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
