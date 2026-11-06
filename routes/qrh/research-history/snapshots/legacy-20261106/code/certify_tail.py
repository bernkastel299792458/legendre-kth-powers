"""Arb certificate for the k=4 infinite tail described in TAIL_BOUND.md.

This verifies numerical premises for an analytic monotonicity proof, not the
upstream QRH or cited analytic-number-theory theorems. No floating-point
literal is used to construct a mathematical constant.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import platform

import flint
from flint import arb, ctx


PRECISION_BITS = 256
L0_INTEGER = 800
PROJECT = Path(__file__).resolve().parents[1]
OUTPUT = PROJECT / "results" / "tail_certificate.json"


def q(numerator: int, denominator: int = 1) -> arb:
    return arb(numerator) / denominator


def ball(value: arb) -> str:
    """A decimal ball enclosure, including outward conversion error."""
    return value.str(60, radius=True, more=True)


def certify() -> dict:
    ctx.prec = PRECISION_BITS
    L = arb(L0_INTEGER)
    mu = q(9, 32)
    log2 = arb(2).log()
    u = mu * L + log2
    lam = L - q(8, 3) * u - 2 * u.log()
    checks: dict[str, dict] = {}

    def positive(name: str, value: arb, explanation: str) -> None:
        passed = bool(value > 0)
        checks[name] = {
            "positive_expression_ball": ball(value),
            "passed": passed,
            "explanation": explanation,
        }
        if not passed:
            raise RuntimeError(f"Unproved strict positivity: {name}: {value}")

    # Preconditions of the cited inputs and elementary relaxations.
    positive("log_x_above_40", L - 40, "The CHJII Table 1 row starts at log(x)=40.")
    positive("log_2_above_half", log2 - q(1, 2), "Used in the elementary prime-power bound.")
    positive("log_2_below_one", 1 - log2, "Gives log(x+h) <= L+1 once h<=x.")
    positive("h_less_than_x", 1 - 4 * (-L / 4).exp(), "h/x decreases for L>=L0.")
    positive("height_above_51", mu * L - arb(51).log(), "log(T)>log(51), increasing in L.")
    positive(
        "height_above_endpoint_log_squared",
        mu * L - 2 * (L + 1).log(),
        "Stronger than T>L^2: also T>(log(x+h))^2 because log(x+h)<=L+1.",
    )
    positive(
        "height_log_squared_margin_increases",
        mu - 2 / (L + 1),
        "Derivative of mu*L-2*log(L+1) is positive and increases.",
    )
    positive(
        "height_upper_bound",
        1 - 4 * (-(q(1, 2) - mu) * L).exp() - 2 * (-L / 2).exp(),
        "Equivalent to T<(sqrt(x)-2)/4; both subtracted terms decrease.",
    )
    positive("density_height_above_H0", u - arb(3 * 10**12).log(), "U=2T exceeds the FKS height H0.")
    positive("counting_height_above_20", u - arb(20).log(), "The elementary relaxation N(U)<=U*log(U) applies.")
    positive("lambda_positive", lam, "Lambda increases because lambda'=1/4-9/(16u)>0.")
    positive("lambda_increases", q(1, 4) - q(9, 16) / u, "Its derivative increases with u.")

    # These inequalities, with the symbolic derivatives in TAIL_BOUND.md,
    # imply monotonicity on the complete unbounded range L >= L0.
    positive("count_term_decreases", q(3, 32) - mu / u, "Negative logarithmic derivative of 4*u*exp(-3L/32).")
    positive("u_exceeds_e", u.log() - 1, "Ensures lambda'*L-lambda>0, hence L/lambda decreases.")
    positive(
        "density_core_decreases",
        q(1, 32) - q(117, 128) / u,
        "Negative logarithmic derivative of u^3*exp(-lambda/8).",
    )
    positive("density_log_term_decreases", q(1, 8) - 2 * mu / u, "Negative logarithmic derivative of u^2*exp(-L/8).")
    positive("CHJ_remainder_decreases", q(1, 32) - 3 / (3 * L + 2), "Negative logarithmic derivative of (3L+2)*exp(-L/32).")
    positive("prime_power_term_decreases", q(1, 4) - 2 / (L + 1), "Negative logarithmic derivative of (L+1)^2*exp(-L/4).")
    positive("right_endpoint_charge_decreases", q(3, 4) - 1 / (L + 1), "Negative logarithmic derivative of (L+1)*exp(-3L/4).")

    terms = {
        "low_real_part_zeros": 4 * u * (-3 * L / 32).exp(),
        "density_main": q(87097, 2500) * u**3 * L / lam * (-lam / 8).exp(),
        "density_log_term": q(26477, 2500) * u**2 * (-L / 8).exp(),
        "CHJ_remainder": q(1447, 2000) * (3 * L + 2) * (-L / 32).exp(),
        "prime_powers": q(1, 2) * (L + 1) ** 2 * (-L / 4).exp(),
        "right_endpoint_charge": q(1, 4) * (L + 1) * (-3 * L / 4).exp(),
    }
    total = sum(terms.values(), arb(0))
    positive("total_less_than_one", 1 - total, "Combined with analytic monotonicity, proves the infinite tail.")
    positive("total_less_than_117_over_1000", q(117, 1000) - total, "A convenient rational envelope for the numerical result.")

    return {
        "status": "PASS: numerical premises of the documented analytic tail proof",
        "scope": "Conditional on QRH beta<=7/8 and the explicitly listed literature inputs; not a full k=4 proof and not Lean verification.",
        "statement": "For every real x>=exp(800), a prime lies strictly between x and x+4*x^(3/4). Hence consecutive fourth powers contain a prime for integer n>=exp(200).",
        "arithmetic": {"library": "python-flint / Arb", "python_flint_version": flint.__version__, "precision_bits": PRECISION_BITS, "python_version": platform.python_version()},
        "parameters_exact": {"L0": "800", "mu": "9/32", "h": "4*x^(3/4)", "T": "x^(9/32)", "U": "2*T", "CHJ_alpha": "1/2", "CHJ_omega": "0", "CHJ_M": "1447/500", "FKS_c1": "87097/5000", "FKS_c2": "26477/5000"},
        "auxiliary_balls": {"log_2": ball(log2), "u": ball(u), "lambda": ball(lam)},
        "normalized_error_term_balls": {name: ball(value) for name, value in terms.items()},
        "normalized_total_ball": ball(total),
        "positive_margin_ball": ball(1 - total),
        "rational_total_upper_bound": "117/1000",
        "checks": checks,
        "source_inputs": [
            {"name": "QRH", "assumption": "Every nontrivial zeta zero has real part beta<=7/8; accepted research premise, not independently reverified here."},
            {"name": "FKS", "url": "https://arxiv.org/html/2204.02588v3", "location": "Theorem 2.7, Corollary 2.9, Table 8 (the a1=0.77 block)", "assumption": "Uniform density bound for sigma in [5/8,7/8], U>=3*10^12, using c1=17.4194 and c2=5.2954."},
            {"name": "CHJII", "url": "https://arxiv.org/html/2402.04272v3", "location": "Theorem 1.3 and Table 1", "assumption": "A common T* in [T,2T] in the short-interval formula, with log(x)>=40, alpha=1/2, omega=0, M=2.894."},
            {"name": "Zero count", "url": "https://arxiv.org/html/2204.02588v3", "location": "Lemma 2.1 and Remark 2.2", "assumption": "Rosser total-zero count with 0.137, 0.443, 1.588; relaxed analytically to N(U)<=U*log(U) for U>=20."},
        ],
        "proof_document": "research/TAIL_BOUND.md",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "limitations": [
            "The literature statements and their numerical constants are accepted inputs, not rederived by this script.",
            "The unbounded range is covered by the symbolic monotonicity proof in TAIL_BOUND.md, not by sampling.",
            "This certificate covers only x>=exp(800), leaving the lower range to separate arguments.",
            "Decimal ball strings are enclosures; the pass/fail decisions use Arb interval comparisons directly.",
        ],
    }


if __name__ == "__main__":
    certificate = certify()
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(json.dumps(certificate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    print(certificate["status"])
    print("L0=800; total:", certificate["normalized_total_ball"])
    print("Strict rational envelope: total < 117/1000 < 1")
    print("Certificate:", OUTPUT)
