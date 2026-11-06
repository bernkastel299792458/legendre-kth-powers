"""Certify the QRH + Chourasiya--Simonic k=4 tail for log(x)>=700.

The analytic proof is research/TAIL_BOUND_CS.md. Density and zero-count inputs
are from CS arXiv:2507.15184v2; CHJII arXiv:2402.04272v3 supplies the explicit
formula. No FKS density estimate or FKS table is used. --verify is read-only.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import platform

import flint
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_OUTPUT = ROOT / "results" / "tail_cs_certificate.json"
PRECISION_BITS = 256
L0 = 700
CS_URL = "https://arxiv.org/html/2507.15184v2"
CHJ_URL = "https://arxiv.org/html/2402.04272v3"


def q(n: int, d: int = 1) -> arb:
    return arb(n) / d


def show(value: arb) -> str:
    return value.str(60, radius=True, more=True)


def certify() -> dict:
    ctx.prec = PRECISION_BITS
    L, mu, log2 = arb(L0), q(9, 32), arb(2).log()
    u = mu * L + log2
    lam = L - q(8, 3) * u
    checks = {}

    def positive(name: str, expression: arb, reason: str) -> None:
        passed = bool(expression > 0)
        checks[name] = {"positive_expression_ball": show(expression),
                        "passed": passed, "reason": reason}
        if not passed:
            raise ValueError(f"Unproved positivity for {name}: {expression}")

    positive("log_x_above_40", L - 40, "L increases; CHJII Table 1 starts at 40.")
    positive("log_2_above_half", log2 - q(1, 2), "Constant; also implies log(2)>0.")
    positive("log_2_below_one", 1 - log2, "Constant; yields log(x+h)<=L+1 when h<x.")
    positive("h_less_than_x", 1 - 4 * (-L / 4).exp(), "4*exp(-L/4) decreases.")
    positive("height_above_51", mu * L - arb(51).log(), "log(T)=mu*L increases.")
    positive("height_above_endpoint_log_squared", mu * L - 2 * (L + 1).log(),
             "T>(L+1)^2 implies T>log(x)^2 and T>log(x+h)^2.")
    positive("height_log_squared_margin_increases", mu - 2 / (L + 1),
             "This derivative increases with L.")
    positive("height_strict_upper_bound",
             1 - 4 * (-(q(1, 2) - mu) * L).exp() - 2 * (-L / 2).exp(),
             "Equivalent to T<(sqrt(x)-2)/4; both subtracted terms decrease.")
    positive("CS_height_above_H_RH", u - arb(3 * 10**12).log(),
             "CS Corollary 1 and equation (11) apply for U>=3*10^12.")
    positive("counting_height_above_20", u - arb(20).log(),
             "Ensures U/2+0.43<U in the relaxation of CS equation (11).")
    positive("lambda_positive", lam, "lambda=L/4-(8/3)log(2), derivative 1/4.")
    positive("lambda_increases", q(1, 4), "Constant positive derivative.")
    positive("count_term_decreases", q(3, 32) - mu / u,
             "Negative logarithmic derivative of 4*u*exp(-3L/32).")
    positive("log_height_above_one", u - 1,
             "For u>1, the CS log power q(sigma)<=3 can be enlarged to u^3.")
    positive("density_core_decreases", q(1, 32) - 3 * mu / u,
             "Negative logarithmic derivative of u^3*exp(-lambda/8).")
    positive("density_lower_order_decreases", q(1, 8) - 2 * mu / u,
             "The log derivative of (8.29*u^2+147*u)*exp(-L/8) is at most 2*mu/u-1/8.")
    positive("CHJ_remainder_decreases", q(1, 32) - 3 / (3 * L + 2),
             "Negative logarithmic derivative of (3L+2)*exp(-L/32).")
    positive("prime_power_term_decreases", q(1, 4) - 2 / (L + 1),
             "Negative logarithmic derivative of (L+1)^2*exp(-L/4).")
    positive("right_endpoint_charge_decreases", q(3, 4) - 1 / (L + 1),
             "Negative logarithmic derivative of (L+1)*exp(-3L/4).")

    terms = {
        "low_real_part_zeros": 4 * u * (-3 * L / 32).exp(),
        "CS_density_main": q(1122, 25) * u**3 * L / lam * (-lam / 8).exp(),
        "CS_density_lower_order": 2 * (q(829, 100) * u**2 + 147 * u) * (-L / 8).exp(),
        "CHJ_remainder": q(1447, 2000) * (3 * L + 2) * (-L / 32).exp(),
        "prime_powers": q(1, 2) * (L + 1)**2 * (-L / 4).exp(),
        "right_endpoint_charge": q(1, 4) * (L + 1) * (-3 * L / 4).exp(),
    }
    total = sum(terms.values(), arb(0))
    positive("total_less_than_one", 1 - total, "With monotonicity, holds for all L>=700.")
    positive("total_less_than_14_over_25", q(14, 25) - total, "Convenient strict rational envelope.")
    if len(checks) != 21:
        raise ValueError("Unexpected number of numerical premises")
    return {
        "schema": "legendre-k4-CS-tail-v1",
        "status": "PASS: numerical premises of the documented analytic tail proof",
        "scope": "Conditional on QRH beta<=7/8 and the stated CS/CHJII literature inputs; not all n and not Lean formalization.",
        "statement": "For every real x>=exp(700), (x,x+4*x^(3/4)) contains a prime; hence for every integer n>=exp(175), (n^4,(n+1)^4) contains a prime.",
        "arithmetic": {"python": platform.python_version(), "python_flint": flint.__version__,
                       "precision_bits": PRECISION_BITS},
        "parameters_exact": {"L0": str(L0), "mu": "9/32", "T": "x^(9/32)", "U": "2*T",
                             "h": "4*x^(3/4)", "CS_source_c1": "2177/100",
                             "CS_used_c1": "561/25", "CS_c2": "829/100", "CS_c3": "147",
                             "CHJ_alpha": "1/2", "CHJ_omega": "0", "CHJ_M": "1447/500"},
        "auxiliary_balls": {"log_2": show(log2), "u": show(u), "lambda": show(lam),
                            "lambda_prime_L_minus_lambda": show(L / 4 - lam)},
        "normalized_error_term_balls": {name: show(value) for name, value in terms.items()},
        "normalized_total_ball": show(total),
        "positive_margin_ball": show(1 - total),
        "rational_total_upper_bound": "14/25",
        "checks": checks,
        "source_inputs": [
            {"name": "QRH", "assumption": "Every nontrivial zeta zero has beta<=7/8; accepted research premise."},
            {"name": "CS density", "url": CS_URL, "location": "Corollary 1, Table 1, displayed uniform bound following Corollary 1",
             "input": "For 5/8<=sigma<=7/8 and U>=3*10^12: N<=21.77*U^[3(1-sigma)/(2-sigma)]*log(U)^[(7-5sigma)/(2-sigma)]+8.29*log(U)^2+147*log(U).",
             "relaxation": "21.77<=22.44; p(sigma)<=8(1-sigma)/3; q(sigma)<=3; log(U)>1."},
            {"name": "CS zero count", "url": CS_URL, "location": "Equation (11), first inequality, valid for U>=H_RH",
             "input": "N(U)<=U/(2*pi)*log(U/(2*pi*e))+0.43*log(U).",
             "relaxation": "For U>=3*10^12>20, this is less than (U/2+0.43)*log(U)<U*log(U)."},
            {"name": "CHJII", "url": CHJ_URL, "location": "Theorem 1.3 and Table 1, log(x_M)=40 row",
             "input": "Common T* in [T,2T]; alpha=1/2, omega=0, M=2.894; max(51,log(x)^2)<T<(sqrt(x)-2)/4."},
        ],
        "FKS_density_or_table_used": False,
        "proof_document": "research/TAIL_BOUND_CS.md",
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "limitations": ["The listed upstream statements and table values are accepted, not independently rederived.",
                        "The infinite range is justified by symbolic monotonicity, not point sampling.",
                        "No claim is made here for x<exp(700), and no optimality of 700 is asserted.",
                        "Decimal balls describe computed enclosures; decisions use rigorous Arb comparisons."],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--verify", action="store_true", help="Read-only comparison with the saved certificate")
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()
    certificate = certify()
    if args.verify:
        saved = json.loads(args.output.read_text(encoding="utf-8"))
        if saved != certificate:
            raise ValueError("Saved certificate differs from recomputed values or metadata")
        print("PASS: saved certificate exactly matches read-only recomputation")
    else:
        args.output.parent.mkdir(parents=True, exist_ok=True)
        args.output.write_text(json.dumps(certificate, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(certificate["status"])
    print("L0=700; total:", certificate["normalized_total_ball"])
    print("Strict rational envelope: total < 14/25 < 1; checks:", len(certificate["checks"]))


if __name__ == "__main__":
    main()
