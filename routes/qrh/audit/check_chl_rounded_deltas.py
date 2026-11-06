#!/usr/bin/env python3
"""Rigorous Arb check of printed CHL parameters -> Delta, and only that map.

Source: Cully-Hugill--Lee, arXiv:2103.05986v3, printed page 12, Table 2.
The printed decimal parameters are treated as exact rationals. No Python
floating-point literals or mpmath computations enter this diagnostic.

This does NOT certify the authors' constraint1, numerical integrals, the CHL
theorem, or the exact contents of the unavailable published corrigendum.

Run from any directory (tested with Python 3.12.10 and python-flint 0.9.0):
    python check_chl_rounded_deltas.py --output chl_rounded_deltas_arb.json
"""
from __future__ import annotations

import argparse
from decimal import Decimal
import hashlib
import json
from pathlib import Path
import platform

import flint
from flint import arb, ctx


# log(x0), m, delta, a, reported Delta; decimal strings come from Table 2.
ROWS = (
    ("log(4*10^18)", 5, "3.341898e-8", "0.2173221", 39097000),
    ("43", 5, "3.123609e-8", "0.2172087", 41816800),
    ("46", 4, "6.874386e-9", "0.1813398", 163940000),
    ("50", 5, "1.208702e-9", "0.2101882", 1061200000),
    ("55", 9, "1.757070e-10", "0.2789679", 10288400000),
    ("60", 30, "4.873014e-11", "0.3832708", 76918400000),
    ("75", 82, "6.286379e-11", "0.4603978", 174043000000),
    ("90", 82, "6.270787e-11", "0.4628348", 184304000000),
    ("105", 80, "6.183604e-11", "0.4641109", 191886000000),
    ("120", 84, "6.335103e-11", "0.4660744", 197917000000),
    ("135", 90, "6.590771e-11", "0.4681018", 202553000000),
    ("150", 79, "6.090246e-11", "0.4666782", 207053000000),
)
EXPECTED_BELOW = {"50", "60", "75", "90", "105", "135"}


def exact_decimal_ball(text: str) -> tuple[arb, dict[str, str]]:
    """Enclose the exact finite decimal, via its exact rational expansion."""
    numerator, denominator = Decimal(text).as_integer_ratio()
    rational = f"{numerator}/{denominator}"
    return arb(rational), {"numerator": str(numerator), "denominator": str(denominator)}


def dyadic(exact: arb) -> dict[str, str | int]:
    """Export a finite exact Arb endpoint as mantissa * 2^exponent."""
    mantissa, exponent = exact.man_exp()
    return {"mantissa": str(mantissa), "exponent": int(exponent)}


def enclosure(value: arb) -> dict:
    return {
        "decimal_ball": value.str(70, radius=True),
        "lower_dyadic": dyadic(value.lower()),
        "upper_dyadic": dyadic(value.upper()),
    }


def run(precision: int) -> dict:
    if precision < 128:
        raise ValueError("Use at least 128 bits for this cancellation-sensitive formula.")
    ctx.prec = precision
    records = []
    below = set()
    for log_x0, m, delta_text, a_text, reported in ROWS:
        delta, delta_rational = exact_decimal_ball(delta_text)
        a, a_rational = exact_decimal_ball(a_text)
        denominator = arb(1) - (arb(1) + delta * a) / (
            (delta / arb(m)).exp() * (arb(1) + delta * (arb(1) - a))
        )
        # A positive lower endpoint certifies that the reciprocal is defined.
        if not denominator.lower() > arb(0):
            raise ArithmeticError(f"Denominator positivity unresolved for {log_x0}.")
        generated = arb(1) / denominator
        difference = generated - arb(reported)
        if difference.upper() < arb(0):
            relation = "strictly_below_reported"
            below.add(log_x0)
        elif difference.lower() > arb(0):
            relation = "strictly_above_reported"
        else:
            raise ArithmeticError(f"Comparison unresolved for {log_x0}.")
        records.append({
            "log_x0": log_x0, "m": m,
            "printed_delta": delta_text, "delta_exact_rational": delta_rational,
            "printed_a": a_text, "a_exact_rational": a_rational,
            "reported_Delta": reported,
            "generated_Delta_enclosure": enclosure(generated),
            "difference_generated_minus_reported_enclosure": enclosure(difference),
            "certified_relation": relation,
        })
    if below != EXPECTED_BELOW:
        raise AssertionError(f"Unexpected certified below-set: {sorted(below)}")
    return {
        "schema_version": 1,
        "status": "RIGOROUS_ARB_PARAMETER_TO_DELTA_DIAGNOSTIC_COMPLETE",
        "source": {
            "url": "https://arxiv.org/pdf/2103.05986v3",
            "version": "2103.05986v3", "printed_page": 12, "table": 2,
            "pdf_sha256": "faf16820df427f883ba7ed32392ee93a9cd36b4b98500b9fcee022c01612d298",
        },
        "formula": "Delta = 1 / (1 - (1 + delta*a) / (exp(delta/m)*(1 + delta*(1-a))))",
        "input_semantics": "Printed finite decimals parsed as exact rationals; enclosed by Arb without Python floats.",
        "precision_bits": precision,
        "python_version": platform.python_version(),
        "python_flint_version": flint.__version__,
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "certified_below_log_x0": sorted(below, key=int),
        "certified_above_count": len(ROWS) - len(below),
        "rows": records,
        "scope_limitations": [
            "Certifies only the stated algebraic/exponential parameter-to-Delta map using Arb.",
            "Does not certify constraint1, quadrature, the CHL theorem, or Lean input CHLRows.",
            "Does not compare the unavailable published corrigendum table.",
            "Does not refute existence of nearby feasible witnesses for the reported Delta.",
            "This is not a Lean kernel proof; it relies on the correctness of Python and FLINT/Arb.",
        ],
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--precision", type=int, default=256)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = run(args.precision)
    payload = json.dumps(result, ensure_ascii=False, indent=2) + "\n"
    if args.output:
        args.output.write_text(payload, encoding="utf-8", newline="\n")
        print(json.dumps({
            "status": result["status"], "precision_bits": result["precision_bits"],
            "certified_below_log_x0": result["certified_below_log_x0"],
            "certified_above_count": result["certified_above_count"],
            "output": str(args.output),
        }))
    else:
        print(payload, end="")


if __name__ == "__main__":
    main()
