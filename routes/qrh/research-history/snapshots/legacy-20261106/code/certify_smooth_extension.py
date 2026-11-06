#!/usr/bin/env python3
"""Rigorous positive-upper-sum extension toward log(x)=375, ending at 400.

The certified kernel and CS v2 density helpers are reused read-only from the
fixed certify_smooth_segment.py dependency. Every L/sigma/height endpoint is
rational. --single and --verify never write certificates.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import platform
import runpy
import time
from datetime import datetime, timedelta, timezone
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
OUTPUT = ROOT / "results" / "smooth_extension_certificate.json"
DEPENDENCIES = {
    "code/certify_smooth_segment.py": "ec7e6d218e09967d9161f44074c35ecdce09eb6a3a3a3d307db1e5b36083d21e",
    "research/SMOOTH_CERTIFICATE.md": "a035e1a8704dbacf96e5be22644af29c73d46de140c9611bbbdfee4b3c9db96d",
}
SOURCE = "https://arxiv.org/html/2507.15184v2"
BALANCED_SCHEDULE = (
    ("375", "376", "1/4", 16384, 32),
    ("376", "380", "1/2", 8192, 32),
    ("380", "400", "1", 4096, 16),
)
_BASE = None


def require(condition, message):
    if not condition:
        raise ValueError(message)


def checked_dependencies():
    for relative, expected in DEPENDENCIES.items():
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        require(actual == expected, f"Dependency hash mismatch: {relative}")
    return dict(DEPENDENCIES)


def base():
    global _BASE
    if _BASE is None:
        checked_dependencies()
        _BASE = runpy.run_path(str(ROOT / "code" / "certify_smooth_segment.py"),
                               run_name="smooth_extension_fixed_dependency")
    return _BASE


def certify_cell(left, right, sigma_denominator=4096, height_denominator=16):
    """Extend the original cell construction without changing its formulas."""
    b = base()
    left, right = Fraction(left), Fraction(right)
    require(Fraction(375) <= left < right <= 400, "Cell outside [375,400]")
    require(isinstance(height_denominator, int) and height_denominator > 0,
            "Positive integer height denominator required")
    require(isinstance(sigma_denominator, int), "Integer sigma denominator required")
    la, lb = b["a"](left), b["a"](right)
    q = 1 + (lb / 4).exp() / 4
    logq = q.log()
    start_i = b["floor_cert"]((logq + (arb(15) / 4).log()) * height_denominator)
    start = arb(start_i) / height_denominator
    require(start > arb(3 * 10**12).log(), "CS source height not reached")
    require(b["kernel"](q, start) == 1, "Initial kernel must be exactly one")
    target = (arb(1800).log() + 3 * logq - la / 8 + 60) / 2
    end_i = max(b["ceil_cert"](target * height_denominator),
                b["ceil_cert"]((logq + (arb(25) / 2).log()) * height_denominator))
    end = arb(end_i) / height_denominator
    require(end >= logq + (arb(25) / 2).log(), "Tail outside cubic kernel piece")
    terms, bsum, esum = b["sigma_terms"](la, sigma_denominator)
    previous = b["kernel"](q, start)
    finite = arb(0)
    for i in range(start_i + 1, end_i + 1):
        u = arb(i) / height_denominator
        current = b["kernel"](q, u)
        mass = previous - current
        require(mass >= 0, "Kernel mass is not certainly nonnegative")
        finite += 2 * b["cumulative"](la, u, terms, bsum, esum) * mass
        previous = current
    tail = 1800 * q**3 * (-la / 8 - 2 * end).exp() * (end / 2 + arb(1) / 4)
    epsilon = 4 * (-la / 4).exp()
    logy = lb + (1 + epsilon).log()
    powers = (arb(15) / 8) * (1 + epsilon).sqrt() * logy**2 / (8 * arb(2).log()) * (-la / 4).exp()
    trivial = (-3 * la).exp() / (1 - (-2 * la).exp())
    delta = finite + tail + powers + trivial
    require(delta.is_finite(), "Nonfinite error enclosure")
    upper, approx = b["upper_decimal"](delta)
    return {
        "left": str(left), "right": str(right), "passed": bool(delta < 1),
        "sigma_denominator": sigma_denominator, "height_denominator": height_denominator,
        "delta_ball": delta.str(40), "delta_upper_rational": upper,
        "delta_upper_approx": approx,
        "finite_zero_ball": finite.str(35), "height_tail_ball": tail.str(35),
        "prime_power_ball": powers.str(35), "trivial_ball": trivial.str(35),
        "height_start": str(Fraction(start_i, height_denominator)),
        "height_end": str(Fraction(end_i, height_denominator)),
        "height_cells": end_i - start_i, "sigma_cells": len(terms),
    }


def verify_certificate(path=OUTPUT):
    path = Path(path)
    saved = json.loads(path.read_text(encoding="utf-8"))
    require(saved["schema"] == "legendre-k4-smooth-extension-v1", "Unknown schema")
    require(saved["status"] == "ALL_CELLS_PASSED" and saved["k"] == 4, "Saved scope")
    require(saved["dependencies_sha256"] == checked_dependencies(), "Saved dependencies")
    script_hash = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    require(saved["script_sha256"] == script_hash, "Extension script hash mismatch")
    require(saved["source_url"] == SOURCE, "Source version mismatch")
    require(saved["source_constants"] == [list(row) for row in base()["CS_ROWS"]], "Source constants mismatch")
    require(saved["kernel"] == {"M": 2, "R": ["1", "15/4", "24", "300"],
                                "max_over_mass": "15/8"}, "Kernel mismatch")
    start, finish = map(Fraction, saved["log_x_interval"])
    require(Fraction(375) <= start < finish == 400, "Wrong extension interval")
    cells = saved["cells"]
    require(cells and len(cells) == saved["number_of_cells"], "Cell count mismatch")
    require(Fraction(cells[0]["left"]) == start and Fraction(cells[-1]["right"]) == finish,
            "Coverage endpoint mismatch")
    for prior, following in zip(cells, cells[1:]):
        require(Fraction(prior["right"]) == Fraction(following["left"]), "Coverage gap or overlap")
    precision = saved["precision_bits"]
    require(isinstance(precision, int) and 100 <= precision <= 4096, "Invalid precision")
    old_precision = ctx.prec
    started = time.monotonic()
    try:
        ctx.prec = precision
        for cell in cells:
            replay = certify_cell(cell["left"], cell["right"], cell["sigma_denominator"], cell["height_denominator"])
            require(cell["passed"] is True and replay["passed"], "Cell fails replay")
            upper = Fraction(cell["delta_upper_rational"])
            require(0 < upper < 1, "Saved upper bound not below one")
            require(Fraction(replay["delta_upper_rational"]) <= upper, "Replay exceeds saved bound")
            for key in ("height_start", "height_end", "height_cells", "sigma_cells"):
                require(cell[key] == replay[key], f"Cell metadata mismatch: {key}")
        worst = max(cells, key=lambda cell: Fraction(cell["delta_upper_rational"]))
        require(saved["worst_cell"] == worst, "Worst-cell metadata mismatch")
    finally:
        ctx.prec = old_precision
    return {"status": "VERIFIED", "log_x_interval": saved["log_x_interval"],
            "number_of_cells": len(cells), "worst_upper_rational": worst["delta_upper_rational"],
            "script_sha256": script_hash,
            "certificate_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "elapsed_seconds": time.monotonic() - started}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--single", nargs=2, metavar=("LEFT", "RIGHT"))
    parser.add_argument("--start", default="375")
    parser.add_argument("--cell-width", help="Use a uniform width/grid instead of the balanced schedule")
    parser.add_argument("--sigma-denominator", type=int, default=4096)
    parser.add_argument("--height-denominator", type=int, default=16)
    parser.add_argument("--precision", type=int, default=160)
    parser.add_argument("--verify", nargs="?", const=str(OUTPUT), metavar="JSON")
    args = parser.parse_args()
    require(100 <= args.precision <= 4096, "Require precision between 100 and 4096 bits")
    if args.verify:
        require(not args.single, "--single incompatible with --verify")
        print(json.dumps(verify_certificate(args.verify), indent=2))
        return
    ctx.prec = args.precision
    started = time.monotonic()
    if args.single:
        print(json.dumps(certify_cell(*args.single, args.sigma_denominator, args.height_denominator), indent=2))
        print(f"Elapsed {time.monotonic()-started:.3f}s")
        return
    left = Fraction(args.start)
    start = left
    require(Fraction(375) <= left < 400, "Invalid target start")
    if args.cell_width is None:
        schedule = BALANCED_SCHEDULE
    else:
        require(Fraction(args.cell_width) > 0, "Invalid cell width")
        schedule = ((str(start), "400", args.cell_width,
                     args.sigma_denominator, args.height_denominator),)
    cells = []
    while left < 400:
        band = next(row for row in schedule if Fraction(row[0]) <= left < Fraction(row[1]))
        right = min(Fraction(band[1]), left + Fraction(band[2]))
        cell = certify_cell(left, right, band[3], band[4])
        print(f"[{left},{right}] upper={cell['delta_upper_approx']} passed={cell['passed']}", flush=True)
        require(cell["passed"], "Cell failed; no certificate written")
        cells.append(cell)
        left = right
    worst = max(cells, key=lambda cell: Fraction(cell["delta_upper_rational"]))
    result = {
        "schema": "legendre-k4-smooth-extension-v1", "status": "ALL_CELLS_PASSED", "k": 4,
        "log_x_interval": [str(start), "400"],
        "statement": f"Under QRH(7/8) and the listed inputs, every real x with {start}<=log(x)<=400 has a prime in (x,x+4*x^(3/4)).",
        "analytic_proof": "research/SMOOTH_EXTENSION.md and the fixed SMOOTH_CERTIFICATE.md dependency",
        "source_url": SOURCE, "source_constants": base()["CS_ROWS"],
        "kernel": {"M": 2, "R": ["1", "15/4", "24", "300"], "max_over_mass": "15/8"},
        "source_height_domain": "T>=3000000000000; checked before every kernel mass interval",
        "precision_bits": ctx.prec, "grid_schedule": schedule, "number_of_cells": len(cells),
        "cells": cells, "worst_cell": worst, "dependencies_sha256": checked_dependencies(),
        "script_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "python": platform.python_version(), "python_flint": flint.__version__,
        "created_at_Asia_Shanghai": datetime.now(timezone(timedelta(hours=8))).isoformat(),
        "elapsed_seconds": time.monotonic() - started,
        "scope": "Conditional finite real interval only; positive rectangular upper sums, not floating-point quadrature or Lean formalization.",
    }
    OUTPUT.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Wrote {OUTPUT}; {len(cells)} cells in {result['elapsed_seconds']:.3f}s")


if __name__ == "__main__":
    main()
