#!/usr/bin/env python3
"""Generate/recheck the k=4 lower range, independently of legendre_k67.

Literature inputs: CHL arXiv:2103.05986v3, Theorem 1 / Table 2;
Sorenson--Webster arXiv:1509.00864v1, Theorem 1.1 (12-base MR cutoff).
Exact integer arithmetic certifies witnesses and overlap; Arb certifies exp.
This is a reproducible computation using published inputs, not a Lean proof.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import math
import platform
import time
from datetime import datetime, timedelta, timezone
from fractions import Fraction
from pathlib import Path

import flint
from flint import arb, ctx


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_CERTIFICATE = ROOT / "results" / "lower_range_certificate.json"
BASES = (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37)
TRIAL_PRIMES = BASES + (41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97)
MR_LIMIT = 318665857834031151167461  # strict; smallest 12-base SPSP
SMALL_X_LIMIT = 4 * 10**18
SMALL_N_MAX = 44721
L_END = Fraction(5473, 50)  # 109.46, exact and inward from CHL endpoint
ARB_PRECISION = 256
CHL_URL = "https://arxiv.org/html/2103.05986v3"
MR_URL = "https://arxiv.org/html/1509.00864v1"

# Transcribed from the full corrected Table 2, not its rounded summary Table 1.
# The first lower threshold is x0 itself; all other labels are log(x0).
CHL_TABLE = (
    ("4e18", "3.90970e7"),
    ("43", "4.18168e7"),
    ("46", "1.63940e8"),
    ("50", "1.06120e9"),
    ("55", "1.02884e10"),
    ("60", "7.69184e10"),
    ("75", "1.74043e11"),
    ("90", "1.84304e11"),
    ("105", "1.91886e11"),
    ("120", "1.97917e11"),
    ("135", "2.02553e11"),
    ("150", "2.07053e11"),
    ("300", "2.30126e11"),
    ("600", "2.51949e11"),
)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def exact_arb(q: Fraction) -> arb:
    return arb(q.numerator) / q.denominator


def integer_floor(value: arb) -> int:
    result = value.floor().unique_fmpz()
    require(result is not None, "Arb enclosure does not determine a unique floor")
    return int(result)


def is_prime_search(n: int) -> bool:
    """12-base MR with iterative squaring, valid only below the fixed cutoff."""
    require(0 <= n < MR_LIMIT, "Primality search outside the certified MR range")
    if n < 2:
        return False
    for p in TRIAL_PRIMES:
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in BASES:
        z = pow(a, d, n)
        if z == 1 or z == n - 1:
            continue
        for _ in range(s - 1):
            z = z * z % n
            if z == n - 1:
                break
        else:
            return False
    return True


def is_prime_verify(n: int) -> bool:
    """Separate checker: tests the defining congruences by direct modular pow.

    It shares the published bases/cutoff, but does not call the search test or
    use its iterative squaring code. It is not a second independent theorem.
    """
    require(isinstance(n, int) and not isinstance(n, bool), "Noninteger witness")
    require(0 <= n < MR_LIMIT, "Witness outside the certified MR range")
    if n <= 37:
        return n in BASES
    if n % 2 == 0:
        return False
    odd_part = n - 1
    exponents = []
    while odd_part % 2 == 0:
        odd_part //= 2
    exponent = odd_part
    while exponent < n - 1:
        exponents.append(exponent)
        exponent *= 2
    for base in BASES:
        if math.gcd(base, n) != 1:
            return False
        if pow(base, odd_part, n) == 1:
            continue
        if not any(pow(base, exponent, n) == n - 1 for exponent in exponents):
            return False
    return True


def regression_checks() -> None:
    """Check both implementations against a sieve and known difficult inputs."""
    stop = 10000
    sieve = bytearray(b"\x01") * (stop + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, math.isqrt(stop) + 1):
        if sieve[p]:
            sieve[p * p : stop + 1 : p] = b"\x00" * ((stop - p * p) // p + 1)
    for n in range(stop + 1):
        expected = bool(sieve[n])
        require(is_prime_search(n) == expected, f"Search MR/sieve disagreement: {n}")
        require(is_prime_verify(n) == expected, f"Verify MR/sieve disagreement: {n}")
    composites = (3215031751, 341550071728321, 3825123056546413051,
                  399165290221 * 399165290221)
    for n in composites:
        require(not is_prime_search(n) and not is_prime_verify(n),
                f"Known composite accepted: {n}")
    require(not is_prime_verify(MR_LIMIT - 1), "Even boundary case accepted")
    for checker in (is_prime_search, is_prime_verify):
        try:
            checker(MR_LIMIT)
        except ValueError:
            pass
        else:
            raise ValueError("MR strict upper cutoff was not enforced")


def compute_chl_rows() -> list[dict]:
    ctx.prec = ARB_PRECISION
    rows = []
    for label, delta_text in CHL_TABLE:
        delta = Fraction(delta_text)
        upper = 4 * (delta - 1)
        n_max = upper.numerator // upper.denominator
        if label == "4e18":
            root_floor = math.isqrt(math.isqrt(SMALL_X_LIMIT))
            n_min = root_floor + (root_floor**4 < SMALL_X_LIMIT)
            require((n_min - 1)**4 < SMALL_X_LIMIT <= n_min**4,
                    "First CHL threshold is not exactly bracketed")
        else:
            root = (arb(int(label)) / 4).exp()
            n_min = integer_floor(root) + 1
            require(arb(n_min - 1) < root < arb(n_min),
                    f"Threshold not strictly bracketed for log x0={label}")
            # Recheck with logs to avoid relying only on the inverse exp check.
            require(4 * arb(n_min - 1).log() < arb(int(label)),
                    "Predecessor is not below the lower threshold")
            require(4 * arb(n_min).log() > arb(int(label)),
                    "First integer is not above the lower threshold")
        require(Fraction(n_max) <= upper < Fraction(n_max + 1),
                "Upper integer endpoint is incorrect")
        rows.append({
            "x0_label": label,
            "delta_printed": delta_text,
            "delta_numerator": delta.numerator,
            "delta_denominator": delta.denominator,
            "n_min": n_min,
            "n_max": n_max,
            "nonempty": n_min <= n_max,
        })
    return rows


def coverage_from_rows(rows: list[dict]) -> dict:
    covered = SMALL_N_MAX
    chain = []
    for row in rows:
        if not row["nonempty"]:
            continue
        require(row["n_min"] <= covered + 1,
                f"Gap before CHL row {row['x0_label']}")
        old = covered
        covered = max(covered, row["n_max"])
        chain.append({"x0_label": row["x0_label"], "previous_end": old,
                      "next_start": row["n_min"], "new_end": covered,
                      "overlap_or_adjacency": True})
    root_end = (exact_arb(L_END) / 4).exp()
    target_n_max = integer_floor(root_end)
    require(root_end < arb(covered), "Requested rational L endpoint not covered")
    require(target_n_max <= covered, "Target integer endpoint not covered")
    return {
        "n_min": 1,
        "n_max_inclusive": covered,
        "target_L_numerator": L_END.numerator,
        "target_L_denominator": L_END.denominator,
        "target_n_max_inclusive": target_n_max,
        "all_n_with_4_log_n_le_target_L_covered": True,
        "target_exp_quarter_enclosure": str(root_end),
        "actual_endpoint_4_log_nmax_enclosure": str(4 * arb(covered).log()),
        "chain": chain,
    }


def witness_digest(witnesses: list[int]) -> str:
    encoded = json.dumps(witnesses, separators=(",", ":")).encode("ascii")
    return hashlib.sha256(encoded).hexdigest()


def find_small_witnesses() -> list[int]:
    witnesses = []
    for n in range(1, SMALL_N_MAX + 1):
        left, right = n**4, n**4 + 4 * n**3
        candidate = 2 if n == 1 else left + 1 + (left % 2)
        while candidate < right and not is_prime_search(candidate):
            candidate += 1 if candidate == 2 else 2
        require(left < candidate < right, f"No short-interval witness found for n={n}")
        witnesses.append(candidate)
    return witnesses


def build_certificate(path: Path) -> dict:
    require(SMALL_N_MAX**4 < SMALL_X_LIMIT <= (SMALL_N_MAX + 1)**4,
            "Small-range endpoint is wrong")
    regression_checks()
    witnesses = find_small_witnesses()
    rows = compute_chl_rows()
    certificate = {
        "schema": "legendre-k4-lower-range-v1",
        "created_at_Asia_Shanghai": datetime.now(timezone(timedelta(hours=8))).isoformat(),
        "status": "computed; recheck with --verify; literature inputs explicit",
        "dependencies": {
            "CHL": {"url": CHL_URL, "version": "arXiv:2103.05986v3",
                    "location": "Theorem 1 and corrected Table 2",
                    "role": "accepted literature input; upstream analytic proof not rechecked here"},
            "Miller_Rabin": {"url": MR_URL, "doi": "https://doi.org/10.1090/mcom/3134",
                             "location": "Sorenson--Webster, Theorem 1.1",
                             "bases": list(BASES), "strict_upper_limit": MR_LIMIT,
                             "role": "accepted exhaustive-computation theorem; no RH assumption"},
            "QRH_required_for_this_lower_range": False,
        },
        "runtime": {"python": platform.python_version(), "python_flint": flint.__version__,
                    "arb_precision_bits": ARB_PRECISION},
        "small_range": {"n_min": 1, "n_max": SMALL_N_MAX,
                        "x_limit": SMALL_X_LIMIT,
                        "witnesses_indexed_by_n_minus_one": witnesses,
                        "witness_sha256": witness_digest(witnesses),
                        "max_witness": max(witnesses),
                        "max_p_minus_n4": max(p - n**4 for n, p in enumerate(witnesses, 1)),
                        "witness_condition": "n^4 < p < n^4+4*n^3 < (n+1)^4"},
        "CHL_rows": rows,
        "coverage": coverage_from_rows(rows),
        "not_claimed": ["all n for k=4", "independent verification of CHL upstream inputs",
                        "Lean/kernel formal verification", "per-prime Pocklington certificates"],
    }
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(certificate, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    return certificate


def verify_certificate(path: Path) -> dict:
    """Read-only verification; recompute every semantic assertion from inputs."""
    ctx.prec = ARB_PRECISION
    data = json.loads(path.read_text(encoding="utf-8"))
    require(data["schema"] == "legendre-k4-lower-range-v1", "Unknown schema")
    dep = data["dependencies"]
    require(dep["CHL"]["url"] == CHL_URL, "CHL source changed")
    require(dep["Miller_Rabin"]["url"] == MR_URL, "MR source changed")
    require(dep["Miller_Rabin"]["bases"] == list(BASES), "MR bases changed")
    require(dep["Miller_Rabin"]["strict_upper_limit"] == MR_LIMIT, "MR cutoff changed")
    require(dep["QRH_required_for_this_lower_range"] is False, "Unexpected QRH dependency")
    regression_checks()
    small = data["small_range"]
    require(small["n_min"] == 1 and small["n_max"] == SMALL_N_MAX, "Wrong finite range")
    require(small["x_limit"] == SMALL_X_LIMIT, "Wrong finite x threshold")
    require(SMALL_N_MAX**4 < SMALL_X_LIMIT <= (SMALL_N_MAX + 1)**4,
            "Finite and CHL ranges do not meet")
    witnesses = small["witnesses_indexed_by_n_minus_one"]
    require(len(witnesses) == SMALL_N_MAX, "Missing or extra witnesses")
    require(witness_digest(witnesses) == small["witness_sha256"], "Witness digest mismatch")
    for n, p in enumerate(witnesses, 1):
        require(n**4 < p < n**4 + 4 * n**3 < (n + 1)**4,
                f"Witness outside the open short interval, n={n}")
        require(p < 2**64 and p < MR_LIMIT, f"Witness exceeds finite-base bound, n={n}")
        require(is_prime_verify(p), f"Independent MR verifier rejects n={n}, p={p}")
    require(max(witnesses) == small["max_witness"], "Maximum witness mismatch")
    require(max(p - n**4 for n, p in enumerate(witnesses, 1)) == small["max_p_minus_n4"],
            "Maximum offset mismatch")
    rows = compute_chl_rows()
    require(data["CHL_rows"] == rows, "CHL rows/derived endpoints differ")
    expected_coverage = coverage_from_rows(rows)
    # Numeric enclosure strings are explanatory; the inequalities are recomputed.
    for key, value in expected_coverage.items():
        if not key.endswith("_enclosure"):
            require(data["coverage"][key] == value, f"Coverage mismatch: {key}")
    return {"verified": True, "small_witnesses_verified": len(witnesses),
            "effective_CHL_rows": sum(row["nonempty"] for row in rows),
            "n_max_inclusive": expected_coverage["n_max_inclusive"],
            "target_L": str(L_END),
            "target_n_max_inclusive": expected_coverage["target_n_max_inclusive"],
            "max_witness": max(witnesses),
            "max_p_minus_n4": small["max_p_minus_n4"],
            "witness_sha256": small["witness_sha256"],
            "scope": "finite lower range only, conditional on cited literature inputs"}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build", action="store_true", help="Generate the certificate, then verify it")
    parser.add_argument("--verify", action="store_true", help="Read-only verification of the saved certificate")
    parser.add_argument("--certificate", type=Path, default=DEFAULT_CERTIFICATE)
    args = parser.parse_args()
    require(args.build != args.verify, "Choose exactly one of --build and --verify")
    started = time.perf_counter()
    if args.build:
        build_certificate(args.certificate)
    summary = verify_certificate(args.certificate)
    summary["elapsed_seconds"] = round(time.perf_counter() - started, 3)
    print(json.dumps(summary, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    main()
