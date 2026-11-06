"""Emit integer witnesses for the M3 far pilot; Lean verifies their arithmetic.

This generator reuses the current enclosure proposals, including both height
paddings. Its output does not assert the soundness of Arb. The separate Lean
factor proofs verify those proposals against their actual real definitions.
"""
from __future__ import annotations

import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from generate_m3_far import ctx, sigma_data, height_data

ROOT = Path(__file__).resolve().parents[1]
BITS = 48
SCALE = 1 << BITS


def integer_pair(values):
    result = tuple(int(v * SCALE) for v in values[:2])
    assert all(v >= 0 for v in result)
    assert all(Fraction(v, SCALE) == q for v, q in zip(result, values[:2]))
    return result


def emit_rows(name, rows):
    body = ',\n'.join(f'  ({c}, {a})' for c, a in rows)
    return f'def {name} : List (ℕ × ℕ) := [\n{body}\n]\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true',
        help='Regenerate in memory and compare bytes without writing any output.')
    args = parser.parse_args()
    ctx.prec = 256
    sigma = [integer_pair(sigma_data(j)) for j in range(384)]
    height = [integer_pair(height_data(i)) for i in range(125)]
    text = '''import LegendreK6.LowRankInteger

/-! Proposed dyadic witnesses for the complete M3 far pilot. The integer rows
are data, not analytic assumptions. Separate factor theorems prove each
real enclosure; the integer certificate proves the resulting exact budget. -/

namespace LegendreK6.M3Far

set_option maxRecDepth 100000
set_option maxHeartbeats 0

'''
    text += emit_rows('sigmaRows', sigma) + '\n' + emit_rows('heightRows', height)
    text += '''
theorem sigmaRows_length : sigmaRows.length = 384 := rfl
theorem heightRows_length : heightRows.length = 125 := rfl

def sigmaRowIndex (j : Fin 384) : Fin sigmaRows.length :=
  ⟨j.val, by simpa only [sigmaRows_length] using j.isLt⟩

def heightRowIndex (i : Fin 125) : Fin heightRows.length :=
  ⟨i.val, by simpa only [heightRows_length] using i.isLt⟩

noncomputable def sigmaDyadicFactor (j : Fin 384) : ℝ :=
  dyadicCoefficient 48 sigmaRows (sigmaRowIndex j)

noncomputable def sigmaDyadicPower (j : Fin 384) : ℝ :=
  dyadicPower 48 sigmaRows (sigmaRowIndex j)

noncomputable def heightDyadicFactor (i : Fin 125) : ℝ :=
  dyadicCoefficient 48 heightRows (heightRowIndex i)

noncomputable def heightDyadicPower (i : Fin 125) : ℝ :=
  dyadicPower 48 heightRows (heightRowIndex i)

end LegendreK6.M3Far
'''
    output = ROOT / 'lean/LegendreK6/M3FarIntegerData.lean'
    proposed_bytes = text.encode('utf-8')
    if args.check:
        matches = output.is_file() and output.read_bytes() == proposed_bytes
        status = 'CHECK_PASS' if matches else 'CHECK_FAIL'
    else:
        output.write_bytes(proposed_bytes)
        status = 'GENERATED_UNCHECKED'
    moments_s = [sum(c*a**n for c, a in sigma) for n in range(22)]
    moments_h = [sum(c*a**n for c, a in height) for n in range(22)]
    import math
    terms = [Fraction(moments_s[n]*moments_h[n], SCALE**(2*(n+1))*math.factorial(n))
             for n in range(22)]
    value = sum(terms[:21]) + 2*terms[21]
    print(json.dumps(dict(status=status, read_only=args.check, bits=BITS,
        sigma_rows=len(sigma), height_rows=len(height),
        height_factor_padding=1048576, height_power_padding=1,
        exploratory_low_rank=float(value), proposed_cap='9/20',
        exploratory_cap_holds=value <= Fraction(9,20),
        bytes=len(proposed_bytes),
        sha256=hashlib.sha256(proposed_bytes).hexdigest()), indent=2))
    if args.check and not matches:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
