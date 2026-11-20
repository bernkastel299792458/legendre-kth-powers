"""First finite rectangle, retaining the minimum ordinate in each height band."""

import contextlib
from fractions import Fraction
import io
from pathlib import Path
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "round2" / "spectrum"))
from finite_box import high_tail
from verify_spectrum import A, verify


def sinc_tail(x):
    if x < arb.pi():
        return (x.sin()/x).max(1/arb.pi())
    assert x >= arb.pi()
    return 1/x


def log_width(L):
    return (4*(-L/4).exp()).log1p()


def verify_first_box():
    ctx.prec = 160
    h = arb(3*10**12)
    end = arb(123)
    de = log_width(end)
    tail = high_tail("37", "123", "28.7", "9.5", "-4", ".75")
    cells = [(Fraction("114.992"), Fraction(115))]
    cells += [(Fraction(i,4), Fraction(i+1,4)) for i in range(460,492)]
    lower_heights = [h, arb(30).exp(), arb(31).exp(), arb(33).exp()]
    ranges = []
    for lo, hi in cells:
        l, r = A(lo), A(hi)
        with contextlib.redirect_stdout(io.StringIO()):
            restricted = verify(str(lo), "1/4", 128, 96, "flat-both", "28.7",
                                "8.5","-4.25",".88","0",".8",str(hi),".0149")
        high = tail*(A(".14")*(r-end)).exp()
        allowance = (1-restricted-high)*(l/8).exp()/2
        assert allowance > 0
        dl, dr = log_width(l), log_width(r)
        budgets = []
        for lower_height in lower_heights:
            cap = arb(1)
            for width in (arb(1)/4, arb(3)/4):
                x = width*lower_height*dr/2
                cap *= arb(1).min(sinc_tail(x)+width*dl/2)
            # Ratio to the first rectangle's original finite-height weight.
            ratio = cap.max((de/dr)**2)
            budgets.append(allowance/ratio)
        ranges.append(budgets)
    min_budgets = [min(row[i] for row in ranges) for i in range(len(lower_heights))]
    for i, bound in enumerate(min_budgets):
        worst = min(range(len(ranges)), key=lambda j: float(ranges[j][i]))
        print("band", i+1, "admissible", bound.str(17), "limiting cell", cells[worst])
    thresholds = (51326, 183930, 611919, 611919)
    assert all(value > threshold for row in ranges for value, threshold in zip(row, thresholds))
    return min_budgets


if __name__ == "__main__":
    verify_first_box()
