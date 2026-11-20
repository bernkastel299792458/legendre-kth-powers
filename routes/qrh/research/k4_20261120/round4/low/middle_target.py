"""Uniform right-boundary targets for two fourth-power detectors at L=160."""
import argparse
from pathlib import Path
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/"euler"))
import verify_euler as euler


def verify(modulus=6):
    ctx.prec = 192
    parameters = (".9", "9.6", "-2.8") if modulus==6 else (".92", "9.5", "-3.5")
    options = {} if modulus==6 else dict(fold="density", direct=True, mellin=True)
    fixed, left, right, terms = euler.verify(
        "160", modulus, modulus, *parameters, split_left=True, breakdown=True, **options
    )
    assert 0<fixed and fixed<1

    def budget(scale):
        return fixed+sum(value*scale**exponent for value,exponent in terms)

    lo, hi = arb(0), arb(1)
    assert budget(hi)>1
    for _ in range(40):
        mid = (lo+hi)/2
        value = budget(mid)
        if value<1:
            lo = mid
        else:
            assert value>1
            hi = mid
    assert budget(lo)<1 and budget(hi)>1
    print("modulus", modulus, "K1", left.str(16), "K3", right.str(16),
          "fixed", fixed.str(14), "total", budget(arb(1)).str(16))
    if modulus==6:
        delta, transition, cutoff = map(euler.A, parameters)
        direct = euler.boundary(euler.A("38.98"),delta,transition,cutoff,6,6,True,direct=True)[1]
        print("direct high norm K3", direct.str(16), "total", budget(direct/right).str(16))
    print("root bracket multiplier", lo.str(16), hi.str(16),
          "absolute", (right*lo).str(16), (right*hi).str(16))
    candidates = ("0.00270","0.00275") if modulus==6 else ("0.00255","0.00257")
    for candidate in candidates:
        print("test K3", candidate, "budget", budget(euler.A(candidate)/right).str(17))


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--modulus", type=int, choices=(6,210), default=6)
    verify(cli.parse_args().modulus)
