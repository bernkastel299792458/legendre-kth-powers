"""Transfer an independently certified finite high-zero charge to a new closed L interval."""
import argparse
from fractions import Fraction
from flint import arb, ctx
from low_replay import A, H, budget, refine


def transfer(lo, hi, old_lo, old_hi, size, high):
    assert Fraction(old_lo) <= Fraction(lo) < Fraction(hi)
    k = arb(H + size)
    q = arb(10000)

    def bandwidth(endpoint):
        return (1-A("1e-12"))*k*(4*(-A(endpoint)/4).exp()).log1p()/2

    new = bandwidth(hi)
    old = bandwidth(old_hi)
    assert arb.pi()/2 < new < arb.pi() and arb.pi()/2 < old < arb.pi()
    finite_charge = A(high)
    if Fraction(hi) < Fraction(old_hi):
        finite_charge *= new/old*old.sin()/new.sin()
    remote = (2*k/(arb.pi()*new.sin()/new)*arb.pi()*(1-new.cos())/new**2 /
              (arb.pi().sqrt()*q)*(1/(16*q**2)).exp()*(k+128*q)**2 *
              (1+A(4)/128**2)*(-A(128)**2/4).exp())
    assert remote < A("1e-1700")
    arith = refine(lo, hi, size, addition="1.16613")[0] - budget(A(lo), A(hi), A("1.16613"), size)[1]
    return arith + finite_charge + remote


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--lo", default="115.038000")
    parser.add_argument("--hi", default="115.040500")
    parser.add_argument("--reference-lo", default="115.038000")
    parser.add_argument("--reference-hi", default="115.040000")
    parser.add_argument("--size", type=int, default=14000000000)
    parser.add_argument("--high", default=".005055995921")
    parser.add_argument("--check", action="store_true")
    a = parser.parse_args()
    ctx.prec = 192
    total = transfer(a.lo, a.hi, a.reference_lo, a.reference_hi, a.size, a.high)
    print(a.lo, a.hi, "total", total.str(18), flush=True)
    if a.check:
        assert total < 1
