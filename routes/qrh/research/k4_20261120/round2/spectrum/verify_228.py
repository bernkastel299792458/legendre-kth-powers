"""Certify the improved right endpoint against the frozen spectrum calculation."""
from flint import arb, ctx

from verify_spectrum import A, check, flat_constants, verify
from pole_norm import sharp_right


def main():
    ctx.prec = 192
    anchor, width, height = "228", ".25", "55.98"
    shift, transition, cutoff = ".9", "10.7", "-4.85"
    step, tail, floor = 256, 192, "1.45"
    params = (anchor, width, step, tail, "flat-both", height,
              transition, cutoff, shift, floor)
    # The second expression sums exactly the original real-part nodes
    # through .850. Its extra base and non-moment costs are nonnegative.
    full = verify(*params, last_gap=".0069")
    prefix = verify(*params, theta=".851", last_gap=".0009")
    _, _, old, _ = flat_constants(height, shift, transition, cutoff,
                                  "flat-both", ctx.prec)
    ybar = A("1.01") * 2048 / 2047
    kappa = arb.pi() / (8 * ybar**2)
    U, delta, W, logh = map(A, (height, shift, transition, cutoff))
    new = sharp_right(U, delta, kappa, W, logh)
    ratio = new / old
    check(0 < ratio and ratio < 1, "right endpoint improvement")

    upper = A("7/8")
    shift_loss = 3 * delta * (2 * upper - 1) / ((2 - upper)**2 * U)
    def exponent_lower(s):
        return 1 - 3 * (1 - s) / (2 - s) - shift_loss

    check(exponent_lower(A(".65")) > 0, "all moment coefficients decrease")
    exponent = exponent_lower(A(".85"))
    check(exponent > 0, "gain for the upper nodes")
    factor = ratio**exponent

    # Bound all omitted rectangle edges. The jumps telescope, and the
    # terminal chord slope is at most L exp((7/8-1)L).
    L = A(anchor)
    d = (4 * (-L/4).exp()).log1p()
    u = (4/d).log()
    # The point masses have y <= tail. The continuous power tail has the
    # same boundary value and contributes an extra factor 2/(2-1/u).
    log_moment = u * (arb(tail)/4)**(1/u) * 2/(2-1/u)
    jlog = A("15/14").log()
    outer = (11*((logh+W)/2).exp()).log()
    edge = 162*(-logh).exp()/(2*arb.pi()) + 2*(2+(arb(2).log()+9*outer)/jlog)
    edge += 27*log_moment/jlog
    all_edges = 2 * L * ((upper-1)*L).exp() * edge

    result = factor*full + (1-factor)*(prefix+all_edges)
    print("old K3", old.str(16), "new K3", new.str(16))
    print("upper-node factor", factor.str(16), "edge cap", all_edges.str(12))
    print("new total bound", result.str(20))
    check(result < 1, "prime interval at and above L=228")


if __name__ == "__main__":
    main()
