"""Replay the round-two spectral certificate with the explicit RS fourth moment."""
import argparse
from unittest.mock import patch

from flint import arb, ctx

from rs_fourth import A, check, left_endpoint
import flat_window
from pole_norm import sharp_right
from verify_spectrum import verify


def boundary(U, delta, W, logh, *_):
    v, order = A("1.01"), 2048
    ybar = v*order/(order-1)
    T = U.exp()
    epsilon = A(".000001")
    check(T>10**10 and ((1+2/T)/v)**order<epsilon, "inner rational window")
    check(4*order/T<1 and 1/(1-(A(".5")+2/T)**order)<1+epsilon,
          "outer rational window")
    k3 = sharp_right(U,delta,arb.pi()/(8*ybar**2),W,logh)
    l0 = (1+epsilon)**2/(1-1/arb(3*10**12))
    return left_endpoint(U,W,logh), arb(0), k3, l0


if __name__ == "__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",default="223")
    cli.add_argument("--u0",default="54.73")
    args=cli.parse_args()
    ctx.prec=192
    # The spectral code imports this boundary function at its sole call site.
    # Supply both proved endpoint estimates and let the original code check
    # all hinge coefficients, the entire height integral and monotonicity.
    with patch.object(flat_window, "moments", boundary):
        budget=verify(args.anchor,".25",256,192,"flat-both",args.u0,"10.7",
                      "-4.85",".9","1.45","7/8",None,".0069")
    print("total",budget.str(18))
    check(budget<1,"point budget")
