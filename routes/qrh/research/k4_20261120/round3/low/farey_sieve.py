"""Published-input BT constants for long layers and their fourth-power endpoints."""

from pathlib import Path
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "round2" / "local"))
from check_edge import budget


def check_sieve(use_spacings):
    C = arb(4)/3
    eta = arb("1.090") if use_spacings else arb(".990")
    allowance = arb(".001")
    y0 = arb(50).exp()
    z0 = (y0/C).sqrt()
    error_constant = arb(61)/25
    c_lower = arb("1.33258")
    # Partial summation includes the endpoint error E(z)/2.
    twice_weight = 2*c_lower-(4*C).log()-4/z0-5*error_constant/z0.sqrt()
    if use_spacings:
        deficit = arb(".249")
        discrepancy = arb(30).sqrt()/(z0/16).sqrt()
        assert (1-2*discrepancy)**2/4 > deficit and discrepancy < arb(1)/2
        gain = arb(0)
        for i in range(8,128):
            a, b = arb(i)/128, arb(i+1)/128
            f = deficit*a**2/((1+a)*(1+a-deficit*a**2))
            mass = (b/a).log()-error_constant*((z0*a)**(-arb(1)/2)+(z0*b)**(-arb(1)/2))
            assert mass > 0
            gain += f*mass
        twice_weight += 2*gain
    assert twice_weight > eta+allowance
    # Move N <= y+2 to the real length y, including all primes <= z.
    log_cap = arb(50)+2
    rounding = 2*log_cap/y0 + log_cap**2/y0.sqrt()
    assert rounding < allowance and eta+allowance < 2
    print("sieve",eta.str(6),"constant before integer rounding",twice_weight.str(17))
    return eta


def check_layer(low, high, eta, extension):
    h = arb(3000175332800)
    K = h + extension
    low, high = arb(low), arb(high)
    a = K*(4*(-high/4).exp()).log1p()/2*(1-arb("1e-12"))
    assert 2*arb.pi()-2*a > 2 and 2*arb.pi() < 7
    # All tangent scales in check_edge.py are between 1/256 and 7.
    assert low >= 115 and high+(4*(-low/4).exp()).log1p()/2 < 116
    assert K <= h+300000 and 116+arb(7).log()+eta < 120
    assert 2*arb(115).exp()/(256*(h+300000)*120**2) > arb(50).exp()+1
    total, _ = budget(low,high,eta,extension)
    assert total < 1
    n = (high/4).exp().floor().unique_fmpz()
    assert 4*arb(n).log() < high and high < 4*arb(n+1).log()
    print("coverage",high.str(12),"K-H",extension,"budget",total.str(16),"n",n)


if __name__ == "__main__":
    ctx.prec = 192
    conservative = check_sieve(False)
    check_layer("115.00099","115.029",conservative,-1280000)
    check_layer("115.029","115.02925",conservative,-1280000)
    refined = check_sieve(True)
    check_layer("115.00099","115.03185",refined,-1280000)
    check_layer("115.03185","115.03210",refined,-1280000)
    check_layer("115.03210","115.032114",refined,-1280000)
    check_layer("115.032114","115.032116",refined,300000)
