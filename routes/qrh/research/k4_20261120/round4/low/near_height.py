"""A compact-height sufficient alternative for the first fourth-power box."""
from pathlib import Path
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/"round2"/"local"))
from check_edge import budget


def verify():
    ctx.prec = 192
    A = arb
    H, Q = A(3000175332800), A(10000)
    eta, b = A("1.090"), A(".72")
    pi = arb.pi()
    rows = [("115.032114", 116, 220000), ("116", 117, 154000),
            ("117", 118, 123000), ("118", 119, 104000),
            ("119", 120, 92000), ("120", 121, 84000),
            ("121", 122, 79000), ("122", 123, 75000)]
    for low, high, allowed in rows:
        l, h = A(low), A(high)
        d = (4*(-h/4).exp()).log1p()/2
        K = A("1.55")*H if high == 116 else A("2.45")/d
        S, T = K-H, K+128*Q
        a = K*d*(1-A("1e-12"))
        I = pi*a.sin()/a
        assert H < K and T < 10*H and (2*pi-2*a)/512 > A(1)/512
        assert 2*l.exp()/(512*K*135**2) > A(50).exp()+1

        gross, edge = budget(l,h,eta,S)
        base = gross-edge
        cold = edge*((-b*l).exp()+(-(1-b)*l).exp())/((-l/8).exp()+(-7*l/8).exp())
        latitude = (-l/8).exp()*(1+(-(2*b-1)*l).exp())
        price = 2*pi/(I*K)*(1/(16*Q**2)).exp()*latitude*(S+Q/pi.sqrt())
        g0 = (1-a.cos())/a**2
        far = 2*K/I*(2*pi*g0)/(2*pi.sqrt()*Q)*(1/(16*Q**2)).exp()
        far *= T**2*(1+4/A(128)**2)*(-A(128)**2/4).exp()
        assert far < A("1e-1700")
        assert base+cold+price*allowed+far < 1
        allowance = (1-base-cold-far)/price
        top = int(T.upper().ceil().unique_fmpz())
        print(low, high, "ordinate ceiling", top, "non-high", base.str(9),
              "central strip", cold.str(9), "allowed mass", allowance.str(13))


if __name__ == "__main__":
    verify()
