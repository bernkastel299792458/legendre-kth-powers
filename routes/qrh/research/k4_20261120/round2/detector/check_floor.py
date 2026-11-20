"""Disk Jensen lower bound for any multiplicatively normalized analytic detector."""
from pathlib import Path
import sys
from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "upper"))
from verify_far import A, check, constants, height_moment


def disk_floor(nu):
    integral = 2**(nu-2)*((nu-1)/2).gamma()/(arb.pi().sqrt()*(nu/2).gamma())
    return 2**nu*(nu-1)**(nu-1)/(2*integral*nu**nu)


def verify():
    U, delta, k1, k2, k3, l0 = constants()
    knots = [arb(i)/1000 for i in range(650, 871)] + [A("7/8")]
    ratio = (k1+k2/U**2)/k3
    floors = []
    for s in knots[:-1]:
        lo = (2+4*delta/U)/(2-s+3*delta/U)
        hi = 2/(2-s)
        values = []
        for j in range(16):
            a = lo+(hi-lo)*j/16
            b = lo+(hi-lo)*(j+1)/16
            values.append(disk_floor(a.union(b)).lower())
        floors.append(min(values))
    for L0 in (280, 290, 295, 298, 300):
        L = arb(L0)
        u = (A("16/7")*(1+(L/4).exp()/4)).log()
        prev = total = arb(0)
        for s,t,c in zip(knots,knots[1:],floors):
            slope = ((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
            jump = slope-prev
            check(jump>0, "positive chord difference")
            prev = slope
            p = 3*(1-s)/(2-s)
            k = 3*delta*(2*s-1)/(2-s)**2
            fixed = l0**(2/(2-s))*k3*ratio**p*(ratio**(k/U)).max(arb(1))
            fixed *= (k*(1+U.log()/U)).exp()*height_moment(u,p,1+p)
            total += jump*c*fixed/arb.pi()
        print("historical moment expression, lower bound",L0,total.str(12))
        check(total>1,"detector-only obstruction")
    for nu in ("1.45","1.65","1.71","16/9","2"):
        print("detector floor",nu,disk_floor(A(nu)).str(16))

if __name__ == "__main__":
    ctx.prec=192
    verify()
