"""Long-interval sieve with the joint distribution of the two Farey neighbors."""
from pathlib import Path
import sys

from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/"round2"/"local"))
from check_edge import budget


def sieve():
    A = arb
    k, C, E = A("1.045"), A(4)/3, A("2.44")
    g = k**2
    z = k*(A(70).exp()/C).sqrt()
    baseline = 2*A("1.33258")-C.log()+2*k.log()-2*(1+g).log()
    baseline -= 4*g/z + 2*E*(1+2*g)/z.sqrt()
    area, variation, previous = A(0), A(0), A(0)
    mesh = 16384
    for i in range(mesh//256, mesh):
        a, b = A(i)/mesh, A(i+1)/mesh
        t, r = divmod(2*mesh,i)
        u, s = divmod(2*mesh,i+1)
        phase = A(0)
        if t == u:
            v, w = A(r)/i, A(s)/(i+1)
            phase = (v*(1-v)).min(w*(1-w))
        deficit = A(1)/4 + phase/2 - 2*A(30).sqrt()/(z*a).sqrt()
        assert 0 < deficit and deficit < 1
        improvement = g*deficit*a**2/((1+g*a)*(1+g*a-g*deficit*a**2))
        area += improvement*(b/a).log()
        variation += abs(improvement-previous)/a.sqrt()
        previous = improvement
    variation += previous
    constant = baseline+2*(area-E*variation/z.sqrt())
    eta = A("1.1328")
    assert constant > eta+A(".00004")
    y0 = A(70).exp()
    assert 2*(A(70)+2)/y0+(A(70)+2)**2/y0.sqrt() < A(".00004")
    assert k < C.sqrt() and eta+A(".00004") < 2
    print("additive constant before rounding", constant.str(18))
    return eta


def cover(eta):
    H = arb(3000175332800)
    # The smallest primary tangent scale equals (2*pi-2*a)/512.
    assert 2*arb(115).exp()/(256*(H+300000)*120**2) > arb(70).exp()+1
    cells = [("115.032114","115.03329",-1280000),
             ("115.03329","115.033338",-1280000),
             ("115.033338","115.033340",300000)]
    for lo, hi, extension in cells:
        l, h = arb(lo), arb(hi)
        K = H+extension
        a = K*(4*(-h/4).exp()).log1p()/2*(1-arb("1e-12"))
        assert 2 < 2*arb.pi()-2*a and 116+arb(7).log()+eta < 120
        assert 115 <= l and h+(4*(-l/4).exp()).log1p()/2 < 116
        total, edge = budget(l,h,eta,extension)
        assert total < 1
        n = (h/4).exp().floor().unique_fmpz()
        assert 4*arb(n).log() < h and h < 4*arb(n+1).log()
        print(lo, hi, extension, total.str(18), "last n", n)


if __name__ == "__main__":
    ctx.prec = 192
    cover(sieve())
