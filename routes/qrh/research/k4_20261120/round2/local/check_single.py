"""Scalars for the one-gap spectral obstruction in SINGLE_GAP.md."""
from flint import arb, ctx
from check_exceptional import bounds


def main():
    ctx.prec = 192
    H, W, count = arb(3000175332800), arb(10**8), arb(5 * 10**6)
    b = arb(8748) / 10000
    lam = arb(138)
    background_k5 = 32 * (-3 * lam / 10).exp() * (lam / 5 + arb(8).log() + 1)
    right_k5 = 2 * count * ((b - 1) * lam).exp()
    assert background_k5 + right_k5 < arb(32) / 100
    cs_floor = arb(5069) / 1000 * ((H.log() + 7 * H.log().log()) / 3).exp()
    assert cs_floor > count
    assert (arb(2)*arb.pi()/116) < arb(3)/50
    print("K5 model upper", (right_k5 + background_k5).str(16))
    for L in [arb(116), arb(120)]:
        n = int((L / 4).exp().ceil().unique_fmpz())
        half = 2 * (arb(1) / n).log1p()
        center = 4 * arb(n).log() + half
        z = (H + W) * half / 2
        assert H * half < arb.pi() / 2 and z < 1 and center > 116
        bmin = (1 - z**2 / 6)**2
        amp = 2 * count * ((b - 1) * center).exp() * bmin
        eps = half.expm1() + half.exp() * (W * half + half.expm1() / bmin)
        tmax = 2000 / half
        background = 4 * (half - (center - half) / 2).exp() * tmax * (tmax.log() + 1)
        rms = amp * (1 / arb(2).sqrt() - eps) - background
        assert rms > 2
        M = ((L + 1) / 4).exp()
        u = (H + W) / (2 * M)
        tent_min = (1 - u**2 / 6)**2 - (1 / M).expm1()
        assert u < 1 and tent_min > 0
        diagonal = ((arb(1)/4 - 2*(1-b))*L + arb(1)/4).exp()
        diagonal *= tent_min**2 * (1 - (-2*(1-b)).exp()) / (2*(1-b))
        assert diagonal > arb("1.02")
        # Uniform model obstruction for the broader signed spectral kernel.
        Q = arb(10000)
        amin, amax = arb("1.85"), arb("2.5")
        w = (H+W)*half
        assert w < amin and w < arb.pi() and amin.sin() > amax.sin()
        ratio = arb(1).min((amin-w).sin()/amin.sin())
        eg = (1/(16*Q**2)).exp()
        error = 2*amax*Q/(H*arb.pi().sqrt()) + eg-1 + eg/(2*Q*arb.pi().sqrt())
        wide = 2*count*((b-1)*center).exp()*(ratio-error/amax.sin())
        assert wide > arb("1.60") if L == 116 else wide > arb("2.94")
        cs, k5 = bounds(L, L)
        factor = M * (1 - (-arb(1)/4).exp()) - 2
        assert cs*factor > 10**11 and k5*factor > 10**10
        print("L", L, "n", n, "single-gap scale", (2/M).str(12),
              "CS ratio", (cs*factor).str(12), "K5 ratio", (k5*factor).str(12),
              "full-model mean-square lower", (rms**2).str(12),
              "one conjugate pair diagonal ratio", diagonal.str(12),
              "broad signed-kernel model sum", wide.str(12))


if __name__ == "__main__":
    main()
