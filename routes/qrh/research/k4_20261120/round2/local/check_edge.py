"""Finite-height signed test extending above the exact Platt–Trudgian height."""
from flint import arb, ctx


def budget(low, high, addition, extension):
    H, Q = arb(3000175332800), arb(10000)
    K = H + extension
    r, R = arb("0.000001"), arb("0.01")
    pi = arb.pi()
    d = (4*(-high/4).exp()).log1p()/2
    cmax = high + (4*(-low/4).exp()).log1p()/2
    a = K*d*(1-arb("1e-12"))
    assert 0 < a and a < pi and K*d > a and K*r > 2*pi
    mass = pi*a.sin()/a
    g0 = (1-a.cos())/a**2
    D = (low/2).exp()*mass/K

    def coefficients(scale, radius):
        """Multiply log lengths in u and the sums of attained levels."""
        v = low - K.log() + addition + scale.log()
        J = K.log() - addition - scale.log() + radius
        assert v > 4 and J > 2 and 2*(v-addition).exp()/v**2 > 10
        initial = 2*(low+radius)*(radius/2).exp()/(mass*v**2)
        return initial*radius.exp()*(v-1), initial*scale

    s = arb("1.55")
    slope, intercept = coefficients(s, r)
    # Upper bounds on the two sums of outward peaks, including both signs.
    last = 64
    parts = 32
    peaks = (1+a.cos())/(2*pi**2*last)
    for j in range(1, last+1):
        best = arb(0)
        for k in range(parts):
            u0 = 2*pi*j+a+(2*pi-2*a)*k/parts
            u1 = 2*pi*j+a+(2*pi-2*a)*(k+1)/parts
            numerator = (1+a.cos()).min(a.cos()-((u0+u1)/2).cos()+(u1-u0)/2)
            best = best.max(numerator/(u0**2-a**2))
        peaks += 2*best
    exterior = slope*(1-a/pi)*mass + intercept*peaks

    # First positive lobe on each side. For each range of heights use its own
    # tangent; the base slope already charged the area's exact total.
    previous = a.sin()/(2*a)
    slabs = 256
    for i in range(slabs):
        width0 = (2*pi-2*a)*i/slabs
        width1 = (2*pi-2*a)*(i+1)/slabs
        u1 = a + width1
        next_value = (a.cos()-u1.cos())/(u1**2-a**2) if i+1<slabs else arb(0)
        height = previous-next_value
        assert height > 0
        c1, c2 = coefficients((width0+width1)/2, r)
        # Upper bound in either sign for (c1-slope) times the level-set area.
        exterior += 2*height*(c2+((c1-slope)*width0).max((c1-slope)*width1))
        previous = next_value

    # Overcount r < |v| <= R separately, using the rational envelope in u.
    threshold = K*r
    j0 = int((threshold/(2*pi)).floor().unique_fmpz())-1
    assert j0 > 1
    c1, c2 = coefficients(arb(1), R)
    exterior += c1*4/(threshold*(1-(a/threshold)**2))
    exterior += c2*(1+a.cos())/(2*pi**2*(j0-1))

    # QRH and the local, frozen-endpoint Riemann–von Mangoldt count.
    S = arb(extension)
    if S >= 0:
        first = S + Q/pi.sqrt()
        second = S**2 + 2*Q**2
        third = S**3 + 6*S**2*Q/pi.sqrt() + 6*S*Q**2 + 8*Q**3/pi.sqrt()
        points = ((H/(2*pi)).log()/(2*pi) + arb(".15")/H)*second/2
        points += third/(12*pi*H) + (arb(".3")*H.log()+6)*first
        edge = pi/(mass*K)*(1/(16*Q**2)).exp()*((-low/8).exp()+(-7*low/8).exp())*points
    else:
        # Gaussian-tail estimate of lower/PROOF.md, independent of QRH.
        edge = 2*K/mass*(2*pi*g0)/(2*pi.sqrt()*Q)*(1/(16*Q**2)).exp()
        edge *= H**2*(1+4*Q**2/S**2)*(-(S/(2*Q))**2).exp()

    powers = g0*R.exp()*(cmax+R)**2/(2*arb(2).log()*D)
    far = 4*g0*(3*cmax/2+9/(8*Q**2)-(Q*R)**2/2).exp()/D
    pole = 16*pi.sqrt()*Q/(K*mass)
    small = 2*H*H.log()*pi/(a*K*D)
    arch = g0*(7+(1+K+2*Q/pi.sqrt()).log())/D
    return exterior + edge + powers + far + pole + small + arch, edge


if __name__ == "__main__":
    ctx.prec = 192
    rows = [
        ("114.992", "115.00099", "115.0009967", "0"),
        ("115.017", "115.02548", "115.0254897", ".8601"),
    ]
    for low, finite_end, qrh_end, eta in rows:
        for high, S in [(finite_end,-1280000),(qrh_end,300000),(qrh_end,0)]:
            total, edge = budget(arb(low), arb(high), arb(eta), S)
            if S == 0:
                assert total > 1
            else:
                assert total < 1
            n = int((arb(high)/4).exp().floor().unique_fmpz())
            assert 4*arb(n).log() < arb(high) and arb(high) < 4*arb(n+1).log()
            print(low, high, "BT addition", eta, "K-H", S, "total", total.str(18),
                  "edge", edge.str(12), "integer endpoint", n)
