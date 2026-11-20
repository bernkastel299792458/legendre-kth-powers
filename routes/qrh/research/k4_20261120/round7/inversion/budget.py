"""Finite-frequency transfer for the lcm phase and the exterior two-point test."""
from flint import arb, ctx


H = 3000175332800


def sieve_G(logz):
    # Ramaré, Theorem 3.1, all z>1. Theorem 1.3 gives c0=1.332582275733...
    assert logz > 0
    return logz+arb("1.332583")+arb("2.44")*(-arb(logz)/2).exp()


def area_floor(L, shift, logz):
    c, k, _, _, I = geometry(L, shift)
    d = c-arb(L)
    a = (1-arb("1e-12"))*k*d
    r = arb("1e-6")
    outside = (1-a/arb.pi()-2*(k*d-a)*(1-a.cos())/(a**2*I)
               -4/(I*k*r*(1-(a/(k*r))**2)))
    return (c-r)*(-r/2-(10000*r)**2).exp()*outside/sieve_G(logz)


def geometry(L, shift):
    ell = arb(L)
    k = arb(H + shift)
    d = (4 * (-ell / 4).exp()).log1p() / 2
    c = ell + d
    u = k * d
    a = (1 - arb("1e-12")) * u
    v = (u - a) / 2
    g = ((u + a) / 2).sin() * (v.sin() / v) / (u + a)
    h = g * (-(10000 * d)**2 - d / 2).exp() * (1 - d / c)
    area = arb.pi() * a.sin() / a
    return c, k, k * d.sinh(), h, area


def gram_floor(L, shift, logz, B):
    c, k, dhalf, h, area = geometry(L, shift)
    G = logz + 2 + arb("2.44") * (-arb(logz) / 2).exp()
    B = arb(B)
    denominator = B + abs((B * dhalf).sin()) / dhalf
    return c / G * 4 * arb.pi() * h / (area * denominator)


def forced_samples(L, shift, logz, steps, parts=1, sharpen=False):
    """Lower absolute Fourier sample mass above the reciprocal endpoint spacing."""
    c, k, dhalf, h, area = geometry(L, shift)
    d = c - arb(L)
    a = (1-arb("1e-12"))*k*d
    G = logz + 2 + arb("2.44")*(-arb(logz)/2).exp()
    if sharpen:
        G = G.min(sieve_G(logz))
    # The two exact endpoints have indices 0 and parts.
    left = k*(-d).expm1()
    total = 2*h
    spacing = 2*dhalf/parts
    for j in range(-steps*parts, (steps+1)*parts+1):
        if 0 <= j <= parts:
            continue
        x = left+j*spacing
        v = (x/k).log1p()
        u = k*v
        assert abs(u)>k*d
        value = (1+v/c)*(-v/2-(10000*v)**2).exp()*(a.cos()-u.cos())/(u**2-a**2)
        total += value.max(0)
    return (spacing*total-area*G/c)/2, 2*arb.pi()*k/(arb(H)*spacing)


def compact_tail(logz, A, T, m, eta=arb(1)/2, width=1):
    """Absolute error for every lcm times w(log q), using only D(it), |t|<=T."""
    Z = 2 * arb(logz)
    assert m >= 2 and A > 0 and T > 0 and 0 < eta < 1 and width > 0
    u0 = (A / (eta * T)).log()
    assert u0 + width < Z
    ratio = eta + arb(m) * (1 + 2 / arb(width)) / T
    return (Z + width - u0) * T * ratio**m * Z.exp() / (arb.pi() * (m - 1))


def gamma_tail(a, A, T, logz):
    """Universal remainder for the full (uncut) Mellin integral, all q <= z^2."""
    a, L = arb(a), arb(logz)
    assert arb(1)/2 < a < 1 and T >= 1 and L > 0 and A > 0
    # Sum tau_3(q) q^-a <= (z^2)^(1-a+1/log(z^2)) zeta(1+1/log(z^2))^3.
    mass = (2*L*(1-a)+1).exp() * (1+2*L)**3
    sigma = 2-a
    constant = ((2*arb.pi()).sqrt() * (1/(12*sigma)).exp()
                * (1+sigma**2)**((sigma-arb(1)/2)/2))
    return (constant * A**a * mass * (1+(-arb.pi()*T).exp())
            * T**(arb(1)/2-a) / (2*arb.pi()*(a-arb(1)/2)))


if __name__ == "__main__":
    ctx.prec = 192
    for shift in (0, 16000000000):
        for zlog, test, floor in ((58, "3.2260", "2.3370"), (60, "3.0867", "2.2616"),
                                  (65, "2.8500", "2.0928"), (70, "2.6861", "1.9475"),
                                  (116, "1.4294", "1.1883")):
            k = arb(H + shift)
            limit = arb(H) / k
            cost = gram_floor(116, shift, zlog, limit)
            # Quoted lower bandwidths are in physical frequency divided by H.
            stronger = gram_floor(116, shift, zlog, arb(test)*limit)
            assert cost > arb(floor) and stronger > 1
            print("shift", shift, "logz <=", zlog, "H-band cost >=", cost.str(13),
                  "required T/H >", test, flush=True)
            tail, start = forced_samples(116,shift,zlog,128)
            print("forced Fourier samples above",start.str(10),"H, mass >",tail.str(11))
    for zlog, parts in ((58, 134), (60, 23), (65, 7), (70, 4), (116, 1)):
        tail, start = forced_samples(116,0,zlog,200,parts)
        assert tail > 0
        print("refined lattice logz", zlog, "parts", parts, "frequency / H",
              start.str(12), "positive tail mass", tail.str(12))
    G58 = sieve_G(arb(58))
    print("sieve upper G(exp(58))",G58.str(13))
    for shift, C in ((0,2300000),(16000000000,1700000)):
        zlog = (arb(116)-arb(H+shift).log())/2+arb(C).log()
        charge = area_floor(116,shift,zlog)
        assert charge > 1
        print("sieve-level obstruction at shift", shift, "C", C, "cost", charge.str(13))
    assert area_floor(116,0,arb(58)) > arb("1.005136")
    tested = (arb(116)-arb(H).log())/2+arb(3000000).log()
    mass, begin = forced_samples(116,0,tested,500,210,True)
    assert mass > arb("0.00004379") and begin > arb("432.24")
    print("C=3000000 forced tail",mass.str(12),"first frequency / H",begin.str(12))
    c, k, _, _, _ = geometry(116, 0)
    M = c.exp()
    T = arb(H)/2
    A = 2 * arb.pi() * M
    y = M/k
    for zlog in (58, 70, 116):
        for n in (1, 128):
            error = compact_tail(zlog, n*A, T, 384, width=arb("0.1")) / y
            assert error < arb("3.211e-42")
            print("compact logz", zlog, "n", n, "absolute tail / y", error.str(10))
        print("full Gamma logz", zlog, "R(0.99,H/2) / y",
              (gamma_tail("0.99", A, T, zlog)/y).str(10))
