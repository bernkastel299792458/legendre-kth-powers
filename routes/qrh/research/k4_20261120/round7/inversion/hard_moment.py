"""Complete |D(it)| at a hard Selberg cutoff, uniformly in the twist interval."""
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb, fmpz, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "mobius"))
from poisson_power import estimate, H
from selberg_band import low_line


@lru_cache(None)
def factors(i, precision, small_twist):
    assert precision == ctx.prec
    s = arb(i)/100
    P = 2000
    ns = n1 = raw_s = raw_1 = arb(1)
    prime_tails = {r: (arb(r)/100).zeta().log() for r in (100+i, 2*i, 200)}
    for n in range(2, P+1):
        if not fmpz(n).is_prime():
            continue
        p = arb(n)
        inv = p**(-s)
        twist = arb(2)
        if small_twist is not None:
            angle = (arb(small_twist)*p.log()).min(arb.pi())
            twist = 2*(angle/2).sin()
        correction = 1 + twist*inv/((p-1)*(1-inv))
        factor = twist*(p/(p-1))**2
        ns *= correction**2 + factor*(inv/(1-inv))**2
        n1 *= correction**2 + factor/(p*(1-inv))**2
        raw_s *= 1 + factor*inv**2
        raw_1 *= 1 + factor/p**2
        for r in prime_tails:
            prime_tails[r] += (-p**(-arb(r)/100)).log1p()
    p = arb(P)
    rho = 1/(1-1/p)
    inv = 1/(1-p**(-s))
    correction = 2*rho*inv*prime_tails[100+i]
    def tail(exponent):
        return rho**2*prime_tails[exponent]
    ns = ns.sqrt()*(correction+inv**2*tail(2*i)).exp()
    n1 = n1.sqrt()*(correction+inv**2*tail(200)).exp()
    return ns, n1, raw_s.sqrt()*tail(2*i).exp(), raw_1.sqrt()*tail(200).exp()


def max_coefficient(log_x):
    primorial = 1
    out = arb(1)
    X = log_x.exp()
    for n in range(2, 10000):
        if fmpz(n).is_prime():
            primorial *= n
            if primorial > X:
                return out
            assert primorial < X
            out *= arb(n+1)/(n-1)
    raise ValueError("primorial bound exhausted")


def complete(logz, T, V, i=62, k=245, m=20, order=32, hV=8):
    """First result is |D(it)| / z^2 for every |t|<=T."""
    L = arb(logz)
    T, V = arb(T), arb(V)
    assert L >= 58 and T >= 0 and V > 100 and T+V < H//2
    s, u = arb(i)/100, 1+1/L
    assert arb(1)/2 < s < 1 < u < 1+arb(k)/100
    tiny = int(T.ceil().unique_fmpz()) if T < 3 else None
    ns, n1, raw_s, raw_1 = factors(i, ctx.prec, tiny)
    rightmost = 1+arb(k)/100
    low = low_line(i,ctx.prec).max(rightmost.zeta()/(2*rightmost).zeta())
    def reciprocal(v):
        return estimate(s, (T+v).max(100), k, m).max(low)
    inverse = reciprocal(V)
    h = arb(hV)/V
    ratio = (1+(h*u).exp())/(h*V)
    hs = order*h
    assert ratio < 1
    b = (1+(h*u).exp())/h
    endpoint = b.min(V)
    cuts = [arb(0)]
    v = arb(1)
    while v < endpoint:
        cuts.append(v)
        v *= 10
    cuts.append(endpoint)
    vertical = sum(reciprocal(r)*((r/s).asinh()-(l/s).asinh())
                   for l,r in zip(cuts,cuts[1:]))
    vertical = ((hs*u).exp()*vertical+inverse/order)/arb.pi()
    discrete = max_coefficient(L+hs)
    endpoints = inverse*(u-s)/(arb.pi()*V) + u.zeta()/(arb.pi()*order)
    G = L+arb("1.331")
    first = (vertical*ns+discrete*raw_s)*((s-1)*L).exp()/G
    second = (arb(1).exp()*ratio**order*endpoints*n1
              + discrete*hs.expm1()*raw_1)/G
    return (first+second)**2, first, second


if __name__ == "__main__":
    ctx.prec = 160
    ctx.cap = 32
    limits = {58: ("2.272e-11", "2.566e-10", "7.695e-10", "3.446e-9"),
              65: ("9.073e-14", "1.014e-12", "3.028e-12", "1.353e-11"),
              70: ("1.982e-15", "2.071e-14", "6.048e-14", "2.656e-13")}
    for logz, ceilings in limits.items():
        for tlog, ceiling in zip((0, 12, 20, 26), ceilings, strict=True):
            result = complete(logz, arb(tlog).exp(), arb(25).exp())
            assert result[0] < arb(ceiling)
            print("hard D/z^2, logz", logz, "log T", tlog,
                  *(v.str(11) for v in result), flush=True)
    from budget import compact_tail, geometry
    c, k, _, _, _ = geometry(116,0)
    M = c.exp()
    y = M/k
    T = arb(1400000000000)
    A = 2*arb.pi()*M
    for L in (58, 70):
        squared = complete(L,T,arb(25).exp())[0]
        order = 384
        h = arb("0.1")
        eta = arb(1)/2
        U = (A/(eta*T)).log()
        absolute_mass = ((2*L+h-U)*(4*order/h+(eta*T)**2/2)).root(4)
        bulk = absolute_mass*squared*arb(2*L).exp()/y
        truncation = compact_tail(L,A,T,order,eta,h)/y
        print("joint n=1 logz", L, "|D|/z^2", squared.str(11),
              "large lcm charge / y", (bulk+truncation).str(11),
              "Fourier remainder / y", truncation.str(9), flush=True)
