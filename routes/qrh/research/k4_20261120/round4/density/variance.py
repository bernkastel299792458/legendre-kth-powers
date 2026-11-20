"""A positive subtraction from the *undiscounted* high Selberg norm.

If V=log T>=U, e=2*delta/V, h=exp(logh), Y=hT and v=2+e, then
T times the Jensen variance saving for the Q-sieved norm is at least
Y**(-e)*high_saving(U,delta,W,logh,q). Subtract the result from
signed_high_norm before the multiplication by discount*zeta(2+lower)/zeta(2).
"""
from bisect import bisect_left
from flint import arb, ctx


def smooth_values(q, cap):
    values = [1]
    primes = []
    for p in range(2,q+1):
        if q%p:
            continue
        primes.append(p)
        q //= p
        powers = []
        r = p
        while r<=cap:
            powers.extend(r*n for n in values if r*n<=cap)
            r *= p
        values += powers
    if q!=1:
        raise ValueError("a squarefree modulus is required")
    return sorted(values),primes


def high_saving(U,delta,W,logh,q,cap=96):
    """The variance in the normalized 2+e norm, uniform for T>=exp(U)."""
    e0 = 2*delta/U
    y0 = (U+logh).exp()
    if not (U>0 and delta>0 and 0<e0 and e0<=arb("0.1") and W>0 and logh<0):
        raise ValueError("unsupported parameters")
    smooth,primes = smooth_values(q,cap)
    density = arb(1)
    zq = (2+e0).zeta()
    for p in primes:
        density *= 1-arb(1)/p
        zq *= 1-arb(p)**(-2-e0)
    dv = 6/arb.pi()**2
    # Geometric grid in jk/Y. Each variable occurs in positive terms only.
    count = 64
    step = arb(1)/16
    grid = [(i*step,(i+1)*step) for i in range(count)]
    rows = [(b, density*(b.exp()-a.exp()), (-(2+e0)*b).exp(), (b-W).exp())
            for a,b in grid]
    total = arb(0)
    for i,k in enumerate(smooth):
        gap = arb(2**len(primes)*k)/y0
        for l in smooth[i+1:]:
            ratio = arb(l)/k
            log_ratio = ratio.log()
            main = dv*log_ratio
            coefficient = 1/(k*arb(l)**(2+e0))
            for b,mass,decay,tail in rows:
                if not b+log_ratio<=W:
                    continue
                difference = (main-arb("1.2")*(1+ratio)*tail).max(arb(0))
                total += coefficient*(mass-gap).max(arb(0))*decay*difference**2
    return zq*total/((logh).exp()*W**2)


def low_saving(U,delta,W,logh,q,cap=512):
    """Uniform coefficient subtractable from the *undiscounted* low norm S(1+e)/V."""
    smooth,primes = smooth_values(q,cap)
    density = arb(1)
    for p in primes:
        density *= 1-arb(1)/p
    e0 = 2*delta/U
    x0 = (U+logh+W).exp()
    if not (U>0 and delta>0 and 0<e0 and e0<=arb("0.1") and W>0 and logh<0):
        raise ValueError("unsupported parameters")
    mu = [1]*(cap+1)
    prime = [True]*(cap+1)
    for p in range(2,cap+1):
        if not prime[p]:
            continue
        for n in range(p,cap+1,p):
            mu[n] *= -1
            if n>p:
                prime[n] = False
        for n in range(p*p,cap+1,p*p):
            mu[n] = 0
    slope, offset = arb(0),arb(0)
    for n in range(1,cap+1):
        t = arb(n).log()
        if n>=2 and not slope*t-offset>arb(".65"):
            raise ArithmeticError("finite G_0 lower bound through cap")
        slope += arb(mu[n])/n
        offset += (arb(mu[n])/n)*t
    grid = [arb(i)/16 for i in range(cap.bit_length()*16+1)
            if arb(i)/16<=W and arb(i)/16<=arb(cap).log()]
    logs = [float(x) for x in grid]
    total = arb(0)
    for i,k in enumerate(smooth):
        gap = arb(2**len(primes)*k)/x0
        prefix=[arb(0)]
        for a,b in zip(grid,grid[1:]):
            mass=(density*((-a).exp()-(-b).exp())-gap).max(arb(0))
            level=a.min(arb(".65"))*(-e0*b).exp()
            prefix.append(prefix[-1]+mass*a.exp()*level**2)
        for l in smooth[i+1:]:
            length=(arb(l)/k).log()
            # The float only suggests a grid index. The actual cutoff is certified.
            j=max(0,min(len(grid)-1,bisect_left(logs,float(length))-1))
            while j and not grid[j]<=length:
                j-=1
            if not grid[j]<=length:
                raise ArithmeticError("finite cutoff")
            total+=prefix[j]/(k*arb(l)**(1+e0))
    # zeta_Q(1+e)/log T >= density/(2*delta), X^(-e)>=Y^(-e)*exp(-e0*W).
    return density*(-e0*W).exp()*total/(2*delta*W**2)


if __name__=="__main__":
    ctx.prec=160
    for q in [2,6,30,210]:
        value=high_saving(arb(49),arb(".9"),arb("10.7"),arb("-4.85"),q)
        print(q,value.str(16))
        print("low",low_saving(arb(49),arb(".9"),arb("10.7"),arb("-4.85"),q).str(16))
