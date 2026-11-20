"""Certified signed adjacent products for the Gaussian square AFE at T=3e12."""
import argparse
from collections import Counter
from flint import arb, ctx, fmpz


T, X = 3*10**12, 10**10
SIGMA_NUM, SIGMA_DEN = 7, 8


def divisors_with_mobius(n):
    """All nonzero sharp mollifier coefficients whose indices divide n."""
    result = [(1, 1)]
    for p, _ in fmpz(n).factor():
        p = int(p)
        result += [(p*d, -mu) for d, mu in result if p*d <= X]
    return result


def nodes(order, r):
    """Positive Gauss weights on unit panels of [-8,8] in standardized height."""
    pi = arb.pi()
    u0 = arb(T)/pi
    for i in range(-8, 8):
        for j in range(order):
            root, weight = arb.legendre_p_root(order, j, weight=True)
            w = i+(1+root)/2
            log_u = (u0*(1+w/20)).log()
            yield w, weight*(-w*w).exp()/(2*pi.sqrt()), log_u, (-r*log_u).exp()


def block(start, length, shifts):
    assert start >= T and 1 <= shifts <= 8 and length >= 1
    pi = arb.pi()
    sigma = arb(SIGMA_NUM)/SIGMA_DEN
    r = 2*sigma-1
    scale = arb(X)**r
    order = 12
    points = list(nodes(order, r))
    # For |z-mid|<=2 the complete node integrand per signed coefficient
    # is <=1000. Positive GL weights and exactness through degree 2N-1
    # give this two-sided error on all 16 panels.
    quadrature = arb(32)*1000*(arb(1)/4)**(2*order)/(1-arb(1)/4)
    omitted = 3*arb(8).erfc()
    gamma = arb(3200)/arb(T)**2
    unsigned_mass = [arb(0) for _ in range(shifts)]
    signed_sum = [arb(0) for _ in range(shifts)]
    errors = [arb(0) for _ in range(shifts)]
    counts = [0 for _ in range(shifts)]
    divisors = {k: divisors_with_mobius(k) for k in range(start,start+length+shifts)}
    for k in range(start,start+length):
        for h in range(1,shifts+1):
            l = k+h
            # Combine identical mn exactly and keep the original unsigned counts.
            signed, unsigned = Counter(), Counter()
            for d, md in divisors[k]:
                for e, me in divisors[l]:
                    mn = (k//d)*(l//e)
                    signed[mn] += md*me
                    unsigned[mn] += 1
            data = [(arb(mn).log(), arb(mn)**r, signed[mn], count)
                    for mn, count in unsigned.items()]
            omega = (arb(h)/k).log1p()*T/10
            coeff = 2*scale/arb(k*l)**sigma   # both orientations
            signed_k, mass_k = arb(0), arb(0)
            for w, weight, log_u, inv_ur in points:
                s, m = arb(0), arb(0)
                for log_mn, mnr, mc, count in data:
                    f = (1+mnr*inv_ur)*((log_mn-log_u)/2).erfc()/2
                    s += mc*f
                    m += count*f
                signed_k += weight*(omega*(20+w)).cos()*s
                mass_k += weight*m
            idx = h-1
            count = sum(unsigned.values())
            counts[idx] += count
            signed_sum[idx] += coeff*signed_k
            unsigned_mass[idx] += coeff*mass_k
            errors[idx] += coeff*count*(quadrature+omitted+gamma)
    net = arb(0)
    norm = arb(0)
    for i, (value, mass, err) in enumerate(zip(signed_sum,unsigned_mass,errors)):
        signed = value+arb(0,err.upper())
        positive = mass+arb(0,err.upper())
        net += signed
        norm += positive
        print("gap", i+1, "pairs", counts[i], "signed", signed.str(10),
              "absolute envelope", positive.str(10), flush=True)
    print("block starting",start,"length",length,"combined",net.str(12),
          "absolute envelope",norm.str(12),"ratio", (net/norm).str(12), flush=True)
    return net, norm


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--start", type=int, default=T)
    parser.add_argument("--length", type=int, default=16)
    parser.add_argument("--shifts", type=int, default=4)
    args = parser.parse_args()
    ctx.prec = 96
    block(args.start,args.length,args.shifts)
