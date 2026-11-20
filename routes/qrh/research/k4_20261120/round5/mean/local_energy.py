"""Folded right mean with exact local divisor-pair densities, uniform for T >= exp(U)."""

from functools import lru_cache
from math import ceil, gcd, prod
import argparse

import numpy as np
from flint import arb, ctx


@lru_cache(maxsize=None)
def gram_bounds(q, max_length=None):
    """Rational upper bounds scaled by 10^6. Floating eigenvalues only propose trials."""
    primes = [p for p in (2, 3, 5, 7, 11) if q % p == 0]
    if not primes or primes[0] != 2 or prod(primes) != q:
        raise ValueError("an even squarefree sieve modulus is needed")
    period = q//2
    count = prod(p-1 for p in primes)
    scale = 10**6
    # A whole period of Fourier vectors gives period*I.
    bounds = [0, count*scale] + [period*scale]*(period-1)
    gram = [prod(p-1 if h % p == 0 else -1 for p in primes) for h in range(period)]
    largest = period-count if max_length is None else min(period-count,max_length)
    for k in range(2, largest+1):
        row = np.arange(k)
        matrix = np.asarray(gram)[np.abs(row[:, None]-row)]
        guess = ceil(float(np.linalg.eigvalsh(matrix)[-1])*scale)+20
        if guess >= period*scale:
            continue
        rows = [[arb(-gram[i-j]) for j in range(i)] + [arb(guess)/scale-count]
                for i in range(k)]
        passed = True
        for i in range(k):
            pivot = rows[i][i]
            if not pivot > 0:
                passed = False
                break
            for j in range(i+1, k):
                factor = rows[j][i]/pivot
                for l in range(i+1, j+1):
                    rows[j][l] -= factor*rows[l][i]
        if passed:
            bounds[k] = guess
    return primes, bounds


def _factor_table(limit):
    """mu(k)*prod_{p|k}p/(p+1) and 2^omega(k), needed only at squarefree k."""
    numer = [1]*(limit+1)
    denom = [1]*(limit+1)
    subsets = [1]*(limit+1)
    for p in range(2, limit+1):
        if subsets[p] != 1:
            continue
        for j in range(p, limit+1, p):
            numer[j] *= -p
            denom[j] *= p+1
            subsets[j] *= 2
        for j in range(p*p, limit+1, p*p):
            numer[j] = 0
    return [arb(n)/d for n,d in zip(numer,denom)], subsets


def _pair_rows(q, primes, limit):
    """Coefficient update at each max(r,s), together with a squarefree count error."""
    return _cached_pair_rows(q,tuple(primes),limit,ctx.prec)


@lru_cache(maxsize=48)
def _cached_pair_rows(q,primes,limit,precision):
    assert precision==ctx.prec
    weight, subsets = _factor_table(limit)
    units = [r for r in range(1, limit+1) if gcd(r,q) == 1]
    logs = [arb(0)] + [arb(i).log() for i in range(1,limit+1)]
    invsqrt = [arb(0)] + [1/arb(i).sqrt() for i in range(1,limit+1)]
    qmass = prod(arb(p)/(p+1) for p in primes) / (arb.pi()**2/6)
    qsubsets = 2**len(primes)
    rows = {}
    for j,s in enumerate(units):
        a2 = a1 = a0 = err = arb(0)
        for r in units[:j+1]:
            g = gcd(r,s)
            a,b = r//g,s//g
            if weight[a] == 0 or weight[b] == 0:
                continue
            symmetry = 1 if r == s else 2
            pair = symmetry * weight[a]*weight[b]/(s*a)
            a2 += pair
            a1 -= pair*(logs[r]+logs[s])
            a0 += pair*logs[r]*logs[s]
            err += symmetry*(qsubsets*subsets[a]*subsets[b]+2)*invsqrt[s]*invsqrt[a]
        rows[s] = (qmass*a2, qmass*a1, qmass*a0, err)
    return rows


def _upper_floor(x):
    return int(x.upper().floor().unique_fmpz())


def local_right_rows(U, delta, W, logh, q, cells=16, spacing=None, outer_spacing=None,
                     frequency_cut=None):
    """Return (C_H, B_rows, tail_factor): see RIGHT.md for the normalized mean bound."""
    spacing = q if spacing is None else spacing
    if spacing <= 0 or q % spacing:
        raise ValueError("spacing must divide the sieve modulus")
    primes = [p for p in (2, 3, 5, 7, 11) if q % p == 0]
    if prod(primes) != q:
        raise ValueError("squarefree sieve modulus required")
    _, bounds = gram_bounds(spacing)
    period = spacing//2
    units = bounds[1]//10**6
    v, order = arb("1.01"), 2048
    tail_cut = arb("1.03")
    h = logh.exp()
    T0 = U.exp()
    emax = 2*delta/U
    eps = (v*T0)**(-arb(1)/5)
    mass = 1-4*eps/arb.pi()
    if not mass > 0 or not delta > 0 or not h < 1 or cells < 1:
        raise ValueError("positive height, exponent and taper required")
    correction = ((1+eps)*eps*(2*eps**3).exp()).exp()/mass
    k0 = arb.pi()*units/spacing
    base_scale = v*tail_cut*(1+eps)*(eps**3).exp()/arb.pi()
    xscale = spacing*base_scale
    cutoff = xscale
    tail_units = units
    if (outer_spacing is None) != (frequency_cut is None):
        raise ValueError("supply both an outer modulus and a positive cutoff")
    if outer_spacing is not None:
        cutoff = arb(frequency_cut)
        if outer_spacing <= 0 or q % outer_spacing or not cutoff > 0:
            raise ValueError("outer modulus must divide Q and cutoff must be positive")
        outer_scale = outer_spacing*base_scale
        max_outer = _upper_floor(outer_scale/cutoff)+1
        if max_outer > outer_spacing//2:
            raise ValueError("choose cutoff with at most one outer period in the high range")
        # Fully resolve the range near the transfer as well as all n >= cutoff*T.
        partial = min(outer_spacing//2, max(32, max_outer))
        _, outer = gram_bounds(outer_spacing, partial)
        tail_units = outer[1]//10**6
        k0 = arb.pi()*outer[max_outer]/(10**6*outer_spacing)
    limit = _upper_floor(cutoff/h)+1
    if not arb(limit).log() <= W:
        raise ValueError("local energy extends past the upper taper endpoint")
    pairs = _pair_rows(q, primes,limit)
    spectrum = [arb(0) for _ in range(cells)]
    local_error = arb(0)
    a2 = a1 = a0 = err = arb(0)
    for r in range(1,limit):
        if r in pairs:
            c2,c1,c0,ce = pairs[r]
            a2 += c2
            a1 += c1
            a0 += c0
            err += ce
        steps = 32 if r<12 else (8 if r<70 else 1)
        for j in range(steps):
            z0 = h*(r+arb(j)/steps)
            z1 = h*(r+arb(j+1)/steps)
            t0, t1 = (z0/h).log(), (z1/h).log()
            count = _upper_floor(xscale/z0)+1
            cycles, residue = divmod(count-1,period)
            if outer_spacing is None:
                spectral_excess = cycles*period + arb(bounds[residue+1])/10**6-units
                charge = arb.pi()*z1*spectral_excess/spacing
            else:
                eigen = cycles*period + arb(bounds[residue+1])/10**6
                per_index = arb.pi()*eigen/spacing
                count_outer = _upper_floor(outer_scale/z0)+1
                if count_outer <= partial:
                    per_index = per_index.min(arb.pi()*outer[count_outer]/(10**6*outer_spacing))
                charge = z1*(per_index-k0).max(arb(0))
            if charge == 0:
                continue
            # Supremum of the quadratic density using a Taylor expansion at the midpoint.
            mid, rad = (t0+t1)/2, (t1-t0)/2
            density = (a2*mid+a1)*mid+a0
            density += abs(2*a2*mid+a1)*rad+abs(a2)*rad**2
            if not density >= 0:
                raise ArithmeticError("negative or indeterminate local quadratic upper bound")
            # Every taper is bounded by min(1,t1/W). Abel summation uses one-sided endpoints.
            error = 2*err*(z1/T0).sqrt()*(t1/W)**2
            local_error += charge*error/z0**2
            amount = charge*(z1-z0)*density/(W*z0)**2
            power = arb(1)
            step = (-emax*t0/cells).exp()
            for i in range(cells):
                spectrum[i] += amount*power
                power *= step
    # Each extra Fourier vector has squared norm 'units'. This gives a
    # universal slope 'units' and the same intercept k0 on the remote time tail.
    tail_factor = (1+eps)*v*order/(order-1)*tail_cut**(1-order)*tail_units
    return correction*k0, [correction*(val+local_error) for val in spectrum], correction*tail_factor


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--U", default="42.98")
    cli.add_argument("--delta", default=".92")
    cli.add_argument("--width", default="9.5")
    cli.add_argument("--logh", default="-3.5")
    cli.add_argument("--modulus", type=int, default=210)
    cli.add_argument("--spacing", type=int)
    cli.add_argument("--outer-spacing", type=int)
    cli.add_argument("--frequency-cut")
    cli.add_argument("--cells", type=int, default=16)
    args = cli.parse_args()
    ctx.prec = 192
    result = local_right_rows(*map(arb, (args.U, args.delta, args.width, args.logh)),
                              args.modulus, cells=args.cells, spacing=args.spacing,
                              outer_spacing=args.outer_spacing, frequency_cut=args.frequency_cut)
    print("Hilbert", result[0].str(16))
    print("Local cells", " ".join(x.str(12) for x in result[1]))
    print("Far time tail", result[2].str(10))
