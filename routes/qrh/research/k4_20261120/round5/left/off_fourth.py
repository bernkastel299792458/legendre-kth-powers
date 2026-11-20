"""Split small and large shifts in the off-diagonal fourth moment of zeta*E6."""

from fractions import Fraction
from functools import lru_cache
from itertools import product
from math import gcd
from flint import arb, arb_poly, ctx


def allowed(row, n):
    if row == 1:
        return gcd(n, 6) == 1
    if row == 3:
        return n % 2 == 1
    return True


def ball(x):
    return arb(x.numerator)/x.denominator


@lru_cache(maxsize=None)
def gcd_mass(A, B, i, k, modulus=30):
    g = gcd(A, B)
    # The true gcd is a multiple of the following periodic divisor.
    buckets = {}
    for a in range(1,modulus+1):
        if allowed(i,a):
            for c in range(1,modulus+1):
                if allowed(k,c):
                    divisor = g*gcd(gcd((A//g)*a,(B//g)*c),modulus)
                    buckets[divisor] = buckets.get(divisor,0)+1
    return sum(Fraction(n,d*modulus**2) for d,n in buckets.items())


def interval_discrepancy(values):
    """Sup of #(integer points)-density*length over arbitrary finite intervals."""
    if not values:
        return Fraction(0)
    rho = Fraction(len(values),6)
    right = max(j+1-rho*r for j,r in enumerate(values))
    left = min(j-rho*r for j,r in enumerate(values))
    return right-left


@lru_cache(maxsize=None)
def progression_data(j,l):
    # The reduced step lengths P,Q are coprime, so every congruence class
    # P*b-Q*d=h (mod 6) has precisely six pairs, given by one orbit of k.
    out = []
    for P,Q in product(range(6),repeat=2):
        if gcd(gcd(P,Q),6)!=1:
            continue
        ds,rs = [],[]
        for h in range(1,7):
            b0,d0 = next((b,d) for b,d in product(range(6),repeat=2) if (P*b-Q*d-h)%6==0)
            v = [t for t in range(6) if allowed(j,b0+Q*t) and allowed(l,d0+P*t)]
            ds.append(interval_discrepancy(v))
            rs.append(Fraction(len(v),6))
        out.append((tuple(ds),tuple(rs)))
    return set(out)


@lru_cache(maxsize=None)
def near_constants(j,l,precision):
    # H_(r mod 6)(y) <= log(y)/6 + kappa_r, y>=96.
    K = [sum(arb(1)/(r+6*k) for k in range(16))-arb(r+90).log()/6
         for r in range(1,7)]
    dbar=dconstant=rconstant=arb(0)
    for ds,rs in progression_data(j,l):
        dbar=dbar.max(ball(sum(ds)/6))
        dconstant=dconstant.max(sum(ball(x)*k for x,k in zip(ds,K)))
        rconstant=rconstant.max(sum(ball(x)*k for x,k in zip(rs,K)))
    return dbar,dconstant,rconstant


@lru_cache(maxsize=None)
def reciprocal_gap(precision):
    # x=log(m/n). For x<=1, sinh(x/2)/(x/2) <= 1/(1-x^2/24).
    # For x>=9 the difference is at most 1/9. Finite closed cells cover the rest.
    bound=arb(59)/500
    if not (arb(1)/24 < bound and arb(1)/9 < bound):
        raise ArithmeticError("reciprocal-gap tails")
    for i in range(1024,9*1024):
        a,b=arb(i)/1024,arb(i+1)/1024
        if not 1/a-1/(2*(b/2).sinh()) < bound:
            raise ArithmeticError("reciprocal-gap interior")
    return bound


_inv_lambdas = {1:Fraction(0),2:Fraction(1,2),3:Fraction(1,3),6:Fraction(1,2)}


def cone_integral(A,B,i,k):
    """Integral of the homogeneous reciprocal max on the clipped unit square."""
    lo=_inv_lambdas[i]
    hi=1/_inv_lambdas[k] if _inv_lambdas[k] else None
    points=[lo]+[v for v in sorted({Fraction(1),Fraction(B,A)})
                 if v>lo and (hi is None or v<hi)]+[hi]
    integral=arb(0)
    for a,b in zip(points,points[1:]):
        ab=ball(a)
        if b is not None:
            bb=ball(b)
        if b is not None and b<=1 and A*b<=B:
            integral+=(bb-ab)/B
        elif b is not None and b<=1:
            integral+=(bb/ab).log()/A
        elif b is not None and A*b<=B:
            integral+=(bb/ab).log()/B
        else:
            integral+=(1/ab-(0 if b is None else 1/bb))/A
    return integral


def off_bound(U):
    """An affine polynomial in log(T) bounding the off-diagonal integral / T."""
    pi=arb.pi()
    y0=(U/2).exp()/(2*pi).sqrt()
    if not y0>200:
        raise ValueError("minimum height for the shift split")
    ell=(arb_poly([0,1])-(2*pi).log())*(arb(1)/2)
    densities={r:arb(sum(allowed(r,k) for k in range(6)))/6 for r in (1,2,3,6)}
    derror={r:ball(interval_discrepancy([k for k in range(6) if allowed(r,k)]))
            for r in densities}
    total=arb_poly()
    for i0,j0,k0,l0 in product(densities,repeat=4):
        A,B=i0*j0,k0*l0
        best=None
        for (i,j),(k,l) in product(set(((i0,j0),(j0,i0))),set(((k0,l0),(l0,k0)))):
            alpha,beta=densities[i],densities[k]
            db,dd=densities[j],densities[l]
            eb,ed=derror[j],derror[l]
            area=1-ball(_inv_lambdas[i]+_inv_lambdas[k])/2
            first=(area+120/y0+3600/y0**2)*ball(gcd_mass(A,B,i,k))
            jcone=cone_integral(A,B,i,k)
            second=alpha*beta*(jcone+(144+12*((1+(A*y0).log())/A
                                                +(1+(B*y0).log())/B))/y0)
            # Any inner tail variable is >= max(a,c)/lambda.  If both
            # variables have this restriction, shorten either progression.
            inv_inner=ball(min(_inv_lambdas[j],_inv_lambdas[l]))
            # Use an interior rectangle, whose ratio is always in [1/2,2].
            lower_count=(alpha/2-2/y0)*(beta/2-2/y0)
            shorter=second-lower_count*inv_inner/max(A,B)
            dbar,dc,rc=near_constants(j,l,ctx.prec)
            for c in (arb(1)/2,arb(1),arb(2)):
                # Near: h/g <= c*Y. Far: h>=c*g*Y with h<=A*Y^2.
                near_log=ell+c.log()
                far_log=ell+(arb(A)/c).log()
                far_error=((db*ed).max(dd*eb)+eb*ed/y0)/c
                far_main=db*dd+(db*ed).max(dd*eb)/y0
                near=(dbar*near_log+dc)*first+(db*dd*near_log+rc)*shorter
                simple=(1+near_log)*(first+shorter)
                if simple(U)<near(U):
                    near=simple
                candidate=near+first*far_error+(shorter*db*dd
                              +second*((db*ed).max(dd*eb)/y0))*far_log
                if best is None or candidate(U)<best(U):
                    best=candidate
        total+=best
    # N_i(x)<=delta_i*x+1, hence sum_{n<=Y} n^-1/2 <=2*delta_i*sqrt(Y)+1.
    ef=sum((densities[i]+1/(2*y0.sqrt()))/arb(i).sqrt() for i in densities)
    # Positive shifts were counted above; for the symmetric additive remainder
    # the full quadruple norm counts both orientations simultaneously.
    return (4*total+32*reciprocal_gap(ctx.prec)*ef**4)*(1/(2*pi))


def fourth(U):
    """Return the new uniform normalized fourth moment; same interface as six_energy."""
    from six_energy import fourth as old_fourth
    return old_fourth(U,off_bound=off_bound)


if __name__=="__main__":
    ctx.prec=160
    U=arb(40)
    p=off_bound(U)
    print("off/T at logT=40",p(U).str(16),flush=True)
    print("uniform fourth constant",fourth(U).str(16),flush=True)
