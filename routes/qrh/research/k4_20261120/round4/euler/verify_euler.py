"""Conditional fourth-power certificate with complete small Euler factors."""
import argparse
import math
from pathlib import Path
import sys

from flint import arb, ctx

research = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(research / "round3" / "spectrum"))
from verify_height import A, check, coefficient, fourth_constant, height_groups, quintic_bound, sharp_right
sys.path.insert(0, str(research / "round4" / "density"))
from variance import high_saving, low_saving
from direct_high import direct_high
from verify_fine import signed_high_norm
sys.path.insert(0, str(research / "round4" / "hilbert"))
from periodic_hilbert import hilbert_coefficient
from linear_mean import linear_mean_coefficients


def prime_factors(q):
    primes = [p for p in (2, 3, 5, 7, 11) if q % p == 0]
    check(math.prod(primes)==q, "squarefree modulus with verified sieve primes")
    return primes


def discrepancy(q):
    """Maximum of count minus length*phi(q)/q on any open/closed interval."""
    units = [i for i in range(1,q+1) if math.gcd(i,q)==1]
    residues = units+[i+q for i in units]
    phi = len(units)
    worst = max((j-i+1)*q-phi*(residues[j]-residues[i])
                for i in range(phi) for j in range(i,i+phi))
    return arb(worst)/q


def boundary(U, delta, W, logh, q, spacing, split_left, bandwidth=None, variance=True,
             direct=False, periodic=False, fold=None, mellin=False):
    primes = prime_factors(q)
    check(spacing > 0 and q % spacing == 0, "spacing modulus divides sieve modulus")
    classes = math.prod(p-1 for p in prime_factors(spacing))
    T = U.exp()
    order, v = 2048, A("1.01")
    ybar = v*order/(order-1)
    w, padding = A(".001"), arb(10**9)
    mass = 1-4/(arb.pi()*w*padding)
    check(mass>0, "positive localized time mass")
    hilbert = arb.pi()*w.exp()/mass
    diagonal = (ybar+padding/T)/mass

    # Frequencies in each unit class are separated by at least spacing
    # times the old local gap. Cauchy over the classes costs their number.
    old_hilbert = arb.pi()*(1+A("2/3")*A("6/5").sqrt()).sqrt()
    right_hilbert = classes*hilbert/spacing
    right_diagonal = classes*diagonal
    check(sum((bandwidth is not None, periodic, fold is not None))<=1,
          "choose one right mean-value bound")
    if bandwidth is not None:
        alpha = A(bandwidth)
        check(0<alpha and alpha<arb.pi(), "positive sinc time majorant")
        inverse_sinc = ((alpha/2)/(alpha/2).sin())**2
        right_hilbert = arb.pi()*inverse_sinc*(alpha/(v*T)).exp()*classes/spacing
        right_diagonal = arb.pi()*inverse_sinc*discrepancy(spacing)*ybar/alpha
    if periodic:
        right_hilbert = hilbert_coefficient(spacing,w,padding)
        right_diagonal = diagonal
    if fold is not None:
        right_diagonal, right_hilbert = linear_mean_coefficients(spacing,v*T,ybar,fold)
    original_diagonal = right_diagonal
    if variance or direct or mellin:
        high_base = signed_high_norm(logh.exp(),W,(U+logh).exp(),2*delta/U)
        saving = high_saving(U,delta,W,logh,q) if variance else arb(0)
        check(0<=saving and saving<high_base, "nonnegative remaining high norm")
        high_bound = high_base-saving
        if direct:
            high_bound = high_bound.min(direct_high(U,delta,W,logh,q))
        right_diagonal *= high_bound/high_base
    scale = right_hilbert/old_hilbert
    kappa = arb.pi()*scale**2/(8*right_diagonal**2)
    right = scale*sharp_right(U,delta,kappa,W,logh)
    if variance:
        right -= right_hilbert*(-2*delta).exp()*low_saving(U,delta,W,logh,q)
        check(right>0, "positive right-boundary constant")
    if mellin:
        from mellin_low import mellin_low_rows
        rows = mellin_low_rows(U,delta,W,logh,q,cells=16)
        spectral = arb(0)
        for i, low_bound in enumerate(rows):
            lower = 2*delta*i/(U*len(rows))
            upper = 2*delta*(i+1)/(U*len(rows))
            discount = (-2*delta-upper*logh).exp()
            high = high_bound*(2+lower).zeta()/arb(2).zeta()
            spectral = spectral.max(discount*(right_hilbert*low_bound
                               +original_diagonal*high*upper/(2*delta)))
        right = right.min(spectral)

    # Coefficients of M_q at r*d, r|q and (d,q)=1, have modulus
    # mu^2(r)*|mu(d)|*omega(d). These representations are unique.
    divisors = {1: 1}
    for p in (2,3,5,7,11):
        factor = p if p in primes else p*p
        divisors.update({factor*d: -sign for d,sign in divisors.copy().items()})
    density = sum(arb(sign)/d for d,sign in divisors.items())
    offset = sum((max(sign,0)-sign*arb(d).log())/d for d,sign in divisors.items())
    check(T*logh.exp()>max(divisors), "whole use of harmonic sieve above its range")
    harmonic = density+(density*(W/3+logh)+offset).max(arb(0))/U
    taper = 2*(W+logh).exp()*(1-(1+W)*(-W).exp())/W**2
    tail = sum(sign<0 for sign in divisors.values())
    unweighted = density*taper+tail/T
    if split_left:
        check(q%2==0, "critical-line fourth moment requires 2 in the modulus")
        from sieved_fourth import fourth_six, fourth_two
        filtered = 6 if q%6==0 else 2
        fourth = fourth_six(U) if filtered==6 else fourth_two(U, phased=True)
        remaining = [p for p in primes if filtered%p]
        r_mass = math.prod(1+arb(1)/p for p in remaining)
        left_diagonal = diagonal
        left_hilbert = hilbert_coefficient(filtered,w,padding) if periodic else hilbert/2
        if fold is not None:
            left_diagonal, left_hilbert = linear_mean_coefficients(filtered,v*T,ybar)
        cm = left_diagonal*r_mass*harmonic+left_hilbert*2**len(remaining)*unweighted/U
    else:
        fourth = fourth_constant(U,phased=True,averaged=True,shifted=True)
        r_mass = math.prod(1+arb(1)/p for p in primes)
        cm = diagonal*r_mass*harmonic+hilbert*2**len(primes)*unweighted/U
    c4 = fourth*v**(1+4/U)*order/(order-1-4/U)
    left = (c4**A("1/4")*cm.sqrt()+ybar**A("3/4")/U**A("3/2"))**A("4/3")
    eps = A(".000001")
    check(T>10**10 and ((1+2/T)/v)**order<eps and 4*order/T<1
          and 1/(1-(A(".5")+2/T)**order)<1+eps, "analytic window")
    return left, right, (1+eps)**2/(1-1/arb(3*10**12))


def verify(anchor, modulus, spacing, shift, transition, cutoff, split_left=False, bandwidth=None,
           variance=True, direct=False, periodic=False, fold=None, mellin=False, breakdown=False):
    L, delta, W, logh = map(A,(anchor,shift,transition,cutoff))
    U = L/4-A("1.02")
    epsilon = 4*(-L/4).exp()
    d = epsilon.log1p()
    floor = A("1.45")
    umin = (floor/d).log()
    check(umin>U and umin>arb(3*10**12).log(), "all effective heights")
    left,right,norm = boundary(U,delta,W,logh,modulus,spacing,split_left,
                              bandwidth,variance,direct,periodic,fold,mellin)
    print("K1, K3",left.str(16),right.str(16),flush=True)
    ratio = left/right
    heights = height_groups(d,A("1/4"),floor,256,192)
    knots = [arb(i)/1000 for i in range(650,869)]+[A("7/8")]
    base = 2*((knots[0]-1)*L).exp()*sum(heights(arb(1),arb(1)))
    check(knots[0]-1+A("1/4")+1/(4*umin)<0, "base decreases")
    jlog = A("15/14").log()
    check(arb(modulus)*(logh+W).exp()>=1 and 9/((U+logh)/2).exp()<A("1/4"),
          "Jensen disk and right edge")
    outer = (11*arb(modulus).sqrt()*((logh+W)/2).exp()).log()
    edge = 162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+9*outer)/jlog)
    edge += 27*sum(heights(arb(0),arb(1)))/jlog
    cost = last = arb(0)
    terms = []
    for s,t in zip(knots,knots[1:]):
        p = 3*(1-s)/(2-s)
        lo,hi = (2+4*delta/U)/(2-s+3*delta/U),2/(2-s)
        check(A("1.4")<=lo and hi<=A("16/9"),"detector domain")
        cd = coefficient(lo,hi)
        quin = quintic_bound(lo,hi)
        if quin is not None:
            cd = cd.min(quin)
        k,c = 3*delta*(2*s-1)/(2-s)**2,3*delta/(2-s)
        check(c+1+c/U<(U*ratio).log(),"height correction decreases")
        B = cd*norm**hi*right*ratio**p*(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
        slope = ((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        check(slope>last and t-1+2/L+p/4+(1+p)/(4*umin)<0
              and t-1+2/L+1/(4*umin)<0, "all slope jumps and decay rates")
        contribution = 2*(slope-last)*B*sum(heights(p,1+p))
        cost += contribution
        if breakdown:
            exponent = 1-p-k/(U+c)
            check(exponent>0 and contribution>0, "right-boundary sensitivity")
            terms.append((contribution,exponent))
        last = slope
    check(2/L<A("1/4"),"prime powers decrease")
    powers = (1+epsilon)**A("1.5")*(L+d)**2*(-L/4).exp()/(6*arb(2).log())
    trivial = (-3*L).exp()/(1-(-2*L).exp())
    fixed = base+2*last*edge+powers+trivial
    print("L",anchor,"modulus",modulus,"spacing",spacing,"fixed",fixed.str(11),
          "total",(fixed+cost).str(20),flush=True)
    if breakdown:
        return fixed, left, right, terms
    return fixed+cost


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",default="184.5")
    cli.add_argument("--modulus",type=int,default=6)
    cli.add_argument("--spacing",type=int,default=6)
    cli.add_argument("--shift",default=".9")
    cli.add_argument("--transition",default="9.6")
    cli.add_argument("--cutoff",default="-2.8")
    cli.add_argument("--split-left",action=argparse.BooleanOptionalAction, default=True)
    cli.add_argument("--bandwidth",help="use the triangular Fourier window at this scaled bandwidth")
    cli.add_argument("--no-variance",action="store_false",dest="variance")
    cli.add_argument("--direct",action="store_true",help="also use the coprime finite high-norm sum")
    cli.add_argument("--periodic",action="store_true",help="apply the periodic Hilbert estimate")
    cli.add_argument("--fold",choices=("unit","middle","density"),
                     help="use the linearized short-window estimate")
    cli.add_argument("--mellin",action="store_true",help="also bound the low norm by a Mellin integral")
    args = cli.parse_args()
    ctx.prec = 192
    check(verify(**vars(args))<1,"prime in the full half-line")
