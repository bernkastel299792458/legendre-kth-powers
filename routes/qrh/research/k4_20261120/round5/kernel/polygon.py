"""Certified Fourier envelope of a nonnegative symmetric polygon on [0,1]."""

from functools import lru_cache
from flint import arb, ctx


# Heights from the midpoint to the boundary. The common normalization is exact.
HEIGHT = (
    133332,133332,133332,133332,133332,133332,133332,133332,
    133332,133332,133332,133121,132764,132357,131929,131356,
    130669,129983,129296,128333,127370,126406,125327,124248,
    122951,121653,120271,118823,117376,115928,114323,112717,
    110979,109237,107485,105653,103693,101728,99698,97543,
    95388,93232,91077,88800,86523,84055,81587,78848,
    76110,73303,70496,67688,64763,61838,58675,55513,
    52350,49188,45406,41624,37249,32875,27690,22505,0,
)
N = len(HEIGHT)-1
TOTAL = 2*sum(HEIGHT)-HEIGHT[0]
SCALE = 10**9


def _ceiling(x):
    return int(x.upper().ceil().unique_fmpz())


@lru_cache(maxsize=8)
def _levels(step, tail, precision):
    if not (precision == ctx.prec and step > 0 and tail >= 2 and step % 2 == 0):
        raise ValueError("use a positive even grid denominator")
    if 3*2*N*max(HEIGHT) > 4*TOTAL:
        raise ArithmeticError("prime-power height exceeds the old 4/3 bound")
    spacing = arb(1)/(2*N)
    jumps = [2*(HEIGHT[1]-HEIGHT[0])]
    for j in range(1,N+1):
        after = HEIGHT[j+1] if j < N else 0
        jumps.append(2*(HEIGHT[j-1]-2*HEIGHT[j]+after))
    if sum(jumps) != 0:
        raise ArithmeticError("curvature identity")
    factor = arb((2*N)**2)/TOTAL
    total_variation = factor*sum(abs(k) for k in jumps)
    numerator_dd = sum(abs(k)*j**2 for j,k in enumerate(jumps))/arb(TOTAL)
    # The centered density is a mixture of translates of a triangle of variance h^2/6.
    moment2 = spacing**2*(arb(1)/6+2*sum(i*i*k for i,k in enumerate(HEIGHT))/arb(TOTAL))
    den_error = moment2/(8*step**2)
    num_error = numerator_dd/(8*step**2)

    # Clenshaw's formula evaluates the signed curvature polynomial as a whole.
    def numerator(i):
        x = 2*(arb(i)/(2*N*step)).cos()
        b1 = b2 = arb(0)
        for k in reversed(jumps[1:]):
            b1, b2 = x*b1-b2+k, b1
        return abs((jumps[0]+x*b1/2-b2)*factor)

    first = step//2
    left = numerator(first)
    vals = []
    for i in range(first,tail*step):
        low = arb(i)/step
        high = arb(i+1)/step
        right = numerator(i+1)
        cap_smooth = (left/low**2).max(right/high**2)+den_error
        cap_curve = (left.max(right)+num_error)/low**2
        vals.append(cap_smooth.min(cap_curve))
        left = right
    return vals, total_variation


def envelope(d, step=256, tail=192):
    vals, variation = _levels(step,tail,ctx.prec)
    first = step//2
    last = _ceiling(variation*SCALE/tail**2)
    if not (0 < last < SCALE):
        raise ArithmeticError("increase the tail cutoff")
    residual = arb(last)/SCALE
    jumps = []
    for j in range(len(vals)-1,-1,-1):
        i = first+j
        low = arb(i)/step
        cap = (vals[j]+d/2).min(variation/low**2)
        level = min(SCALE,_ceiling(cap*SCALE))
        if level > last:
            jumps.append((arb(i+1)/step,arb(level-last)/SCALE))
            last = level
    if last < SCALE:
        jumps.append((arb(first)/step,arb(SCALE-last)/SCALE))
    return jumps,residual


def height_groups(d, a, floor, step, tail):
    """Drop-in replacement for round3/spectrum/verify_height.height_groups at a=1/4."""
    if not (a-arb(1)/4).is_zero():
        raise ValueError("the prime-power bound uses the original a=1/4 normalization")
    jumps,residual = envelope(d,step,tail)
    cuts = (2,4,8,16,64)
    groups = [[] for _ in range(len(cuts)+1)]
    for y,w in jumps:
        y = y.max(floor)
        index = next((i for i,cut in enumerate(cuts) if y<=cut),len(cuts))
        groups[index].append(((y/4).log(),w))
    u, end = (4/d).log(), (arb(tail)/4).log()

    def moments(p,r):
        power = p+r/u
        if not power < 2:
            raise ValueError("nonintegrable tail")
        scale = (p*u+r*u.log()).exp()
        values = [sum((w*(power*z).exp() for z,w in group), arb(0)) for group in groups]
        values[-1] += residual*(power*end).exp()*2/(2-power)
        return [scale*v for v in values]
    return moments


if __name__ == "__main__":
    from pathlib import Path
    import sys
    sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round3"/"spectrum"))
    from verify_height import height_groups as old
    ctx.prec=192
    d=(4*arb(-42).exp()).log1p()
    args=(d,arb(1)/4,arb("1.45"),256,192)
    before,after=old(*args),height_groups(*args)
    print("height", (arb(2*N)*max(HEIGHT)/TOTAL).str(14))
    for p in map(arb,(".34",".37",".40",".45","1")):
        a,b=sum(before(p,1+p)),sum(after(p,1+p))
        print("p",p.str(4),"new/old", (b/a).str(14))
