"""Actual sample moments of the first prime frequencies of the finite detector."""
from functools import lru_cache
from math import isqrt, factorial
from flint import arb, ctx

N = 32768
H = 3000175332800


@lru_cache(maxsize=None)
def prime_bins(end):
    sieve = bytearray([1])*(end+1)
    for p in range(2,isqrt(end)+1):
        if sieve[p]:
            sieve[p*p::p] = bytes(1+(end-p*p)//p)
    return [(n, sum(sieve[n+1:min(n+33,end+1)])) for n in range(N,end,32)]


def samples(j,k,end):
    s = arb(j)/1000
    top = arb(7)/8
    t = arb(H)*(arb(k)/4).exp()
    v = t*arb("1.01")
    budget = 6*t.log()*t**(3*(1-s)/(3*s-1))
    A = (2*t).log()/2+3
    best = None
    for power in range(2,10):
        r = 1/(power*arb(N).log())
        x = s-r
        assert x>arb(1)/2 and r<1
        # All counted zeros and their left partners occur in the Poisson sum.
        def lower_kernel(a,b):
            return 1/(b+r**2/a)
        lower = lower_kernel(2-top,2-s)+lower_kernel(1+s,1+top)
        q0 = q1 = arb(0)
        for left, count in prime_bins(end):
            value = count*arb(left)**(-2*x)
            q0 += value
            # For 1-2x<0, the same left bin edge bounds the weighted sum.
            q1 += left*value
        length = v-H+2*r
        mean = factorial(power)*((length+5)*q0**power+10*q1**power)
        sample = A/lower*mean/(arb.pi()*r**2*2*power*arb(N).log()*budget)
        root = sample**(arb(1)/(2*power))
        best = root if best is None else best.min(root)
    return best


if __name__ == "__main__":
    ctx.prec = 160
    for end in (N+2048,N+4096,N+8192,2*N):
        overall = arb(0)
        best_ratio = arb(100)
        for k in (1,4,9,17,30,51):
            for j in (800,820,837,852,865):
                point = samples(j,k,end)
                trivial = sum(n*arb(a)**(-arb(j)/1000) for a,n in prime_bins(end))
                overall = overall.max(point)
                best_ratio = best_ratio.min(point/trivial)
        print("prime band",N,end,"uniform RMS allowance",overall.str(13),
              "best ratio to direct majorant",best_ratio.str(10),flush=True)
        assert best_ratio > (arb('.91') if end==2*N else arb('1.61'))
