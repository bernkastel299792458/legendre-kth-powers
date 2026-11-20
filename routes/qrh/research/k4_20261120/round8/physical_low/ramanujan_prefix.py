"""Exact signed Ramanujan prefix envelopes on the one-turn low-frequency cells."""
from flint import fmpz
import numpy as np
from annular_inverse import harmonic_sums

def signed_maxima(Q,caps):
    cap=max(caps)
    if cap>700000000:
        core=max(v for v in (210,2310,30030,510510,9699690,223092870) if Q%v==0)
        if core<Q:
            divisors=[1]
            for p,_ in fmpz(Q//core).factor():
                divisors += [d*int(p) for d in divisors]
            # One period suffices at the base, since the zeroth moment has mean zero.
            asks={0,core}
            for n in caps:
                asks.update(min(n//d,core) for d in divisors)
            old=signed_maxima(core,asks)
            full,full1=old[core]
            phi=int(fmpz(core).euler_phi())
            out={}
            for n in caps:
                a=b=0
                for d in divisors:
                    m=n//d
                    x,y=old[min(core,m)]
                    a+=d*x
                    b+=d*d*(y+(m//core)*core*(2*full+phi)//2)
                out[n]=(a,min(b,2*n*a))
            return out
    primes=[int(p) for p,_ in fmpz(Q).factor()]
    sign=(-1)**len(primes);peak=running=peak1=running1=0
    last=0;out={}
    n0,n1=harmonic_sums(Q,max(caps))
    assert n0<2**62
    exact_first=n1<2**62
    for end in sorted(set(caps)):
        for lo in range(last+1,end+1,1<<18):
            hi=min(end+1,lo+(1<<18))
            c=np.full(hi-lo,sign,dtype=np.int64)
            for p in primes:c[(-lo)%p::p]*=1-p
            s=np.cumsum(c,dtype=np.int64)+running
            peak=max(peak,int(np.abs(s).max()));running=int(s[-1])
            if exact_first:
                s1=np.cumsum(c*np.arange(lo,hi,dtype=np.int64),dtype=np.int64)+running1
                peak1=max(peak1,int(np.abs(s1).max()));running1=int(s1[-1])
        out[end]=(peak,peak1 if exact_first else 2*end*peak);last=end
    return out
