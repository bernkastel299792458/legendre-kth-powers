"""Fixed-exponent high Selberg norm with exact Laurent derivative and signed tail breakpoints."""
from functools import lru_cache
from math import gcd
from flint import arb,arb_series,ctx


@lru_cache(maxsize=64)
def mobius(q,N):
    values=[1]*(N+1);prime=bytearray(b"\1")*(N+1)
    for p in range(2,N+1):
        if not prime[p]:continue
        for j in range(p,N+1,p):
            values[j]=-values[j]
            if j!=p:prime[j]=0
        for j in range(p*p,N+1,p*p):values[j]=0
    return [(n,values[n]) for n in range(1,N+1) if values[n] and gcd(n,q)==1]


def sharp(U,delta,W,lh,q,N=4096):
    e=2*delta/U; v=2+e;Y=(U+lh).exp();S=arb(8)
    primes=[p for p in (2,3,5,7,11) if q%p==0]
    assert 0<e<arb(".1") and Y>1 and q in (210,2310)
    eta=arb(1);jet=arb_series([v,1],prec=2);z=jet.zeta()
    for p in primes:
        eta*=1-1/arb(p)
        z*=1-(-arb(p).log()*jet).exp()
    inverse=1/z;D=inverse[0];F=-inverse[1]
    terms=mobius(q,N);ns=[i for i,_ in terms]
    logs=[arb(n).log() for n in ns]
    weights=[m*(-v*l).exp() for l,(_,m) in zip(logs,terms)]
    a0=[arb(0)]*(len(ns)+1);a1=a0.copy()
    for i in reversed(range(len(ns))):
        a0[i]=a0[i+1]+weights[i];a1[i]=a1[i+1]+weights[i]*logs[i]
    ln=arb(N).log();cn=(1-v)*ln
    spikes=[a1[i]-l*a0[i] for i,l in enumerate(logs)]
    def index(t):
        # It is harmless to include the breakpoint with vanishing (log n-t).
        a,b=0,len(ns)
        while a<b:
            m=(a+b)//2
            if logs[m]<=t:a=m+1
            elif logs[m]>t:b=m
            else:
                # Exact zero or overlapping tiny Arb balls. Either affine piece
                # is valid at the common breakpoint; the unresolved term is enclosed.
                break
        if a!=b:
            assert abs(logs[m]-t)<arb("1e-35")
            return m
        return a
    def rest(a,b):
        # W-b is exactly zero at the final mesh endpoint; intersect its enclosure.
        a=a.max(arb(0));b=b.max(arb(0))
        assert a<=b
        simple=arb("1.2")*(-(v-1)*a).exp()
        if a>=ln:return -simple,simple
        start,end=index(a),index(b)
        za=a1[start]-a*a0[start];zb=a1[end]-b*a0[end]
        low=za.min(zb);high=za.max(zb)
        for x in spikes[start:end]:
            low=low.min(x);high=high.max(x)
        # The positive decreasing unsieved tail can start at N. The a=0
        # version is valid even if b extends beyond log N.
        err=cn.exp()*(ln/(v-1)+1/(v-1)**2)+arb("1e-34")
        return (low-err).max(-simple),(high+err).min(simple)
    def den(a,b):
        return (eta*(b.exp()-a.exp())+arb(2**len(primes))/Y)*(-v*a).exp()
    disc=arb(2**len(primes))
    head=arb("1.2")**2*(1+(-W).exp())**2*(eta+disc*S.exp()/Y)*(-(1+e)*S).exp()
    for i in range(192):
        a,b=-S+S*i/192,-S+S*(i+1)/192
        l,h=rest(-b,-a);ll,hh=rest(W-b,W-a)
        head+=den(a,b)*abs(l-hh).max(abs(h-ll))**2
    middle=arb(0)
    for i in range(512):
        a,b=W*i/512,W*(i+1)/512
        l,h=rest(W-b,W-a)
        middle+=den(a,b)*abs(a*D+F-h).max(abs(b*D+F-l))**2
    tail=(eta/(1+e)+disc/Y)*(-(1+e)*W).exp()*(W*D)**2
    return z[0]*(head+middle+tail)/((lh).exp()*W**2)
