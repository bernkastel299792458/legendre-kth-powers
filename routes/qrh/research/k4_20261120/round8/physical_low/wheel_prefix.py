"""Complete physical prefixes using a larger unit wheel, with explicit new frequency scales."""
from functools import lru_cache
from itertools import combinations
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants,costs
from odd_sieve import denominator
from whole_spike import upper,shared_lower
from annular_inverse import cost
from compact_spline import run as spline

@lru_cache(None)
def physical(k,Q,prec,width,anchored=False,conditional=False):
    assert ctx.prec==prec
    ps=[p for p in range(2,k) if fmpz(p).is_prime() and Q%p]
    # R<k. Verify that no four-dimensional Boolean counterexample can occur.
    good=len(ps)<=4 and all(b*d>=k*a for a,b,c,d in combinations(ps,4))
    assert len(ps)<2 or ps[0]*ps[1]>=k
    PP=max(37,max(int(p) for p,_ in fmpz(Q).factor()))
    s,e=upper(k,PP,Q,width=width);raw=s+e
    if good:
        for g in ps:
            raw-=shared_lower(k,g,max(23,max(int(p) for p,_ in fmpz(Q).factor()),g),Q)
    else:
        anchors=set(ps[:3]) if anchored else set()
        for g in ps:
            if g in anchors:
                raw-=shared_lower(k,g,max(23,max(int(p) for p,_ in fmpz(Q).factor()),g),Q)
            else:
                v,d=upper(k,PP,Q,g,width=width);part=v+d
                if conditional:
                    from moving_anchor import rare
                    lower=shared_lower(k,g,max(PP,g),Q)
                    part=part.min(2*rare(k,g,Q,width)-lower)
                raw+=part
    return raw,good

def run(Q,cut,harmonic_limit=210,width=".0002",tiny_arg=None,same_j=False,unit_small=False,fast_low=False,anchored=False,conditional=False,physical_spectrum=False,ordered_small=False,selberg_small=False,exact_spectrum=False,signed_prefix=False):
    assert Q%210==0 and fmpz(Q).moebius_mu() and harmonic_limit>=cut>=23
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();xl=(c-2*r).exp()
    ks=[k for k in range(2,cut) if gcd(k,Q)==1]
    assert z*z<xl and all(xl/k>X/cut for k in ks)
    assert not conditional or anchored
    if physical_spectrum:
        from physical_l2 import physical as signed
        acts=sum((signed(k,Q,tau=".3" if exact_spectrum else ".4",width=width,exact=exact_spectrum)[-1] for k in ks),arb(0))
    else:
        acts=sum((physical(k,Q,ctx.prec,width,anchored,conditional)[0] for k in ks),arb(0))
    eta=arb(int(fmpz(Q).euler_phi()))/Q
    main=u*(2*r).exp()*A*eta/denominator(z,Q)
    _,upstream,remote=costs(1732099);other=upstream+remote
    pref=cost(1,cut,mean_only=True,mod=Q,harmonic_limit=harmonic_limit,width=width)[1]
    pts=[cut]
    while pts[-1]<harmonic_limit:pts.append(min(harmonic_limit,(5*pts[-1]+3)//4))
    if fast_low:
        from wheel_low import low as grouped
        low=grouped(Q,cut,harmonic_limit,width,signed_prefix=signed_prefix)
    else:
        low=sum((cost(a,b,low_only=True,mod=Q,harmonic_limit=harmonic_limit,width=width)[1] for a,b in zip(pts,pts[1:])),arb(0))
    J=4*10**18 if same_j else 4*10**18*(Q//210)
    tinylog=arb(tiny_arg) if tiny_arg is not None else arb("70.7")-(arb(Q)/210).log()-1
    assert 0<arb(width)<1 and 1<tinylog.exp()<X/harmonic_limit
    _,_,ordinary,high,tiny=spline(1732099,Q,cut,width,J,64,tinylog)
    if unit_small:
        from wheel_small import small
        tiny=tiny.min(small(Q,tinylog,width,ordered=ordered_small,selberg=selberg_small)[1])
    rem=1-main-other-ordinary-high-tiny-acts-pref-low
    return main,acts,pref,low,ordinary,high,tiny,tinylog,rem

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--Q",type=int,default=2310)
    ap.add_argument("--cut",type=int,default=31);ap.add_argument("--harmonic-limit",type=int,default=210)
    ap.add_argument("--width",default=".0002");ap.add_argument("--tiny-log");ap.add_argument("--same-j",action="store_true")
    ap.add_argument("--unit-small",action="store_true");ap.add_argument("--fast-low",action="store_true")
    ap.add_argument("--anchored",action="store_true")
    ap.add_argument("--conditional",action="store_true")
    ap.add_argument("--physical-spectrum",action="store_true")
    ap.add_argument("--ordered-small",action="store_true")
    ap.add_argument("--selberg-small",action="store_true")
    ap.add_argument("--exact-spectrum",action="store_true")
    ap.add_argument("--signed-prefix",action="store_true")
    ap.add_argument("--lower");a=ap.parse_args();ctx.prec=144
    v=run(a.Q,a.cut,a.harmonic_limit,a.width,a.tiny_log,a.same_j,a.unit_small,a.fast_low,a.anchored,a.conditional,a.physical_spectrum,a.ordered_small,a.selberg_small,a.exact_spectrum,a.signed_prefix)
    print("Q,cut,integer harmonic scale",a.Q,a.cut,a.harmonic_limit,"bulk,actual,inverse,low,dilation,high,tiny,log Y,allowance",*(t.str(13) for t in v))
    if a.lower:assert v[-1]>arb(a.lower)
