"""Integer Hilbert endpoint with positive weights on divisibility classes."""
from functools import lru_cache,partial
from inspect import getsource
from itertools import combinations
from math import gcd,prod

from flint import acb,arb,ctx

from endpoint_fourth import fourth as upper,norm
from interference import smooth_cut
from periodic_hilbert import positive_schur_pivots


@lru_cache(None)
def restricted(mask):
    def sequence(q,dual):
        assert q%mask==0 and dual
        values=smooth_cut.period(q,dual)
        return [v if gcd(j,mask)==1 else 0 for j,v in enumerate(values)]
    context=dict(vars(smooth_cut),period=sequence)
    exec(compile(getsource(smooth_cut.cutoff_coefficients),__file__,"exec"),context)
    exec(compile(getsource(smooth_cut.endpoint_norm),__file__,"exec"),context)
    return context["endpoint_norm"]


def mixtures(primes,weights):
    for k in range(len(primes)+1):
        for subset in combinations(range(len(primes)),k):
            mask=prod(primes[j] for j in subset)
            co=prod(1-1/weights[j] if j in subset else 1/weights[j]
                    for j in range(len(primes)))
            yield mask,co


def spectral(primes,weights,target):
    mod=prod(primes)
    assert all(w>=1 for w in weights)
    W=[prod(weights[j] for j,p in enumerate(primes) if i%p==0) for i in range(mod)]
    # Certify (mod*target/pi)D^{-2} - I - iC > 0 by congruence.
    scaled=mod*target/arb.pi()
    rows=[]
    for r in range(mod):
        row=[acb(0,-1/(arb.pi()*(r-s)/mod).sin()) for s in range(r)]
        rows.append(row+[acb(scaled/W[r]-1)])
    positive_schur_pivots(rows)
    return target


@lru_cache(None)
def constant(primes,weight_tuple,target,prec):
    assert prec==ctx.prec
    return spectral(primes,tuple(map(arb,weight_tuple)),arb(target))


def candidate(q,dual,ell,Y0,primes,weight_tuple,target):
    K=max(2*q,192)
    if not dual:
        return norm(q,ctx.prec)*smooth_cut.endpoint_norm(ell,Y0,q,dual,K)
    assert q%prod(primes)==0
    weights=tuple(map(arb,weight_tuple))
    terms=0
    for mask,co in mixtures(primes,weights):
        if mask==1:
            terms+=co*smooth_cut.endpoint_norm(ell,Y0,q,True,K)
        else:
            terms+=co*restricted(mask)(ell,Y0,q,True,K)
    return constant(primes,weight_tuple,target,ctx.prec)*terms


def fourth(U,q=210,alpha=arb(1),width=arb(".04"),Z=384,limit=65536):
    if q!=210:
        return upper(U,q,alpha,width,Z,limit)
    fn=partial(candidate,primes=(2,3,5,7),weight_tuple=("1.625","3.75","10.5","18"),
               target="117.354")
    return upper(U,q,alpha,width,Z,limit,fn)


if __name__=="__main__":
    ctx.prec=160
    for u,ceiling in ((35,".000991964"),(37,".000869330"),(40,".000750741")):
        value=fourth(arb(u))
        assert value<arb(ceiling)
        print("weighted upper endpoint",u,value.str(15),flush=True)
