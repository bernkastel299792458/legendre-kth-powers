"""Remove a complete short product from the real AFE interference covariance."""
from functools import lru_cache, partial
from inspect import getsource
from math import isqrt
from pathlib import Path
import sys
import numpy as np
from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[2]/"round6"/"phase"))
import smooth_cut
from centered_phase import fourth as previous, means
from mixed_product import mixed_bound
from periodic_fourth import f, period, weighted_disc
from product_energy import bounds


@lru_cache(None)
def arithmetic(q, M, precision):
    assert precision == ctx.prec and 2 <= M <= 30000000
    N = 2*M
    unit = np.resize(np.array(period(q,False), dtype=np.int16), N+1)
    tau = np.zeros(N+1, dtype=np.int32)
    root = isqrt(N)
    for d in range(1,root+1):
        if unit[d]:
            tau[d::d] += 1
    for j in range(1,N//(root+1)+1):
        tau[(root+1)*j::j] += unit[root+1:N//j+1]
    assert 0 <= tau.min() and tau.max() <= 2*isqrt(N)+2 < 2**31
    ramanujan = np.resize(np.array(period(q,True), dtype=np.int64), N+1)
    raw = np.abs(ramanujan*tau)
    assert N*int(raw.max())**2 < 2**63
    dlow = dup = dboth = total = arb(0)
    for L,R in ((1,M),(M+1,N)):
        while L <= R:
            end = min(R,L+L//256)
            terms = raw[L:end+1]
            squares = arb(int(np.dot(terms,terms)))/q
            dboth += squares/L
            if end <= M:
                dlow += squares/end
                dup += squares/L
                total += arb(int(terms.sum()))/arb(q*L).sqrt()
            L = end+1
    return dlow, dup, dboth, total


def reduction(U,q,alpha,width,start,M):
    pi, T = arb.pi(), U.exp()
    moving = M < 0
    delta = arb("0.25") if moving else arb(1)
    scales = [arb(q).sqrt()*a/(2*pi).sqrt() for a in (alpha,1/alpha)]
    smallest = min(scales)*(-width).exp()
    cut = (delta.exp()/smallest)**2
    if moving:
        M = int((T/cut).sqrt().mid().floor().unique_fmpz())
        diagonal,up,twice,B = bounds(q,M,T,cut,start)
    else:
        early = (M*M*cut).max(start)
        assert early < T and delta.exp()>2
        D,up,twice,B = arithmetic(q,M,ctx.prec)
        diagonal = (1-early/T)*D
    norms = []
    for dual,scale in enumerate(scales):
        vals = list(map(abs,period(q,dual)))
        size = scale*width.exp()*T.sqrt()
        raw = 2*arb(sum(vals))/q*size.sqrt()+f(weighted_disc(vals))
        norms.append(raw/(arb(q).sqrt() if dual else 1))
    forward, dual = norms
    close = 8*M*(1+arb(2*M).log())*(up*twice).sqrt()/T
    far = 2*forward*dual*B/(arb(2).log()*T)
    cross_harmonic = 2*forward*dual*B/(delta*T)
    self_close = 4*M*(1+arb(M).log())*up/T
    self_harmonic = B**2/(delta*T)
    gain = 2*diagonal-4*(close+far+cross_harmonic)-2*(self_close+self_harmonic)
    signed = 4*B*(forward**2+dual**2)/(delta*T)
    mean = 4*B/(delta*T)
    return gain,signed,mean


def covariance(U,q,alpha,width,start,s2,v2,m,v,upper,M):
    ordinary = s2+v2+2*((s2-m*m/upper**4).max(0)*v2).sqrt()+2*m*v/U**4
    if not M:
        return ordinary
    gain,signed,mean = reduction(U,q,alpha,width,start,M)
    if not gain>0:
        return ordinary
    var = (s2-m*m/upper**4).max(0)
    residual = (v2-gain/upper**4).max(0)
    revised = s2+v2+2*(var*residual).sqrt()+2*(m*v+signed+m*mean)/U**4
    return ordinary.min(revised)


def finite(U,q,alpha,width,Z,slab,M,covariance_fn=covariance):
    # Reuse all upstream arithmetic and remainder terms; replace one scalar estimate.
    source = getsource(smooth_cut.smooth_fourth)
    old = "fourth=s2+v2+2*(var*v2).sqrt()+2*m*v/U**4"
    new = "fourth=calculate_covariance(U,q,alpha,width,start,s2,v2,m,v,upper)"
    assert source.count(old)==1
    context = dict(vars(smooth_cut),calculate_covariance=partial(covariance_fn,M=M))
    exec(compile(source.replace(old,new),__file__,"exec"),context)
    return context["smooth_fourth"](U,q,alpha,width,Z,paired=True,disjoint=True,
                projective=True,mixed_bound=partial(mixed_bound,projective=True),
                centering=partial(means,slab=slab))


def fourth(U,q=210,alpha=arb(1),width=arb(".04"),Z=384,M=-1,
           slab=arb(1),count=3):
    assert slab>0 and count>=1
    if U > 64:
        return previous(U,q,alpha,width,Z)
    rows = [finite(U+j*slab,q,alpha,width,Z,slab,M) for j in range(count)]
    return max(rows+[previous(U+count*slab,q,alpha,width,Z)])


if __name__=="__main__":
    ctx.prec=160
    for u,ceiling in ((35,".001207338"),(37,".001056038"),(40,".000907721")):
        U=arb(u)
        args=(210,arb(1),arb(".04"),384)
        result=fourth(U,*args)
        assert result<arb(ceiling)
        print("U",u,"old",previous(U,*args).str(12),
              "matched centering",fourth(U,*args,M=0).str(12),
              "fixed product",fourth(U,*args,M=1000000).str(12),
              "moving product",result.str(12),flush=True)
