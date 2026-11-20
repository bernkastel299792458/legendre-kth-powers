"""A variable positive multiplier in the rational projection of the covariance."""
from functools import partial

from flint import arb, ctx

from grouped_rational import counts, geometry
from interference import covariance, finite, fourth as moving, reduction
from rational_fourth import fourth as rational


def improved(U, q, alpha, width, start, s2, v2, m, v, upper, M, limit, slopes):
    assert M < 0
    prior = covariance(U,q,alpha,width,start,s2,v2,m,v,upper,M)
    gain,signed,h0 = reduction(U,q,alpha,width,start,M)
    vr = v2-gain/upper**4
    sr = s2-m*m/upper**4
    if not gain>0 or not vr>0 or not sr>0:
        return prior
    T = U.exp()
    scale = (upper/U)**4
    g = arb(1)/2+arb("4.2")*(limit**2+1)/T
    bins,ns,sums,bad = counts(q,limit)
    harmonic = [arb(int(n))**2/int(s) if n else arb(0) for n,s in zip(ns,sums)]
    bound = geometry(U,upper-U,q,alpha,width,start)
    entries = [arb(arb(a+b)/2,arb(b-a)/2) for a,b in bins]
    base = arb(".25")+(q*arb(start)/(2*arb.pi())).log()/2
    cutoff = (q*T/(2*arb.pi())).sqrt()*alpha.min(1/alpha)*(-width-arb(".25")).exp()
    M0 = max(1,int(cutoff.lower().floor().unique_fmpz())-1)
    measures = []
    for i,r in enumerate(entries):
        for j in range(i):
            if not ns[i] or not ns[j]:
                continue
            pairs = harmonic[i]*harmonic[j]-arb(int(bad[i,j]))/(bins[i][0]*bins[j][0])
            if not pairs>0:
                continue
            s = entries[j]
            R, root = r/s,(r*s).sqrt()
            w = R.log()
            if not w>0:
                continue
            l,h = bound(r,s)
            early = 2*(2*arb.pi()*R**2/(q*T))*(h0*arb(".25")*T/4)*(R/M0).sqrt()
            short = h0+early
            if base>w:
                short = short.min(h0*arb(".25")/(base-w))
            signal = (l-root*m/(T*w)).lower()
            if signal>0:
                measures.append((signal,(root*(h+short)).upper(),pairs.lower()))
    row = prior
    zero = (vr/sr).sqrt()
    common = s2+v2+2*(m*v+signed+m*h0)/U**4
    for slope in slopes:
        lam = zero*arb(slope)
        assert lam>0
        kappa = scale/lam
        benefit = arb(0)
        for signal,noise,weight in measures:
            net = (signal-kappa*noise).lower()
            if net>0:
                benefit += net**2*weight
        row = row.min(common+lam*sr+vr/lam-lam*benefit/(g*upper**4))
    return row


def fourth(U,q=210,alpha=arb(1),width=arb(".04"),Z=384,limit=65536,
           slopes=("1","1.08","1.16","1.25","1.35","1.45","1.6","1.85","2.2")):
    if U>64:
        return moving(U,q,alpha,width,Z)
    callback = partial(improved,limit=limit,slopes=slopes)
    edge = U
    rows = [rational(U+1,q,alpha,width,Z)]
    for length in map(arb,(".125",".25",".625")):
        rows.append(finite(edge,q,alpha,width,Z,length,-1,callback))
        edge += length
    return max(rows)


if __name__=="__main__":
    ctx.prec=160
    for u,ceiling in ((35,".001140886"),(37,".000989248"),(40,".000842988")):
        result = fourth(arb(u))
        assert result<arb(ceiling)
        print("variational projection",u,result.str(15),flush=True)
