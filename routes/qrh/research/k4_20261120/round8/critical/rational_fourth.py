"""Further remove a finite set of rational frequencies on the S side."""
from functools import partial
from flint import arb,ctx
from interference import covariance, reduction, finite, fourth as moving
from twisted import project, cos_bounds as asymmetric
from stationary import cos_bounds as saddle


def updated(U,q,alpha,width,start,s2,v2,m,v,upper,M,limit,bound_fn):
    assert M<0
    prior=covariance(U,q,alpha,width,start,s2,v2,m,v,upper,M)
    gain,signed,mean=reduction(U,q,alpha,width,start,M)
    if not gain>0:
        return prior
    vr=(v2-gain/upper**4).max(0)
    if not vr>0:
        return prior
    sr=(s2-m*m/upper**4).max(0)
    inc,cost=project(U,upper-U,q,alpha,width,start,m,vr,sr,mean,limit,bound_fn)
    if not inc>0:
        return prior
    row=s2+v2+2*(vr*(sr-inc/upper**4).max(0)).sqrt()
    row+=2*(m*v+signed+m*mean+cost)/U**4
    return prior.min(row)


def fourth(U,q=210,alpha=arb(1),width=arb(".04"),Z=384,limit=512,bound_fn=saddle):
    if U>64:
        return moving(U,q,alpha,width,Z)
    slab=arb(1)
    # The existing bound at U+1 covers the remainder of the half-line.
    row=finite(U,q,alpha,width,Z,slab,-1,partial(updated,limit=limit,bound_fn=bound_fn))
    return row.max(moving(U+slab,q,alpha,width,Z))


if __name__=="__main__":
    ctx.prec=160
    for i,ceiling in ((35,".001178156"), (37,".001027044"), (40,".000879727")):
        U=arb(i)
        result=fourth(U)
        assert result<arb(ceiling)
        print(i,moving(U).str(13),fourth(U,limit=70,bound_fn=asymmetric).str(13),
              result.str(13),flush=True)
