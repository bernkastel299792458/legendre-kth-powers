"""Individual sharp fourth branches when Euler factors use both orientations."""
from functools import lru_cache
from inspect import getsource
from math import factorial,gcd,prod

import numpy as np
from flint import acb,arb,arb_poly,ctx
from scipy.linalg import eigvalsh

from interference import smooth_cut
from periodic_fourth import diagonal,period,weighted_disc,harmonic,f
from weighted_boundary import mixtures
from periodic_hilbert import positive_schur_pivots


@lru_cache(None)
def seq(q,unit,ram,mask=1):
    assert unit*ram==q and gcd(unit,ram)==1 and ram%mask==0
    c=period(ram,True)
    return tuple(c[n%ram] if gcd(n,unit*mask)==1 else 0 for n in range(q))


@lru_cache(None)
def forms(q,unit,ram,mask=1):
    vals=seq(q,unit,ram,mask)
    # The dual loops retain all coprime gcd categories; zero categories disappear.
    diag_env=dict(diagonal.__wrapped__.__globals__,period=lambda q,dual: vals)
    exec(compile(getsource(diagonal),__file__,"exec"),diag_env)
    ep_env=dict(vars(smooth_cut),period=lambda q,dual: vals)
    exec(compile(getsource(smooth_cut.cutoff_coefficients),__file__,"exec"),ep_env)
    exec(compile(getsource(smooth_cut.endpoint_norm),__file__,"exec"),ep_env)
    return diag_env["diagonal"],ep_env["endpoint_norm"]


@lru_cache(None)
def data(q,unit,ram,prec):
    assert prec==ctx.prec
    vals=seq(q,unit,ram)
    sq=tuple(v*v for v in vals)
    mean,head,err=harmonic(sq,prec)
    ab=tuple(map(abs,vals))
    return (mean/ram,head/ram,err/ram,arb(max(sq))/ram,
            arb(sum(ab))/(q*arb(ram).sqrt()),f(weighted_disc(ab))/arb(ram).sqrt())


@lru_cache(None)
def weights(q,unit,ram,prec):
    assert prec==ctx.prec
    wp={2:"1.625",3:"3.75",5:"10.5",7:"18",11:"35"}
    best=None
    moduli=[q] if q<=210 else [m for m in range(2,386) if q%m==0]
    for mod in moduli:
        ps=tuple(p for p in wp if gcd(ram,mod)%p==0)
        ws=tuple(arb(wp[p]) for p in ps)
        residues=[r for r in range(mod) if gcd(r,gcd(unit,mod))==1]
        if len(residues)>210:continue
        W=[prod(ws[j] for j,p in enumerate(ps) if r%p==0) for r in residues]
        ar=np.array(residues)
        diff=np.subtract.outer(ar,ar)
        np.fill_diagonal(diff,1)
        H=1j/np.sin(np.pi*diff/mod)
        np.fill_diagonal(H,1.)
        root=np.sqrt(np.array(list(map(float,W))))
        head=eigvalsh(root[:,None]*H*root,subset_by_index=(len(ar)-1,len(ar)-1))[0]
        est=np.pi/mod*head
        score=est*prod(1/float(w)+(1-1/float(w))/p**2 for p,w in zip(ps,ws))
        if best is None or score<best[0]:best=score,est,mod,ps,ws,residues,W
    _,est,mod,ps,ws,residues,W=best
    ceiling=arb(int(np.ceil(est*10000))+1)/10000
    rows=[]
    for j,r in enumerate(residues):
        row=[acb(0,-1/(arb.pi()*(r-s)/mod).sin()) for s in residues[:j]]
        rows.append(row+[acb(mod*ceiling/(arb.pi()*W[j])-1)])
    positive_schur_pivots(rows)
    return ceiling,tuple(mixtures(ps,ws))


def upper(q,unit,ram,U,alpha,width,Z,start):
    pi=arb.pi();K=max(q if q>210 else 2*q,192)
    Yscale=arb(q).sqrt()*alpha*width.exp()
    ell=(arb_poly([0,1])-(2*pi).log())*(arb(1)/2)+Yscale.log()
    Y0=Yscale*(U/2).exp()/(2*pi).sqrt()
    eta=(-2*width).exp()
    v=seq(q,unit,ram)
    M=max(map(abs,v))
    density=arb(sum(map(abs,v)))/q
    disc=f(weighted_disc(tuple(map(abs,v))))
    gap=smooth_cut.reciprocal_gap(ctx.prec)
    coeff,parts=weights(q,unit,ram,ctx.prec)
    def boundary(ymin):
        gram=0
        for mask,weight in parts:
            gram+=weight*forms(q,unit,ram,mask)[1](ell,ymin,q,True,K)
        return coeff*gram+16*gap*(density+disc/(2*ymin.sqrt()))**4
    b=arb(K*(K+1)+10)
    te=2*pi*(b/(eta*Yscale))**2
    assert te<U.exp()
    small=M**4*(2*pi*(1+(b/eta).log())+16*gap)*te/U.exp()
    lower=(1+eta**2)/(4*width)*(boundary(b)+small)
    top=(1-eta**2)/(4*width)*boundary(eta*Y0)
    off=(lower+top)*(Yscale**2/(2*pi))
    D=forms(q,unit,ram)[0](q,True,Z,ctx.prec)
    base=D(ell)
    for j in range(1,5):
        D=D.derivative()
        base+=D(ell)*((-2*width)**j/factorial(j+1))
    cut=2*pi*Z**4/Yscale**2*(4*width).exp()
    assert start<cut<U.exp()
    raw=M**4*(1+2*arb(Z).log()+2*width)**4
    early=(raw+sum(abs(x)*cut.log()**j for j,x in enumerate(base.coeffs())))*cut/U.exp()
    anti=base
    d=base
    for j in range(1,5):
        d=d.derivative()
        anti+=(-1)**j*d
    early+=(-start*anti(arb(start).log())).max(0)/U.exp()
    P=(anti+early+off)*(arb(1)/ram**2)
    return sum(P[j].max(0)*U**(j-4) for j in range(5))


if __name__=="__main__":
    ctx.prec=128
    U=arb(37);q=210
    for unit in (210,105,70,42,30,35,21,15,14,10,7,6,5,3,2,1):
        ram=q//unit
        c=upper(q,unit,ram,U,arb(1),arb(".34"),384,10000)
        print(unit,ram,"normalized branch",c.str(10),flush=True)
