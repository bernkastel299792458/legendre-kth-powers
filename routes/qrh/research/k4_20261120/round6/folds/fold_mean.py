"""Short-window second moments for the polynomial paired with zeta times E_base."""
from fractions import Fraction
from functools import lru_cache
from math import ceil, gcd, prod
from pathlib import Path
import sys

import numpy as np
from flint import arb, ctx

research=Path(__file__).resolve().parents[2]
for path in (research/"round4"/"hilbert",research/"round5"/"spectrum",
             research/"round5"/"left",research/"round6"/"phase"):
    sys.path.insert(0,str(path))
from critical_mean import critical_mean
from linear_mean import certify_fold,as_arb
from periodic_fourth import fourth
from short_block import normalized_row


@lru_cache(maxsize=None)
def gram(modulus,count,precision):
    """Rigorous upper bound for a segment of count consecutive Fourier rows."""
    assert precision==ctx.prec and modulus%6==0 and 2310%modulus==0 and count>0
    primes=[p for p in (2,3,5,7,11) if modulus%p==0]
    assert prod(primes)==modulus
    period=modulus//2
    cycles,k=divmod(count,period)
    if not k:
        return arb(cycles*period)
    phi=prod(p-1 for p in primes)
    if k==1:
        return arb(cycles*period+phi)
    vals=[prod(p-1 if h%p==0 else -1 for p in primes) for h in range(k)]
    entries=[[vals[abs(i-j)] for j in range(k)] for i in range(k)]
    eig=float(np.linalg.eigvalsh(entries)[-1])
    cap=min(k*phi,period)
    numerator=ceil(eig*10**7)+2
    if numerator<cap*10**7:
        hi=arb(numerator)/10**7
        rows=[[-arb(t) for t in es[:i]]+[hi-phi] for i,es in enumerate(entries)]
        for j in range(k):
            pivot=rows[j][j]
            assert pivot>0
            for i in range(j+1,k):
                factor=rows[i][j]/pivot
                for l in range(j+1,i+1):
                    rows[i][l]-=factor*rows[l][j]
        return cycles*period+hi
    return arb(cycles*period+cap)


def partial_folds(depth):
    assert 1<=depth<=32
    def evaluate(base,B,rs,v,tau,order,ybar,eps,width,corr,U,X,pieces,
                 harmonic,energy,rho,harmonic_offset):
        small=base*v*tau*(1+eps)/arb.pi()
        end=B*X
        ratios=sorted({Fraction(a,j) for a in rs for j in range(1,depth+1)
                      if small*as_arb(Fraction(a,j))<end})
        assert ratios and ratios[0]==Fraction(1,depth)
        _,defect=certify_fold(base,"unit")
        affine=arb.pi()*as_arb(defect)/base
        overlap=width.exp()
        cut=small*as_arb(ratios[0])*overlap
        near=ybar*harmonic(cut)
        bands=affine*sum(energy(arb(0),cut,r) for r in rs)
        for index,ratio in enumerate(ratios):
            lo=small*as_arb(ratio)
            hi=small*as_arb(ratios[index+1]) if index+1<len(ratios) else end
            groups=[]
            for a in rs:
                j=ceil(a/ratio)
                if j<=depth:
                    groups.append((base*a,[(gram(base*a//g,j,ctx.prec),[r for r in rs if gcd(a,r)==g])
                                           for g in sorted({gcd(a,r) for r in rs})]))
            assert groups
            divisions=max(1,int(float(pieces*(hi/lo).log()/(end/small*depth).log()))+1)
            step=(hi/lo)**(arb(1)/divisions)
            for i in range(divisions):
                l=lo*step**i
                h=lo*step**(i+1) if i+1<divisions else hi
                es={r:energy(l,h*overlap,r) for r in rs}
                best=None
                for mod,row in groups:
                    cost=arb.pi()/mod*sum((cap*sum(es[r] for r in members)).sqrt()
                                            for cap,members in row)**2
                    best=cost if best is None else best.min(cost)
                bands+=best
        full=sum(arb(1)/r for r in rs)*(rho+harmonic_offset.max(arb(0))/U)
        tail=affine*sum(energy(arb(0),end,r) for r in rs)
        return corr*((1+eps)*(near+ybar*tau**(1-order)*full)+(bands+tau**(-order)*tail)/U)
    return evaluate


def source(U,W,lh,q,base,depth):
    near=arb("1.01")*2048/2047*(1-arb("1.03")**(-2047))
    return critical_mean(U,W,lh,q=q,base=base,fold=partial_folds(depth)),near


@lru_cache(maxsize=1024)
def moment(index,base,alpha,precision,method="sharp"):
    assert precision==ctx.prec
    if method=="disjoint":
        from shifted_harmonic import disjoint_fourth
        return disjoint_fourth(arb(index)/1000000,base,as_arb(alpha),arb(".06"),384)
    if method=="projected":
        from mixed_product import projected_fourth
        return projected_fourth(arb(index)/1000000,base,as_arb(alpha),arb(".04"),384)
    if method=="centered":
        from centered_phase import fourth as centered_fourth
        return centered_fourth(arb(index)/1000000,base,as_arb(alpha),arb(".04"),384)
    if method in ("smoothed","paired"):
        from smooth_cut import smooth_fourth
        return smooth_fourth(arb(index)/1000000,base,as_arb(alpha),arb(".06"),384,paired=method=="paired")
    assert method=="sharp"
    return fourth(arb(index)/1000000,base,as_arb(alpha),96)


def joint(U,V,W,lh,q=210,ncore=2097152,base=30,depth=12,alpha=Fraction(3,2),method="sharp"):
    def cm(u,w,l,mod):
        return source(u,w,l,mod,base,depth)
    def m4(u):
        i=int((u*1000000).lower().floor().unique_fmpz())
        return moment(i,base,alpha,ctx.prec,method)
    return normalized_row(U,V,q,ncore,W,lh,cm,fourth_fn=m4,sieve_base=base,
                          small_factor=arb(1)/depth)


if __name__=="__main__":
    import argparse
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--u",default="40")
    cli.add_argument("--base",type=int,default=30)
    cli.add_argument("--depth",type=int,default=12)
    cli.add_argument("--core",type=int,default=32768)
    cli.add_argument("--alpha",default="3/2")
    args=cli.parse_args()
    ctx.prec=160
    u,w,lh=map(arb,(args.u,"9.5","-3.5"))
    print("residual polynomial mean",source(u,w,lh,210,args.base,args.depth)[0].str(16),flush=True)
    row=joint(u,u+1,w,lh,ncore=args.core,base=args.base,depth=args.depth,alpha=Fraction(args.alpha))
    print("joint left row, unsplit comparator, short coefficient",*[v.str(16) for v in row],flush=True)
