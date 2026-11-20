"""Recompute independent ordinate slabs and join their outward-rounded row bounds."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import sys
from flint import arb,ctx
import height_profile as profile

SCALE=10**20
TRIPLES=tuple(tuple(p.split(",")) for p in profile.mellin_bridge.PARAM.split(";"))
sys.path.insert(0,str(profile.research/"round8"/"critical"))


def upward(value):
    return int((value*SCALE).upper().ceil().unique_fmpz())


def fourth_piece(task):
    from balanced_fourth import finite as balanced
    from sweep_boundary import finite as sweep
    ctx.prec=160
    k,end,den=task
    U=arb(k)/den
    width=arb(end-k)/den
    first=sweep(U,210,arb(".82"),arb(".34"),384,width,65536)
    second=balanced(U,210,42,arb("1.06"),arb(".34"),384,width,65536)
    return k,upward(first.min(second))


def boundary_rows(task):
    ctx.prec=160
    k,sub,cap,cutoff=task[:4]
    products=len(task)>4 and task[4]
    U,V=arb(k)/sub,arb(k+1)/sub
    result=[]
    for parts in TRIPLES:
        d,w,h=map(arb,parts)
        pair=profile.mellin_bridge.finite_row(U,V,d,w,h,2**20,128,"1",210,"centered",2310,
                                   causal="real",cutoff=cutoff,jordan="second",prime="products" if products else True,
                                   adaptive_core=True,fourth_cap=arb(cap)/SCALE)
        result.append(tuple(map(upward,pair)))
    return k,result


def run(first,last,join,sub,nh,mesh,cutoff,workers,products=False):
    from balanced_fourth import finite as balanced
    from rational_fourth import fourth as rational
    d=(4*(-arb(first)/4).exp()).log1p()
    bottom=min(36,int((arb(".5")/d).log().lower().floor().unique_fmpz()))
    top=46
    assert sub in (4,8,16,32) and 32<=bottom<top
    slabs=range(bottom*sub,top*sub)
    pieces=[(k,k+1,sub) for k in slabs]+[(k*sub,(k+1)*sub,sub) for k in range(top,top+10)]
    tail=arb(top+10)
    cap=upward(rational(tail).min(balanced(tail,210,42,arb("1.06"),arb(".34"),384)))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        local=dict(pool.map(fourth_piece,pieces,chunksize=2))
        uniform={}
        for k,_,_ in reversed(pieces):
            cap=max(cap,local[k])
            uniform[k]=cap
        tasks=[(k,sub,uniform[k],cutoff,products) for k in slabs]
        rows=dict(pool.map(boundary_rows,tasks,chunksize=3))
    names=[tuple(int((100*arb(v)).unique_fmpz()) for v in p) for p in TRIPLES]
    def provider(U,V,d,w,h,core,cells,alpha,base,smooth,q):
        k=int((U*sub).unique_fmpz())
        assert k in rows and (sub*V-(k+1)).is_zero()
        assert (core,cells,alpha,base,smooth,q)==(2**20,128,"1",210,"centered",2310)
        key=tuple(int((100*v).unique_fmpz()) for v in (d,w,h))
        return tuple(arb(n)/SCALE for n in rows[k][names.index(key)])
    return profile.bound(first,last,nh,mesh,True,True,sub,cutoff,join=join,row_provider=provider)


if __name__=="__main__":
    ctx.prec=160
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--first",required=True);ap.add_argument("--last",required=True)
    ap.add_argument("--join");ap.add_argument("--sub",type=int,default=16)
    ap.add_argument("--nh",type=int,default=32);ap.add_argument("--mesh",type=int,default=192)
    ap.add_argument("--cutoff",type=int,default=320);ap.add_argument("--workers",type=int,default=4)
    ap.add_argument("--products",action="store_true")
    args=ap.parse_args()
    result=run(**vars(args))
    assert result<1
