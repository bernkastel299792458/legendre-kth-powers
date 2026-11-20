"""Existing exact bridge, with a tighter right vertical mean for the same f_2310."""
import argparse
import sys
from functools import lru_cache,partial
from types import FunctionType
from flint import arb,ctx
from taper_profile import research
for folder in ("round6/reduction","round6/folds","round5/mean","round5/kernel"):
    sys.path.insert(0,str(research/folder))
import exact_bridge as exact
from fold_mean import source
from short_block import normalized_row
from local_energy import local_right_rows
from finite_anchor import direct_high
from mellin_sharp import low_rows


def right(U,V,d,W,lh,cells,q=2310,refine=4,causal=False,cutoff=100,jordan=False,prime=False):
    # The local polynomial formula applies through the last complete taper cell.
    end=int((lh.exp()*(W.exp()-2)).lower().floor().unique_fmpz())
    cutoff=min(cutoff,end)
    assert cutoff>0
    local_cells=cells
    if causal=="real":cells*=8
    first=min(cells-1,int((cells*U/V).lower().floor().unique_fmpz()))
    low=low_rows(U,V,d,W,lh,q,cells,first,refine,causal,jordan)
    H,rows,tail=local_right_rows(U,d,W,lh,q,cells=local_cells,spacing=210,outer_spacing=q,frequency_cut=cutoff)
    high=direct_high(U,d,W,lh,q)
    y=arb(0)
    for i,m in enumerate(low,first):
        b=rows[i*local_cells//cells]
        e=2*d*(i+1)/(U*cells)
        if e<2*d/V:continue
        y=y.max((-2*d-e*lh).exp()*(H*m+(b+tail*high)*e/(2*d)))
    if prime:
        from prime_slope import saving
        y-=saving(U,V,d,W,lh,cutoff,q)
        if prime=="products":
            from product_slope import saving as composite_saving
            y-=composite_saving(U,V,d,W,lh,cutoff,q)
    assert y>0
    return y


@lru_cache(maxsize=512)
def interference_moment(index,base,precision,method):
    assert precision==ctx.prec
    sys.path.insert(0,str(research/"round8"/"critical"))
    if method=="sweep-table":
        return complete_sweep_table(precision)[index//2]
    if method=="sweep":
        from sweep_boundary import fourth
        return fourth(arb(index)/16,base,arb(".82"),arb(".34"),384)
    if method=="weighted":
        from weighted_boundary import fourth
    elif method=="endpoint":
        from endpoint_fourth import fourth
    elif method=="multiplier":
        from dual_projection import fourth
    elif method=="grouped":
        from grouped_rational import fourth
    elif method=="rational":
        from rational_fourth import fourth
    else:
        from interference import fourth
    return fourth(arb(index)/16,base,arb(1),arb(".04"),384)


@lru_cache(None)
def complete_sweep_table(precision):
    assert ctx.prec==precision
    from sweep_table import table
    return table([arb(j)/8 for j in range(32*8,46*8+1)])


def finite_row(U,V,d,w,lh,core,cells,alpha,base,smooth=False,q=210,*,causal=False,cutoff=100,jordan=False,prime=False,interference=False,adaptive_core=False,fourth_cap=None):
    assert q==2310 and base==210 and core*q<2**32 and smooth and (V-U)<=arb(1)/2
    def residual(u,ww,hh,qq):
        return source(u,ww,hh,qq,base,12)
    def periodic(u):
        k=int((u*10**6).lower().floor().unique_fmpz())
        ordinary=exact.smooth_cached(k,base,ctx.prec,smooth)
        if fourth_cap is not None:
            assert u is U or u>=U
            return ordinary.min(fourth_cap)
        if interference:
            j=int((u*16).lower().floor().unique_fmpz())
            return ordinary.min(interference_moment(j,base,ctx.prec,interference))
        return ordinary
    def left_for(length):
        return normalized_row(U,V,q,length,w,lh,residual,fourth_fn=periodic,
                              sieve_base=base,small_factor=arb(1)/12)[0]
    left=left_for(core)
    if adaptive_core:
        exponent=16+int(((U-34)*2/3).lower().floor().unique_fmpz())
        short=2**min(20,max(12,exponent))
        if short<core:left=left.min(left_for(short))
    return left,right(U,V,d,w,lh,cells,q,causal=causal,cutoff=cutoff,jordan=jordan,prime=prime)


PARAM="1.1,9.5,-3;1.28,9.5,-2.75;1.34,8.5,-2.75;1.16,9,-3;1.04,9.5,-3.5;1.1,9,-2.75;1.16,10,-3"
if __name__=="__main__":
    ctx.prec=160
    cli=argparse.ArgumentParser()
    cli.add_argument("--first",default="146.7");cli.add_argument("--last",default="147.21")
    cli.add_argument("--param",default=PARAM);cli.add_argument("--cells",type=int,default=128)
    cli.add_argument("--nheight",type=int,default=80);cli.add_argument("--mesh",type=int,default=96)
    cli.add_argument("--old",action="store_true");cli.add_argument("--diagnose",action="store_true")
    cli.add_argument("--causal",action="store_true")
    cli.add_argument("--real",action="store_true")
    args=cli.parse_args()
    # Run the unaltered bridge bytecode with only the row provider replaced.
    code=exact.test
    row=partial(finite_row,causal="real" if args.real else args.causal)
    run=code if args.old else FunctionType(code.__code__,dict(code.__globals__,finite_row=row),
                                          code.__name__,code.__defaults__,code.__closure__)
    z=run(args.first,args.last,args.param,args.nheight,args.mesh,2,args.cells,
          2**20,"1",2,210,"centered",2310,hi=46,interpolate=True)
    if not args.diagnose:assert z<1
