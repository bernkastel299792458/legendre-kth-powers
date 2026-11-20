"""Displaced Gabriel rows using the balanced endpoint table and physical polygon."""
import argparse
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path

from flint import arb,ctx

from shift_bridge import profile,check
from shift_detector import left
from parallel_profile import SCALE,TRIPLES,upward,fourth_piece,boundary_rows


def build(task):
    k,sub,cap,cutoff,steps=task
    _,normal=boundary_rows((k,sub,cap,cutoff))
    ctx.prec=160
    U,V=arb(k)/sub,arb(k+1)/sub
    if not (34<=U<42):return k,normal,[[] for row in normal]
    exponent=16+int(((U-34)*2/3).lower().floor().unique_fmpz())
    N=2**min(20,max(12,exponent))
    extra=[]
    for parts in TRIPLES:
        _,w,lh=map(arb,parts)
        extra.append([upward(left(U,V,arb(h),w,lh,2310,N,arb(cap)/SCALE)[0]) for h in steps])
    return k,normal,extra


def run(first,last,join,sub,nh,mesh,cutoff,workers,steps,export=None):
    from rational_fourth import fourth as rational
    from balanced_fourth import finite as balanced
    d=(4*(-arb(first)/4).exp()).log1p()
    bottom=min(36,int((arb(".5")/d).log().lower().floor().unique_fmpz()))
    top=46
    assert sub in (4,8,16,32) and 32<=bottom<top
    slabs=range(bottom*sub,top*sub)
    pieces=[(k,k+1,sub) for k in slabs]+[(k*sub,(k+1)*sub,sub) for k in range(top,top+10)]
    end=arb(top+10)
    cap=upward(rational(end).min(balanced(end,210,42,arb("1.06"),arb(".34"),384)))
    with ProcessPoolExecutor(max_workers=workers) as pool:
        local=dict(pool.map(fourth_piece,pieces,chunksize=2))
        uniform={}
        for k,_,_ in reversed(pieces):
            cap=max(cap,local[k]);uniform[k]=cap
        data={}
        for k,center,shifted in pool.map(build,[(k,sub,uniform[k],cutoff,steps)
                                                for k in slabs],chunksize=2):
            data[k]=center,shifted
    names=[tuple(int((100*arb(v)).unique_fmpz()) for v in p) for p in TRIPLES]
    configs=[p[1:] for p in names]
    assert len(set(configs))==len(configs)
    if export is not None:
        saved={}
        for k,(normal,shifted) in data.items():
            U,V=arb(k)/sub,arb(k+1)/sub
            edges=[]
            for _,ws,lhs in TRIPLES:
                edges.append(upward(profile.exact.angular_edge(U,V,arb(ws),arb(lhs),q=2310)))
            saved[k]=dict(uniform_fourth=uniform[k],moments=normal,left_shifts=shifted,
                          angular_edges=edges)
        content=json.dumps(dict(scale=SCALE,sub=sub,cutoff=cutoff,steps=steps,
                                triples=TRIPLES,rows=saved),separators=(",",":"))
        filename=Path(export)
        if filename.exists():
            assert json.loads(filename.read_text(encoding="utf-8"))==json.loads(content)
        else:
            with filename.open("x",encoding="utf-8") as stream:stream.write(content)
    def provider(U,V,d,w,h,core,cells,alpha,base,smooth,q):
        key=tuple(int((100*v).unique_fmpz()) for v in (d,w,h))
        k=int((U*sub).unique_fmpz());assert V*sub==k+1
        assert (core,cells,alpha,base,smooth,q)==(2**20,128,"1",210,"centered",2310)
        return tuple(arb(n)/SCALE for n in data[k][0][names.index(key)])
    def extras(U,V,w,h,keys):
        key=tuple(int((100*v).unique_fmpz()) for v in (w,h))
        k=int((U*sub).unique_fmpz())
        assert V*sub==k+1 and keys==steps
        vals=data[k][1][configs.index(key)]
        if not vals:return []
        return [(arb(s),(arb(a)/SCALE).log()) for s,a in zip(keys,vals,strict=True)]
    return check(first,last,nh,mesh,sub,steps,join,provider,extras)


if __name__=="__main__":
    ctx.prec=160
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--first",default="143.3");ap.add_argument("--last",default="143.88")
    ap.add_argument("--join");ap.add_argument("--sub",type=int,default=16)
    ap.add_argument("--nh",type=int,default=28);ap.add_argument("--mesh",type=int,default=192)
    ap.add_argument("--cutoff",type=int,default=320);ap.add_argument("--workers",type=int,default=4)
    ap.add_argument("--export",help="optional JSON file for the verified vertical and angular bounds")
    ap.add_argument("--shifts",default=".005");ap.add_argument("--diagnose",action="store_true")
    args=vars(ap.parse_args());args["steps"]=tuple(args.pop("shifts").split(","))
    relaxed=args.pop("diagnose")
    val=run(**args);print("displaced full bound",val.str(16),flush=True)
    if not relaxed:assert val<1
