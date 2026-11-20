"""Build a compact .495 shifted-line source table for the three baseline mollifiers."""
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path

from flint import arb,ctx
from complete_green import fourth_cap
from shift_detector import left


def one(task):
    k,sub,prs,steps=task;ctx.prec=160
    U,V=arb(k)/sub,arb(k+1)/sub
    c4=fourth_cap(U)
    n=2**min(20,max(12,16+int(((U-34)*2/3).lower().floor().unique_fmpz())))
    up=lambda x:int((x*10**20).upper().ceil().unique_fmpz())
    rows=[]
    for _,w,lh in prs:
        if U<34 or U>=42:rows.append([]);continue
        rows.append([up(left(U,V,arb(s),arb(w),arb(lh),2310,n,c4)[0]) for s in steps])
    return k,rows


def build(source,destination,workers=3):
    raw=json.loads(Path(source).read_text(encoding='utf8'))
    scale=raw['norm_scale'];sub=raw['sub'];p_scale=raw['parameter_scale']
    assert scale==10**20 and p_scale==1000 and raw['top_padding']=='.1'
    keys=sorted({r[0] for r in raw['rows']})
    triples=[r[1:4] for r in raw['rows'] if r[0]==keys[0]]
    from decimal import Decimal
    prs=[[str(Decimal(n)/1000) for n in triple] for triple in triples]
    steps=['.005'];out={}
    with ProcessPoolExecutor(max_workers=workers) as pool:
        for k,extra in pool.map(one,[(k,sub,prs,steps) for k in keys]):
            batch=[r for r in raw['rows'] if r[0]==k]
            assert [r[1:4] for r in batch]==triples
            out[k]=dict(moments=[r[4:6] for r in batch],angular_edges=[r[6] for r in batch],left_shifts=extra)
    data=dict(scale=scale,sub=sub,triples=prs,steps=steps,rows=out)
    path=Path(destination)
    if path.exists():assert json.loads(path.read_text(encoding='utf8'))==json.loads(json.dumps(data))
    else:path.write_text(json.dumps(data,separators=(',',':')),encoding='utf8')


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--source',default='phase_norms.json')
    p.add_argument('--destination',default='phase_shift_norms.json');p.add_argument('--workers',type=int,default=3)
    build(**vars(p.parse_args()))
