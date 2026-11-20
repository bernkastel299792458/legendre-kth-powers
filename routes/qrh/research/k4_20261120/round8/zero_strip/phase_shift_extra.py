"""Recompute further left displacements from a previously certified fourth-moment table."""
from concurrent.futures import ProcessPoolExecutor
import json
from pathlib import Path

from flint import arb,ctx
from complete_green import fourth_cap  # initialize the original research module paths
from shift_detector import left


def extend(task):
    k,sub,scale,c4,triples,steps=task
    ctx.prec=160;u,v=arb(k)/sub,arb(k+1)/sub
    n=2**min(20,max(12,16+int(((u-34)*2/3).lower().floor().unique_fmpz())))
    values=[]
    for _,w,lh in triples:
        vals=[left(u,v,arb(h),arb(w),arb(lh),2310,n,arb(c4)/scale)[0] for h in steps]
        values.append([int((a*scale).upper().ceil().unique_fmpz()) for a in vals])
    return k,values


def build(source,destination,steps,workers):
    data=json.loads(Path(source).read_text(encoding='utf8'));sub=data['sub'];scale=data['scale']
    keys=[int(k) for k in data['rows'] if 34*sub<=int(k)<42*sub]
    extra=steps.split(',')
    assert not(set(extra)&set(data['steps'])) and len(extra)==len(set(extra))
    tasks=[(k,sub,scale,data['rows'][str(k)]['uniform_fourth'],data['triples'],extra) for k in keys]
    if workers==1:
        results=map(extend,tasks)
    else:
        with ProcessPoolExecutor(max_workers=workers) as pool:
            results=list(pool.map(extend,tasks,chunksize=2))
    for k,rows in results:
        old=data['rows'][str(k)]['left_shifts']
        for a,b in zip(old,rows,strict=True):
            assert len(a)==len(data['steps']);a.extend(b)
    data['steps'].extend(extra)
    path=Path(destination)
    if path.exists():assert json.loads(path.read_text(encoding='utf8'))==data
    else:
        with path.open('x',encoding='utf8') as f:json.dump(data,f,separators=(',',':'))


if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--source',default='../critical/shift_rows_16.json')
    p.add_argument('--destination',default='phase_shift_extra.json');p.add_argument('--workers',type=int,default=4)
    p.add_argument('--steps',default='.016,.020,.026')
    build(**vars(p.parse_args()))
