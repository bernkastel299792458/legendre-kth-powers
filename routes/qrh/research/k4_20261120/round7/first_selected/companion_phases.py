"""Upper bounds for the positive physical cosine on each mixed Logan height row."""
import argparse
from fractions import Fraction
from pathlib import Path
import json
from flint import arb,ctx
from near_phase import cumulative


def build(scalar,lo,hi,original=False):
    size,n,scale=scalar['size'],scalar['panels'],scalar['scale']
    rows=[]
    for j in range(1,n+1):
        t=Fraction((size+1280000)*j,n);D=-(-t.numerator//t.denominator)
        bound=arb(scalar['rows'][j-1])/scale
        delta=arb(lo)-arb(scalar['location'])
        bound*=(-delta).max(-delta/8).exp()
        if (arb(D)/2).log()>20:
            base,q=(6,210) if original else (30,2310)
            _,signed=cumulative(lo,hi,D,base,q,spacing=3,count=14,free=True,original=original)
            bound=bound.min(signed)
        upper=int((scale*bound.upper()).ceil().unique_fmpz())
        rows.append(upper)
        print('signed physical row',D,upper,'scalar',scalar['rows'][j-1],flush=True)
    return dict(scalar,signed_rows=rows,signed_lo=lo,signed_hi=hi)


if __name__=='__main__':
    ctx.prec=192
    p=argparse.ArgumentParser();p.add_argument('--scalar',required=True);p.add_argument('--table',required=True)
    p.add_argument('--lo',default='115.400');p.add_argument('--hi',default='115.455')
    p.add_argument('--original',action='store_true')
    a=p.parse_args();out=build(json.loads(Path(a.scalar).read_text(encoding='utf8')),a.lo,a.hi,a.original)
    file=Path(a.table)
    if file.exists():assert json.loads(file.read_text(encoding='utf8'))==out
    else:
        with file.open('x',encoding='utf8') as f:json.dump(out,f,separators=(',',':'))
