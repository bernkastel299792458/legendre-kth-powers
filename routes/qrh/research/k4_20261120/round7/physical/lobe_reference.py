"""A common positive Selberg error majorant for a family of physical lobes."""
import argparse
import json
from pathlib import Path
from fractions import Fraction
from functools import partial
from flint import arb,ctx
from bilinear import rational
from odd_sieve import denominator
from direct_partition import grouped,H


def build(lo,hi,size,modulus,ratio,secondary_ratio,inside,linear=False):
    l,h=map(arb,(lo,hi));K=arb(H+size)
    assert 115<l<h<116 and modulus in (2,6,30,210)
    cmax=h+(4*(-l/4).exp()).log1p()/2
    rem=partial(grouped.remainder,modulus=modulus,exact_harmonics=True,sparse=3)
    rows=[];quant=10**16
    # Prototype variation and area per unit cap. Each induces a separately
    # valid majorant, without requiring it to be realized by any spatial lobe.
    for sel,width,osc,area in ((ratio,inside,'1.0','1.245'),(secondary_ratio,None,'2.60','1.85')):
        z=rational(Fraction(sel))*((l-K.log())/2).exp();G=denominator(z,modulus)
        interior=None if width is None else arb(width)
        area0=arb(area)+(interior/2 if interior is not None else 0)
        cost,_=rem(l,cmax,K,z,G,2**48,arb(1),arb(osc),area0,interior is None,True,
                   inside=interior,poisson=True,linear=linear)
        def rounded(v):return int((quant*K*(-l).exp()*z**2*v).upper().ceil().unique_fmpz())
        row=dict(ratio=sel,inside=width,variation=osc,area=area)
        if linear:row['tangent']=[rounded(v) for v in cost]
        else:row['price']=rounded(cost)
        rows.append(row)
    return dict(lo=lo,hi=hi,size=size,modulus=modulus,scale=quant,rows=rows)


def transfer(table,l,h,size,modulus,sel,area,cap,osc,width):
    low,high=arb(table['lo']),arb(table['hi'])
    assert (low<=l or low.overlaps(l)) and (high>=h or high.overlaps(h))
    assert size==table['size'] and modulus==table['modulus']
    row=table['rows'][width is None]
    assert Fraction(row['ratio'])==Fraction(sel)
    assert (width is None and row['inside'] is None) or abs(arb(row['inside'])-width)<arb('1e-40')
    G=denominator(rational(Fraction(sel))*((low-arb(H+size).log())/2).exp(),modulus)
    ref_area=arb(row['area'])+(width/2 if width is not None else 0)
    components=cap,osc/arb(row['variation']),area/ref_area
    if 'tangent' in row:
        price=sum((v*a for v,a in zip(components,row['tangent'],strict=True)),arb(0))
    else:
        price=components[0].max(components[1]).max(components[2])*row['price']
    return G, (low-l).exp()*price/table['scale']


if __name__=='__main__':
    ctx.prec=192
    p=argparse.ArgumentParser()
    p.add_argument('--lo',default='115.400');p.add_argument('--hi',default='115.455')
    p.add_argument('--size',type=int,required=True);p.add_argument('--modulus',type=int,default=30)
    p.add_argument('--ratio',default='145');p.add_argument('--secondary-ratio',default='146')
    p.add_argument('--inside',default='.0016');p.add_argument('--table',required=True)
    p.add_argument('--linear',action='store_true')
    args=vars(p.parse_args());file=Path(args.pop('table'));obj=build(**args)
    if file.exists():assert obj==json.loads(file.read_text(encoding='utf8'))
    else:
        with file.open('x',encoding='utf8') as out:json.dump(obj,out,separators=(',',':'))
    print('verified common sieve prices',obj,flush=True)
