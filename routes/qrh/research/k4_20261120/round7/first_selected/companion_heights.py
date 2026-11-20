"""Price a full mixed Logan spectrum on a common, reproducible cumulative height table."""
import argparse
import json
from fractions import Fraction
from pathlib import Path
from flint import arb,ctx
from near_height import H,A,old_weights,weighted


def build(size,panels,ref='115.402',refined=False,rotating=False,signed_circle=False):
    assert panels>=1 and 0<size<H//2
    scale=10**15
    rows=[]
    for i in range(1,panels+1):
        t=Fraction((size+1280000)*i,panels)
        D=-(-t.numerator//t.denominator)
        if D>150000000000:
            value=weighted(ref,D,'7.5','-2.5','.73',30,2310,ctx.prec)
        else:
            value=old_weights(ref,D,'.73','7.8','-2.65',6)
            if (arb(D)/2).log()>20:
                value=value.min(weighted(ref,D,'7.5','-2.5','.73',30,2310,ctx.prec))
        if refined and (arb(D)/2).log()>20:
            value=value.min(old_weights(ref,D,'.73','7.8','-2.65',6))
            value=value.min(weighted(ref,D,'8','-2.5','.88',30,210,ctx.prec))
        if (rotating or signed_circle) and (arb(D)/2).log()>20:
            from near_rotating import cumulative
            value=value.min(cumulative(ref,D,signed_circle))
        rows.append(int((scale*value.upper()).ceil().unique_fmpz()))
    return dict(size=size,panels=panels,location=ref,scale=scale,rows=rows)


def charge(lo,mix,table,hi=None):
    size=table['size'];n=table['panels'];K=arb(H+size);Q=arb(10000)
    rows=[arb(j)/table['scale'] for j in table['rows']]
    assert n==len(rows)>0 and all(z>0 for z in rows)
    delta=arb(lo)-arb(table['location'])
    transfer=(-delta).max(-delta/8).exp()
    a=mix.a;v=a*size/K
    assert v<arb.pi()/2
    def value(x):
        return (mix.c*(a*x).sin()/a-sum((e*(b*x).sin()/b for b,e in zip(mix.bs,mix.coefficients,strict=True)),arb(0)))*a/a.sin()
    xgrid=[((size-arb(size+1280000)*i/n)/K).max(0) for i in range(n+1)]
    monotone=mix.c*v.cos()>mix.mass
    if not monotone:
        monotone=True
        for i in range(256):
            x=(arb(i)*size/(256*K)).union(arb(i+1)*size/(256*K))
            derivative=mix.c*(a*x).cos()-sum((e*(b*x).cos() for b,e in zip(mix.bs,mix.coefficients,strict=True)),arb(0))
            if not derivative>0:monotone=False;break
    if monotone:
        positive=list(map(value,xgrid[:-1]));negative=[arb(0)]*n
    else:
        positive=[];negative=[]
        curvature=a/a.sin()*(mix.c*a+sum((abs(e)*b for b,e in zip(mix.bs,mix.coefficients,strict=True)),arb(0)))
        for high,low in zip(xgrid,xgrid[1:]):
            step=(high-low)/24
            vals=[value(low+j*step) for j in range(25)]
            correction=curvature*step**2/8
            positive.append((max(x.upper() for x in vals)+correction).upper().max(0))
            negative.append((max((-x).upper() for x in vals)+correction).upper().max(0))
    # Complex Gaussian convolution of a Lipschitz spectrum minus its value at
    # gamma. Its complex multiplier has mean one at every imaginary shift.
    smooth=(1/(16*Q**2)).exp()*2*Q*(mix.c+mix.mass)*a/(K*arb.pi().sqrt()*a.sin())
    priced=[transfer*w for w in rows]
    if 'signed_rows' in table:
        assert Fraction(table['signed_lo'])<=Fraction(lo)<Fraction(hi)<=Fraction(table['signed_hi'])
        ds=arb(lo)-arb(table['signed_lo'])
        signed_transfer=(-ds).max(-ds/8).exp()
        priced=[v.min(signed_transfer*w/table['scale']) for v,w in zip(priced,table['signed_rows'],strict=True)]
    def abel(caps,cost):
        envelope=[v for v in caps]+[arb(0)]
        for i in range(n-1,-1,-1):envelope[i]=envelope[i].max(envelope[i+1])
        return sum(((x-y).max(0)*v for x,y,v in zip(envelope[:-1],envelope[1:],cost,strict=True)),arb(0))
    unsigned=abel([p.max(q) for p,q in zip(positive,negative,strict=True)],[transfer*w for w in rows])
    directional=abel(positive,priced)+abel(negative,priced)
    return 2*(unsigned.min(directional)+smooth*transfer*rows[-1])


if __name__=='__main__':
    ctx.prec=192
    p=argparse.ArgumentParser()
    p.add_argument('--size',type=int,required=True);p.add_argument('--panels',type=int,required=True)
    p.add_argument('--location',default='115.402');p.add_argument('--table',required=True)
    p.add_argument('--refined',action='store_true')
    p.add_argument('--rotating',action='store_true')
    p.add_argument('--signed-circle',action='store_true')
    v=p.parse_args();file=Path(v.table)
    obj=build(v.size,v.panels,v.location,v.refined,v.rotating,v.signed_circle)
    if file.exists():
        assert obj==json.loads(file.read_text(encoding='utf8'))
    else:
        with file.open('x',encoding='utf8') as out:json.dump(obj,out,separators=(',',':'))
    print('verified cumulative mixed-spectrum input',v.size,v.panels,obj['rows'],flush=True)
