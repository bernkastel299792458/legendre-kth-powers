"""Store real-part hinges for true intervals (H,T], retaining the physical L dependence."""
import argparse
import json
from pathlib import Path
import sys
from flint import arb,ctx
from near_phase import H,RESEARCH,rv_count,angular_edge,chord_bounds,weights,dot
from near_height import left,right
sys.path.insert(0,str(RESEARCH/'round8'/'zero_strip'))
from rotating_signed import signed_price


def build(offsets,fourth,precision):
    assert precision==ctx.prec
    caps=json.loads(Path(fourth).read_text(encoding='utf8'))
    scale=10**10
    def ceil(x):return int((scale*x.upper()).ceil().unique_fmpz())
    labels=list(range(650,875,2))+[875];nodes=[arb(i)/1000 for i in labels]
    result=[]
    for cut in offsets:
        size=cut+1
        R=arb(size)/2;C=H+R;U=R.log()
        assert U>20 and C-arb('1.04')*R>1000
        assert (1+arb('1e-6'))*(1+((1+2/R)/arb('1.01'))**2048)*(1+1/(arb(H)-1))-1<arb('2e-6')
        B=C+arb('1.01')*R
        index=int((B.log()*caps['den']).lower().floor().unique_fmpz())
        c4=(caps['rows'][str(index)],caps['scale']) if str(index) in caps['rows'] else None
        bounds=None
        for ds,ws,hs,q,base in (('.88','8','-2.5',210,30),('1.1','8.5','-2.25',2310,210),
                                ('1.16','9','-2.75',2310,210)):
            d,w,h=map(arb,(ds,ws,hs))
            V=U.max(25).max(((H+3*R+4)/4).log())
            assert q*(U+w+h).exp()<(3*V).exp() and H+3*R+3<4*V.exp()
            l=left(H,size,ws,hs,base,'1' if base==210 else '1.5',32768,ctx.prec,q,
                   c4 if base==210 else None)
            r=U*right(U,U,d,w,h,64,q,causal='real',cutoff=95)
            edge=9*angular_edge(U,U,w,h,height_top=arb(H+size),length_factor=2,q=q)/8
            row=[signed_price(U,arb(1)/2,d,2*l/(U**2*R),2*r/U,s,V=V)[0]+edge for s in nodes[:-1]]
            bounds=row if bounds is None else [a.min(b) for a,b in zip(bounds,row,strict=True)]
        hinges=chord_bounds(nodes,bounds+[arb(0)])[:-1]
        result.append(dict(cut=cut,hinges=list(map(ceil,hinges)),count=ceil(rv_count(arb(size)))))
        print('translated physical hinge row',cut,'central fourth',c4,flush=True)
    return dict(scale=scale,nodes=labels,ordrows=result,omitted=ceil(rv_count(arb('.1'))))


def prices(data,lo):
    l=arb(lo);nodes=[arb(k)/1000 for k in data['nodes']]
    w=weights([nodes],l);s=data['scale']
    assert all(v>0 for v in w) and nodes[-1]==arb(7)/8
    extra=(-l/8).exp()*data['omitted']
    return [(arb(H+r['cut']),(w[0]*r['count']+dot(w[1:],[arb(v) for v in r['hinges']])+extra)/s)
            for r in data['ordrows']]


if __name__=='__main__':
    ctx.prec=160
    p=argparse.ArgumentParser()
    p.add_argument('--offsets',required=True,help='comma-separated offsets in billions of ordinates')
    p.add_argument('--fourth',default=str(RESEARCH/'round8'/'zero_strip'/'early_uniform_fourth.json'))
    p.add_argument('--out',required=True)
    v=p.parse_args();cuts=[10**9*int(x) for x in v.offsets.split(',')]
    assert cuts==sorted(set(cuts)) and cuts[0]>0
    data=build(cuts,v.fourth,ctx.prec)
    path=Path(v.out)
    if path.exists():assert json.loads(path.read_text(encoding='utf8'))==data
    else:
        with path.open('x',encoding='utf8') as f:json.dump(data,f,separators=(',',':'))
    print('physical L=118 prices',[(str(t),v.str(9)) for t,v in prices(data,'118')],flush=True)
