"""Extend the physical Gabriel table below its earliest full height slab."""
import argparse
import json
from pathlib import Path
from flint import arb,ctx
from complete_green import mb,angular_edge


def block(k,den,triples,scale,core):
    U,V=arb(k)/den,arb(k+1)/den
    assert 28<U<V and V-U<=arb(1)/2
    moments=[];edges=[]
    def ceil(x):return int((scale*x.upper()).ceil().unique_fmpz())
    for pars in triples:
        d,w,lh=map(arb,pars)
        a,b=mb.finite_row(U,V,d,w,lh,core,64,'1',210,'centered',2310,
                          causal='real',cutoff=95,jordan='second' if U+lh>=26 else False,
                          adaptive_core=True)
        moments.append([ceil(a),ceil(b)])
        edges.append(ceil(angular_edge(U,V,w,lh,q=2310)))
    return dict(moments=moments,left_shifts=[[] for _ in moments],angular_edges=edges)


def build(source,destination,lo,den,core):
    data=json.loads(Path(source).read_text(encoding='utf8'))
    sub=data['sub'];start=min(map(int,data['rows']))
    assert sub%den==0 and start%sub==0 and lo<start//sub
    for k in range(lo*den,start*den//sub):
        row=block(k,den,data['triples'],data['scale'],core)
        print('early height source',k,den,row['moments'][0],flush=True)
        for i in range(k*sub//den,(k+1)*sub//den):
            assert str(i) not in data['rows']
            data['rows'][str(i)]=row
    path=Path(destination)
    if path.exists():assert json.loads(path.read_text(encoding='utf8'))==data
    else:
        with path.open('x',encoding='utf8') as out:json.dump(data,out,separators=(',',':'))


if __name__=='__main__':
    ctx.prec=160
    p=argparse.ArgumentParser()
    here=Path(__file__).resolve().parent
    p.add_argument('--source',default=str(here/'phase_shift_extra.json'))
    p.add_argument('--destination',required=True);p.add_argument('--lo',type=int,default=29)
    p.add_argument('--den',type=int,default=2);p.add_argument('--core',type=int,default=65536)
    build(**vars(p.parse_args()))
