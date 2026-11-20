"""Physical-grid replay with a compact density of height at most 3/2."""
import argparse
from functools import lru_cache,partial
from pathlib import Path
import sys
from types import FunctionType

from flint import arb,ctx

research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round7"/"taper"))
import mellin_bridge
from mellin_bridge import exact
import polygon

NUM=(1397091,1397091,1392938,1387210,1379574,1367723,1355873,1340483,
     1321870,1303258,1278851,1254346,1228551,1197489,1166427,1132112,
     1095535,1058959,1018462,976428,934393,886799,839205,791611,737924,
     684237,630550,567313,504077,430733,357388,284044,0)


@lru_cache(maxsize=2)
def spectrum(step,tail,prec):
    """Return interval caps on [j/step,(j+1)/step] and the inverse-square tail."""
    n=len(NUM)-1
    total=2*sum(NUM)-NUM[0]
    assert all(v>=0 for v in NUM) and NUM[-1]==0 and 4*n*max(NUM)<=3*total
    jump=[2*(NUM[1]-NUM[0])]+[2*(NUM[k-1]-2*NUM[k]+(NUM[k+1] if k<n else 0))
                              for k in range(1,n+1)]
    assert sum(jump)==0 and prec==ctx.prec
    scale=arb((2*n)**2)/total
    variation=scale*sum(abs(a) for a in jump)
    second=sum(abs(a)*i*i for i,a in enumerate(jump))/arb(total)
    moment=(arb(1)/6+2*sum(v*i*i for i,v in enumerate(NUM))/arb(total))/(2*n)**2
    err1,err2=moment/(8*step**2),second/(8*step**2)
    def numerator(i):
        z=2*(arb(i)/(2*n*step)).cos()
        prev=last=arb(0)
        for k in reversed(jump[1:]):prev,last=z*prev-last+k,prev
        return abs(scale*(jump[0]+z*prev/2-last))
    raw=[]
    a=numerator(step//2)
    for i in range(step//2,tail*step):
        b=numerator(i+1)
        lo,hi=arb(i)/step,arb(i+1)/step
        raw.append(((a/lo**2).max(b/hi**2)+err1).min((a.max(b)+err2)/lo**2))
        a=b
    return raw,variation


def profile_cap(d,step=256,tail=192):
    raw,variation=spectrum(step,tail,ctx.prec)
    scale=polygon.SCALE
    top=step*tail
    rest=polygon._ceiling(variation*scale/tail**2)
    ticks=[scale]*(top+1)
    ticks[top]=last=rest
    for i in range(top-1,step//2-1,-1):
        lo=arb(i)/step
        val=(raw[i-step//2]+d/2).min(variation/lo**2).min(arb(1))
        last=max(last,polygon._ceiling(val*scale))
        ticks[i]=last
    def cap(y):
        if y>tail:return arb(rest)/scale*(tail/y)**2
        index=int((y*step).lower().floor().unique_fmpz())
        # Floor indexing includes the containing cell, including an undecidable endpoint.
        return arb(ticks[max(0,min(index,top))])/scale
    return cap


def bound(first,last,nheight=64,mesh=64,real=False,tight=False,sub=2,cutoff=100,jordan=False,prime=False,interference=False,adaptive_core=False,join=None,row_provider=None):
    assert arb(first)>=140
    original=exact.test
    provider=partial(mellin_bridge.finite_row,causal="real" if real else False,cutoff=cutoff,jordan=jordan,prime=prime,interference=interference,adaptive_core=adaptive_core)
    if row_provider is not None:provider=row_provider
    run=FunctionType(original.__code__,dict(original.__globals__,cap_table=profile_cap,
                     finite_row=provider),original.__name__,
                     original.__defaults__,original.__closure__)
    a,b=arb(first),arb(last)
    eps=4*(-a/4).exp()
    # Replace the previously allowed 4/3 by the proved 3/2 in the prime-power term.
    powers=(1+eps)**(arb(3)/2)*(b+eps.log1p())**2*(-a/4).exp()/(6*arb(2).log())
    retained=[]
    def observe(x,y,cost):
        retained.append((x,y,cost+powers/8))
    result=run(first,last,mellin_bridge.PARAM,nheight,mesh,2,128,2**20,
               "1",sub,210,"centered",2310,hi=46,interpolate=True,tight_rows=tight,
               observe_cell=observe if join is not None else None)
    if join is not None:
        edge=b;worst=arb(0)
        for x,y,cost in reversed(retained):
            if not cost<1:break
            edge=x;worst=worst.max(cost)
        assert edge<b
        endpoint=int((edge*1000).upper().ceil().unique_fmpz())
        print("certified suffix from",endpoint,"/1000 to",last,"upper",worst.str(15),flush=True)
        assert arb(join)>=edge.upper() and arb(join)<=b
        return worst
    return result+powers/8


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--first",default="146.5")
    parser.add_argument("--last",default="146.71")
    parser.add_argument("--nh",type=int,default=80)
    parser.add_argument("--mesh",type=int,default=96)
    parser.add_argument("--diagnose",action="store_true")
    parser.add_argument("--real",action="store_true")
    parser.add_argument("--tight",action="store_true")
    parser.add_argument("--sub",type=int,default=2)
    parser.add_argument("--cutoff",type=int,default=100)
    parser.add_argument("--jordan",action="store_true")
    parser.add_argument("--inner",action="store_true")
    parser.add_argument("--rough",action="store_true")
    parser.add_argument("--prime",action="store_true")
    parser.add_argument("--interference",action="store_true")
    parser.add_argument("--rational",action="store_true")
    parser.add_argument("--rational-groups",action="store_true")
    parser.add_argument("--multiplier",action="store_true")
    parser.add_argument("--endpoint",action="store_true")
    parser.add_argument("--weighted",action="store_true")
    parser.add_argument("--sweep",action="store_true")
    parser.add_argument("--sweep-table",action="store_true")
    parser.add_argument("--join",help="require the entire suffix beginning at this physical point")
    parser.add_argument("--adapt-core",action="store_true")
    args=parser.parse_args()
    ctx.prec=160
    moment="grouped" if args.rational_groups else ("rational" if args.rational else args.interference)
    if args.multiplier:moment="multiplier"
    if args.endpoint:moment="endpoint"
    if args.weighted:moment="weighted"
    if args.sweep:moment="sweep"
    if args.sweep_table:moment="sweep-table"
    jordan="inner" if args.inner else args.jordan
    if args.rough:jordan="rough"
    value=bound(args.first,args.last,args.nh,args.mesh,args.real,args.tight,args.sub,args.cutoff,jordan,args.prime,moment,args.adapt_core,args.join)
    print("complete spatial profile bound",value.str(16),flush=True)
    if not args.diagnose:assert value<1
