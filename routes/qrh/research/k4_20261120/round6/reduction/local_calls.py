"""Upper bounds for hinges on a genuine subinterval above the verified height."""
import argparse
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx
from exact_bridge import A,H,interpolated_point,smooth_cached
from tables import angular_edge
from finite_anchor import modest_right
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"folds"))
from fold_mean import source

@lru_cache(maxsize=256)
def constants(start,end,div,prec,shrink):
    assert ctx.prec==prec and 0<=start<end and div>0
    lo=arb(H)*(arb(start)/div).exp()
    hi=arb(H)*(arb(end)/div).exp()
    R=(hi-lo)/2
    C=(hi+lo)/2
    U=R.log()
    m=2048
    v=A("1.01")
    B=C+v*R
    assert v*R<C and 8192/R<1 and ((1+2/R)/v)**m<A("1e-6")
    assert 1/(1-(A(".5")+2/R)**m)<1+A("1e-6")
    logB=B.log()
    lower=int((logB*10**6).lower().floor().unique_fmpz())
    c4=smooth_cached(lower,210,prec,"centered")
    p=1+4/logB
    mass=c4*B*logB**4*m/(m-p)*(1+(v*R/C)**(m-p))/2
    norm=((1+A("1e-6"))**2/(1-1/arb(H))).log()
    out=[]
    if shrink:
        from translated_short import stats,left as split
        short_rows=[(n,stats(R,C,2310,n)) for n in (8192,65536,262144,1048576)]
    for dd,ww,hh in ((".74","7.5","-2.25"),(".88","8","-2.5"),("1.02","8.5","-2.5")):
        d,w,h=map(A,(dd,ww,hh))
        cm=source(U,w,h,2310,210,12)[0]
        left=(mass**A(".25")*(cm*R*U).sqrt()+(v*m/(m-1)*R)**A(".75"))**A("4/3")
        if shrink:left=left.min(split(R,U,h,cm,mass,short_rows))
        right=modest_right(U,U,d,w,h,32,q=2310,frequency_cut="100")*U
        edge=angular_edge(U,U,w,h,hi,2,q=2310)
        out.append((d,left.log(),right.log(),edge))
    return U,norm,out

def hinges(start,end,div,reals,shrink=False):
    U,norm,params=constants(start,end,div,ctx.prec,shrink)
    out=[]
    for s in reals:
        best=None
        for delta,ll,rr,edge in params:
            den=2-s+3*delta/U
            nu=(2+4*delta/U)/den
            power=3*(1-s+delta/U)/den
            assert 0<power<1
            z=interpolated_point(nu)*(nu*norm+power*ll+(1-power)*rr).exp()/arb.pi()+edge
            best=z if best is None else best.min(z)
        out.append(best)
    return out

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--start",type=int,default=28);cli.add_argument("--div",type=int,default=16)
    cli.add_argument("--short",action="store_true")
    cli.add_argument("--counts",action="store_true")
    args=cli.parse_args();ctx.prec=160
    from strong_rows import improve
    s=list(map(A,(".825",".85",".865")))
    for width in (1,2,4,8,16):
        end=args.start+width
        r=hinges(args.start,end,args.div,s,shrink=args.short)
        U=arb(H).log()+arb(end)/args.div
        total=improve(U,s+[A("7/8")],[arb(10)**60]*3+[arb(0)])
        print("log width",width,args.div,"incremental / global hinge",*[ (x/y).str(8) for x,y in zip(r,total)],
              "incremental values",*[x.str(10) for x in r],flush=True)
        if args.counts:
            nodes=[arb(k)/1000 for k in range(760,865)]
            local=hinges(args.start,end,args.div,nodes,shrink=args.short)
            for t in map(arb,(".826",".851",".865")):
                caps=[v/(t-z) for z,v in zip(nodes,local,strict=True) if z<t]
                upper=caps[0]
                for v in caps[1:]:upper=upper.min(v)
                print("strict abscissa",t.str(4),"positive-ordinate count upper",upper.str(14),flush=True)
