"""Bridge using the sieved fourth moment and the matching folded short polynomial."""
import argparse
from fractions import Fraction
import sys

from flint import arb,ctx

from fold_mean import joint,research
sys.path.insert(0,str(research/"round5"/"kernel"))
from finite_anchor import A,REGISTERED,modest_right,moments,verify


def provider(base,depth,alpha,q=210,frequency_cut="100",method="sharp"):
    assert q in (210,2310) and q%base==0
    def get(U,V,delta,W,lh,core,off,unit,cells):
        def value(lo,hi):
            return joint(lo,hi,W,lh,q=q,ncore=core,base=base,depth=depth,alpha=alpha,method=method)[0]
        if V is None:
            left=value(U,None)
            _,right=moments(U,delta,W,lh,q,frequency_cut,tight=True)
        else:
            n=int((2*(V-U)).upper().ceil().unique_fmpz())
            left=arb(0)
            for i in range(n):
                low,high=U+(V-U)*i/n,U+(V-U)*(i+1)/n
                left=left.max(value(low,high))
            right=modest_right(U,V,delta,W,lh,cells,q=q,frequency_cut=frequency_cut)
        assert left>right>0 and 9/((U+lh)/2).exp()<arb(1)/4 and q*(W+lh).exp()>=1
        edge=162*(-lh).exp()/(2*arb.pi())
        edge+=2*(2+(arb(2).log()+9*(11*arb(q).sqrt()*((W+lh)/2).exp()).log())/A("15/14").log())
        return delta,left,right,edge
    return get


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",default="155")
    cli.add_argument("--last",default="162.3")
    cli.add_argument("--param",default=REGISTERED)
    cli.add_argument("--core",type=int,default=2097152)
    cli.add_argument("--cells",type=int,default=128)
    cli.add_argument("--step",type=int,default=2)
    cli.add_argument("--base",type=int,default=30)
    cli.add_argument("--modulus",type=int,choices=(210,2310),default=210)
    cli.add_argument("--frequency-cut",default="100")
    cli.add_argument("--method",choices=("sharp","smoothed","paired","disjoint","projected","centered"),default="sharp")
    cli.add_argument("--alpha",type=Fraction,default=Fraction(3,2))
    cli.add_argument("--depth",type=int,default=12)
    cli.add_argument("--diagnose",action="store_true")
    a=cli.parse_args()
    ctx.prec=160
    val=verify(a.anchor,a.last,a.param,a.core,step=a.step,cells=a.cells,
               row_provider=provider(a.base,a.depth,a.alpha,a.modulus,a.frequency_cut,a.method))
    if not a.diagnose:
        assert val<1
        lo=A(a.anchor)
        idx=(lo/4).exp().ceil().unique_fmpz()
        assert idx is not None and 4*arb(idx-1).log()<lo<4*arb(idx).log()
        print("first integer",idx,flush=True)
