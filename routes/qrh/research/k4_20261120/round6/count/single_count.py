"""Single finite zero-count condition sufficient for covering the fourth-power gap."""
import argparse
from pathlib import Path
import sys

from flint import arb,ctx

sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"reduction"))
from irregular import certify,validate_slabs
from tables import H,get_data,horizons


def known_bound(k,m):
    heights,_,knots,rows,_,_=get_data(4,folded=True)
    index=horizons(heights,4).index(k)
    T=arb(H)*(arb(k)/4).exp()
    assert (heights[index+1].exp()-T).contains(0)
    sigma=arb(m)/1000
    choices=[(a/(sigma-s),s) for s,a in zip(knots,rows[index]) if s<sigma]
    upper,knot=min(choices,key=lambda pair:float(pair[0].upper()))
    print("known positive-part upper bound",upper.str(15),"knot",knot.str(8),flush=True)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--cap",type=int,default=800000)
    cli.add_argument("--sigma-milli",type=int,default=814)
    cli.add_argument("--height-quarter",type=int,default=37)
    cli.add_argument("--last",default="155")
    cli.add_argument("--nheight",type=int,default=16)
    cli.add_argument("--cell",default="1/8")
    cli.add_argument("--diagnose",action="store_true")
    cli.add_argument("--known-only",action="store_true")
    cli.add_argument("--phased",action="store_true")
    a=cli.parse_args()
    ctx.prec=160
    assert a.cap>=0
    validate_slabs(folded=True,phased=a.phased)
    if a.known_only:
        known_bound(a.height_quarter,a.sigma_milli)
        sys.exit(0)
    val=certify([(a.height_quarter,a.sigma_milli)],nheight=a.nheight,cell=a.cell,
                last=a.last,folded=True,phased=a.phased,conditions_fn=lambda u,s:arb(a.cap))
    print("single rectangle bound",a.cap,"sigma",a.sigma_milli,"quarter-height",a.height_quarter,flush=True)
    if not a.diagnose: assert val<1
