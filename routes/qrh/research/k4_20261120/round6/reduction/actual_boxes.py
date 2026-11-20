"""Direct optimization of the six actual counts at their exact cumulative heights."""
import argparse
from pathlib import Path
import sys
from flint import arb,ctx
from coupled import A,H,SIX
from exact_bridge import interpolated_point
from tables import angular_edge
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round7"/"taper"))
from mellin_bridge import finite_row

MENU=((".92","8","-2"),("1.04","8.5","-2.25"),("1.1","8.5","-2.25"),
      ("1.16","9","-2.5"),("1.22","8.5","-2.5"),("1.1","9.5","-3"),
      ("1.28","9.5","-2.75"),("1.16","9","-3"),("1.04","9.5","-3.5"))
FROZEN=((54,"1.1","8.5","-2.25",17499504),(54,"1.1","8.5","-2.25",6768868),
        (57,"1.22","8.5","-2.5",150226960),(52,"1.1","8.5","-2.25",65144864),
        (49,"1.16","9","-2.5",25741660),(46,"1.16","9","-2.5",160413149))

def bound(k,m,cells=128,menu=MENU,gaps=range(4,161),rational=False,sweep=False):
    u=arb(H).log()+arb(k)/4
    norm=((1+A("1e-6"))**2/(1-1/arb(3*10**12))).log()
    th=arb(m)/1000
    best=None;chosen=None
    for dd,ww,hh in menu:
        d,w,h=map(A,(dd,ww,hh))
        options=dict(cutoff=300,interference="rational",jordan=True,prime=True) if rational else {}
        if sweep:options=dict(cutoff=300,interference="sweep",jordan="rough",prime=True,adaptive_core=True)
        l,r=finite_row(u,u,d,w,h,1048576,cells,"1",210,"centered",2310,causal="real",**options)
        L=l.log()+u+2*u.log();R=r.log()+u.log()
        edge=angular_edge(u,u,w,h,q=2310)
        for j in gaps:
            gap=arb(j)/4000
            s=th-gap
            den=2-s+3*d/u
            p=3*(1-s+d/u)/den
            eta=(2+4*d/u)/den
            assert 0<p<1
            v=(interpolated_point(eta)*(norm*eta+p*L+(1-p)*R).exp()/(2*arb.pi())+edge)/gap
            if best is None or v<best:
                best=v;chosen=(j,dd,ww,hh)
            else:best=best.min(v)
    return best,chosen

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--scan",action="store_true")
    cli.add_argument("--rational",action="store_true")
    cli.add_argument("--sweep",action="store_true")
    args=cli.parse_args()
    ctx.prec=160
    first_failing=[1089900,420071,10495930,3630069,1158145,5070970]
    for (k,m),(j,dd,ww,hh,limit) in zip(SIX,FROZEN,strict=True):
        val,chosen=(bound(k,m,rational=args.rational,sweep=args.sweep) if args.scan else bound(k,m,menu=[(dd,ww,hh)],gaps=[j],rational=args.rational,sweep=args.sweep))
        assert val<limit+1
        print(k,m,"actual finite count bound",val.str(13),"chosen 4000-gap and triple",chosen,flush=True)
        if not args.scan:
            gap=arb(j)/4000
            v=arb(m)/1000-gap
            population=sum(3*r*(arb(s)/1000+arb(1)/10**6-v).max(arb(0))
                           for (prior,s),r in zip(SIX,first_failing,strict=True) if prior<=k)
            assert population/(val*gap)<arb(".306")
