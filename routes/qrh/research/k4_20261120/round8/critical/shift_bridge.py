"""Replay the physical polygon with a choice of certified Gabriel left lines."""
import argparse
import inspect
from functools import lru_cache
from pathlib import Path
import sys

from flint import arb,ctx

from shift_detector import left
research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round7"/"spatial"))
import height_profile as profile
from mellin_bridge import complete_sweep_table


@lru_cache(maxsize=4096)
def shifted_row(ui,vi,ws,lhs,hs,prec):
    assert prec==ctx.prec
    U=arb(ui)/8;V=arb(vi)/8;h=arb(hs)
    c4=complete_sweep_table(prec)[ui]
    exponent=16+int(((U-34)*2/3).lower().floor().unique_fmpz())
    N=2**min(20,max(12,exponent))
    return left(U,V,h,arb(ws),arb(lhs),2310,N,c4)[0].log()


def extra(uk,vk,w,lh,steps):
    if uk<34 or uk>=42:return []
    i=int((uk*8).unique_fmpz());j=int((vk*8).unique_fmpz())
    ws=w.str(20,radius=False);ls=lh.str(20,radius=False)
    assert (arb(ws)-w).contains(0) and (arb(ls)-lh).contains(0)
    return [(arb(h),shifted_row(i,j,ws,ls,h,ctx.prec)) for h in steps]


def check(first,last,nh,mesh,sub,steps,join=None,provider=None,extra_fn=extra):
    assert sub in (2,4,8,16,32)
    original=profile.exact.test
    source=inspect.getsource(original)
    def replace(a,b):
        nonlocal source
        assert source.count(a)==1
        source=source.replace(a,b)
    replace("choices.append((delta,left.log(),right.log(),edge))",
            "choices.append((delta,left.log(),right.log(),edge,extra(uk,vk,w,lh,shifts)))")
    replace("for delta,ll,rr,edge in choices:","for delta,ll,rr,edge,other in choices:")
    replace("best=z if best is None else best.min(z)", """if s>arb(3)/4:
                        R=1+delta/u
                        for h,leftlog in other:
                            th=(R-s)/(R-arb(1)/2+h)
                            ph=3*th/(2+th);vh=4/(2+th)
                            alt=interpolated_point(vh)*(vh*normlog+ph*(leftlog+u+2*logu)+(1-ph)*(rr+logu)).exp()/(2*arb.pi())+edge
                            z=z.min(alt)
                    best=z if best is None else best.min(z)""")
    env=dict(original.__globals__,extra=extra_fn,shifts=steps)
    exec(compile(source,__file__,"exec"),env)
    try:
        profile.exact.test=env[original.__name__]
        return profile.bound(first,last,nh,mesh,True,True,sub,300,"rough",True,
                             "sweep-table",True,join=join,row_provider=provider)
    finally:
        profile.exact.test=original


if __name__=="__main__":
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--first",default="143.97");parser.add_argument("--last",default="144.011")
    parser.add_argument("--mesh",type=int,default=192);parser.add_argument("--nh",type=int,default=48)
    parser.add_argument("--sub",type=int,default=8);parser.add_argument("--join")
    parser.add_argument("--shifts",default=".003,.006");parser.add_argument("--diagnose",action="store_true")
    a=parser.parse_args();ctx.prec=160
    z=check(a.first,a.last,a.nh,a.mesh,a.sub,tuple(a.shifts.split(",")),a.join)
    print("complete budget",z.str(16),flush=True)
    if not a.diagnose:assert z<1
