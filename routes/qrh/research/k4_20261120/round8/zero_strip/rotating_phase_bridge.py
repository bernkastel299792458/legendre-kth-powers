"""Combine rotation of the signed angular sources with the spatial polygon certificate."""
import argparse
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from flint import arb,ctx
from complete_green import verify,research
from frozen_green import Book
from weighted_green import H
from height_allocation import add_near_heights,allocate
from joint_polygon import propose,validate


def run(first,last,pieces,table,near,nh,sub,step,top,source_floor,n,limit,reuse,more,opt,diagnose):
    book=Book(table,'.012,.016',rotate='signed')
    lo,hi=Fraction(first),Fraction(last);worst=arb(0);polygon=None
    def dec(x):
        s=str(Decimal(x.numerator)/Decimal(x.denominator));assert Fraction(s)==x
        return s
    for i in range(pieces):
        a,b=[dec(lo+(hi-lo)*j/pieces) for j in (i,i+1)]
        p=i//reuse*reuse
        span=tuple(dec(lo+(hi-lo)*j/pieces) for j in (p,min(pieces,p+reuse)))
        opts=dict(first=a,last=b,nh=nh,sub=sub,hi=top,step=step,book=book,phase_window=span,
                  free_green=True,tight_jump=True,source_floor=source_floor,more_modes=more,
                  rotate_phase=True,rotate_opt=opt,reuse_fit=True)
        budgets=[]
        for kind in ('positive','absolute'):
            out=[]
            def capture(index,value):
                assert index==len(out) and value>0
                out.append(value)
            T,E,constant,tail,unit=verify(**opts,observer=capture,observe_kind=kind)
            budgets.append(out)
        if near:T,budgets=add_near_heights(T,budgets,near,a,b)
        else:T=[arb(H)]+T[1:]
        d0=(4*(-arb(b)/4).exp()).log1p();d1=(4*(-arb(a)/4).exp()).log1p()
        if i%reuse==0:polygon=propose(T,d0,d1,budgets,tail,n,True,limit)
        result=validate(polygon,T,d0,d1,budgets,constant,tail,unit,allocate,True)
        worst=worst.max(result);print('oscillatory rotation',a,b,result.upper().str(15),flush=True)
    print('complete bridge',first,last,worst.upper().str(17),flush=True)
    if not diagnose:assert worst<1
    return worst


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--first',required=True);p.add_argument('--last',required=True)
    p.add_argument('--pieces',type=int,default=1);p.add_argument('--nh',type=int,default=2)
    p.add_argument('--sub',type=int,default=8);p.add_argument('--step',type=int,default=6)
    p.add_argument('--top',type=int,default=41);p.add_argument('--source-floor',default='.775')
    p.add_argument('--n',type=int,default=24);p.add_argument('--limit',type=float,default=60)
    p.add_argument('--reuse',type=int,default=2);p.add_argument('--more',action='store_true')
    p.add_argument('--opt',action='store_true')
    p.add_argument('--diagnose',action='store_true')
    p.add_argument('--table',default=str(Path(__file__).with_name('early_green_rows.json')))
    pre=research/'round7'/'first_selected'
    p.add_argument('--near',default=','.join(str(pre/v) for v in ('companion_original_100.json','companion_original_350.json','companion_rows_600.json')))
    ctx.prec=160;run(**vars(p.parse_args()))
