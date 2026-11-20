"""Replay a compact signed polygon across closed physical slabs using rotated scalar rows."""
import argparse
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from flint import arb,ctx
from height_allocation import Book,H,add_near_heights,allocate
from complete_green import weights,dot
from joint_polygon import propose,validate


def sweep(first,last,pieces,table,low,high,sub,nh,step,n,reuse,limit,near,heights,diagnose):
    table=Book(table,'.012,.016',rotate='signed')
    (source,counts,nodes,rows,F,final),_=table.spectrum(low,high,nh,sub,step)
    assert H<source[0] and pieces>0 and reuse>0
    lo,hi=map(Fraction,(first,last))
    def dec(q):
        s=str(Decimal(q.numerator)/Decimal(q.denominator))
        assert Fraction(s)==q
        return s
    worst=arb(0);grid=None
    if heights:grid=tuple(map(int,heights.split(',')))
    for i in range(pieces):
        left,right=(dec(lo+(hi-lo)*j/pieces) for j in (i,i+1))
        l,h=map(arb,(left,right));dlo=(4*(-h/4).exp()).log1p();dhi=(4*(-l/4).exp()).log1p()
        wt=weights([nodes],l)
        charge=[wt[0]*nn+dot(wt[1:],vs) for nn,vs in zip(counts,rows,strict=True)]
        caps=[charge,charge]
        if near:T,caps=add_near_heights(source,caps,near,left,right)
        else:T=[arb(H)]+source[1:]
        assert dlo*T[-1]>192
        tail=dot(weights(F,l),final)
        constant=2*((-l/2).exp()*arb(H)*arb(H).log()+dhi*charge[-1])+(-3*l).exp()/(1-(-2*l).exp())
        unit=(1+4*(-l/4).exp())**(arb(3)/2)*(h+dhi)**2*(-l/4).exp()/(8*arb(2).log())
        if heights is None and i%reuse==0:
            grid=propose(T,dlo,dhi,caps,tail,n,True,limit)
            print('polygon',left,grid,flush=True)
        val=validate(grid,T,dlo,dhi,caps,constant,tail,unit,allocate,True)
        worst=worst.max(val)
        print('rotating polygon cell',left,right,val.upper().str(15),flush=True)
    print('whole rotating polygon bridge',first,last,'maximum',worst.upper().str(17),flush=True)
    if not diagnose:assert worst<1
    return worst


if __name__=='__main__':
    ctx.prec=160
    p=argparse.ArgumentParser()
    p.add_argument('--first',required=True);p.add_argument('--last',required=True)
    p.add_argument('--pieces',default=1,type=int);p.add_argument('--reuse',default=4,type=int)
    p.add_argument('--table',default=str(Path(__file__).resolve().parents[2]/'round8'/'zero_strip'/'early_green_rows.json'))
    p.add_argument('--low',type=int,default=29);p.add_argument('--high',type=int,default=41)
    p.add_argument('--sub',type=int,default=8);p.add_argument('--nh',type=int,default=2)
    p.add_argument('--step',type=int,default=6);p.add_argument('--n',type=int,default=24)
    p.add_argument('--limit',type=float,default=80);p.add_argument('--near')
    p.add_argument('--heights');p.add_argument('--diagnose',action='store_true')
    sweep(**vars(p.parse_args()))
