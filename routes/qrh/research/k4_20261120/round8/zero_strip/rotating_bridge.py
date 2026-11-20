"""Physical scalar certificate using the complete finite-height table with rotation."""
import argparse
from decimal import Decimal
from fractions import Fraction
from pathlib import Path
from flint import arb,ctx
from complete_green import weights,dot,H,profile_cap
from frozen_green import Book


def bridge(first,last,pieces=24,nh=6,low=33,high=41,sub=16,step=4,table='phase_shift_extra.json',shifts='.012,.016',signed=True,diagnose=False):
    book=Book(table,shifts,rotate='signed' if signed else True)
    data,_=book.spectrum(low,high,nh,sub,step)
    T,counts,nodes,rows,F,final=data
    first,last=Fraction(first),Fraction(last);worst=arb(0)
    def dec(q):
        s=str(Decimal(q.numerator)/Decimal(q.denominator))
        assert Fraction(s)==q
        return s
    for k in range(pieces):
        l=dec(first+(last-first)*k/pieces);r=dec(first+(last-first)*(k+1)/pieces)
        a=arb(l);b=arb(r);d=(4*(-a/4).exp()).log1p();d0=(4*(-b/4).exp()).log1p()
        assert d0*T[-1]>192
        w=weights([nodes],a);cap=profile_cap(d)
        E=[arb(1)]+[cap(d0*t) for t in T[1:]]
        count=[w[0]*n+dot(w[1:],row) for n,row in zip(counts,rows,strict=True)]
        finite=sum(((x-y).max(0)*n for x,y,n in zip(E,E[1:],count)),arb(0))
        lasttail=E[-1]*dot(weights(F,a),final)
        primepowers=(1+4*(-a/4).exp())**(arb(3)/2)*(b+d)**2*(-a/4).exp()/(6*arb(2).log())
        total=2*(finite+lasttail+(-a/2).exp()*arb(H)*arb(H).log()+d*count[-1])+arb(9)/8*primepowers+(-3*a).exp()/(1-(-2*a).exp())
        worst=worst.max(total)
        print(l,r,'full upper',total.upper().str(13),flush=True)
    print('complete scalar bridge',dec(first),dec(last),'upper',worst.upper().str(15),flush=True)
    if not diagnose:assert worst<1
    return worst


if __name__=='__main__':
    ps=argparse.ArgumentParser()
    ps.add_argument('--first',default='129');ps.add_argument('--last',default='135')
    ps.add_argument('--pieces',default=24,type=int);ps.add_argument('--nh',default=6,type=int)
    ps.add_argument('--low',default=33,type=int);ps.add_argument('--high',default=41,type=int)
    ps.add_argument('--sub',default=16,type=int);ps.add_argument('--step',default=4,type=int)
    ps.add_argument('--table',default=str(Path(__file__).with_name('phase_shift_extra.json')))
    ps.add_argument('--shifts',default='.012,.016');ps.add_argument('--positive',action='store_true')
    ps.add_argument('--diagnose',action='store_true');args=vars(ps.parse_args());args['signed']=not args.pop('positive')
    ctx.prec=160;bridge(**args)
