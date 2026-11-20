"""Jointly price a Logan exterior and a signed density supported inside the gap."""
import argparse
from pathlib import Path
import sys
import numpy as np
from flint import arb,ctx
from height_allocation import run,allocate,H,Book
from joint_polygon import propose,jumps
from signed_profile import local_caps

root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'round7'/'physical'))
from companion_cover import verify


def certify(lo,hi,size,height_table,sieve_table,weights,source,n,near,rotating):
    l,h=map(arb,(lo,hi));dlo=(4*(-h/4).exp()).log1p();dhi=(4*(-l/4).exp()).log1p()
    cost,shape=verify(lo,hi,size,1,'.3',1,64,'145','146','.0016',0,96,
                      weights=weights,height_table=height_table,sieve_table=sieve_table,parts=True)
    book=Book(source,'.012,.016',rotate='signed' if rotating else False)
    T,caps,constant,tail,unit=run(lo,hi,book,3,4,16,41,False,8,near_rows=near,inputs=True)
    K=H+size
    assert K<T[-1] and T[0]==arb(H)
    a=shape.a
    def spectrum(t):
        x=(1-t/K).max(0)
        return (shape.c*(a*x).sin()/a-sum((e*(b*x).sin()/b for b,e in
                zip(shape.bs,shape.coefficients,strict=True)),arb(0)))*a/a.sin()
    af=float(a.mid())
    b=np.array([float(v.mid()) for v in shape.bs]);e=np.array([float(v.mid()) for v in shape.coefficients])
    c=float(shape.c.mid())
    def fast(t):
        x=max(0,1-t/K)
        return (c*np.sin(af*x)/af-np.dot(e,np.sin(b*x)/b))*af/np.sin(af)
    grid,v=propose(T,dlo,dhi,caps,tail,n,True,150,(fast,float(cost.mid())))
    total=2*sum(grid)-grid[0]+v
    assert v>=0 and total>0
    fraction=arb(v)/total
    mass=arb(2*sum(map(abs,grid))-abs(grid[0]))/total
    peak=arb(2*n*max(map(abs,grid)))/total
    V=arb((2*n)**2*sum(map(abs,jumps(grid))))/total
    end=V/(dlo*T[-1])**2
    middle=(dlo+dhi)/2
    def polygon(y):
        z=2*(y/(2*n)).cos()
        p=q=arb(0)
        for coef in reversed(grid[1:]):p,q=z*p-q+coef,p
        return (arb(grid[0])+z*p-2*q)*(y/(4*n)).sinc()**2/total
    curve=mass*middle**2/4+fraction*a/a.sin()*(shape.c*a+
          sum((abs(ec)*b0 for b0,ec in zip(shape.bs,shape.coefficients,strict=True)),arb(0)))/K**2
    target=[]
    for first,last in zip(T[:-1],T[1:],strict=True):
        pos=neg=arb(0)
        if first<K:
            stop=last.min(K)
            step=(stop-first)/12
            nodes=[first+i*step for i in range(13)]
            ys=[fraction*spectrum(t)+polygon(middle*t) for t in nodes]
            err=step**2*curve/8+mass*stop*(dhi-dlo)/4
            pos=(max(y.upper() for y in ys)+err).max(0)
            neg=(max((-y).upper() for y in ys)+err).max(0)
        if last>K:
            p,q=local_caps(dlo*first.max(K),dhi*last,heights=grid,normalization=total)
            pos=pos.max(p);neg=neg.max(q)
        target.append(((pos-end.lower()).upper().max(0),(neg-end.lower()).upper().max(0)))
    ordinate=2*(end*tail+allocate(target,*caps))
    value=fraction*cost+mass*constant+peak*unit+ordinate
    print('mixed weights',v,grid,'exterior',cost.str(12),'fraction',fraction.str(12),
          'height',ordinate.str(12),'complete',value.str(18),flush=True)
    return value


if __name__=='__main__':
    ctx.prec=160
    p=argparse.ArgumentParser()
    p.add_argument('--lo',default='115.425');p.add_argument('--hi',default='115.44')
    p.add_argument('--size',type=int,default=100000000000)
    p.add_argument('--height-table',required=True);p.add_argument('--sieve-table',required=True)
    p.add_argument('--weights',type=Path,required=True)
    p.add_argument('--source',default=str(root/'round8'/'zero_strip'/'early_green_rows.json'))
    p.add_argument('--n',type=int,default=20);p.add_argument('--near',required=True)
    p.add_argument('--rotating',action='store_true');p.add_argument('--check',action='store_true')
    args=vars(p.parse_args());check=args.pop('check')
    args['weights']=args['weights'].read_text(encoding='utf8').strip()
    value=certify(**args)
    if check:assert value<1
