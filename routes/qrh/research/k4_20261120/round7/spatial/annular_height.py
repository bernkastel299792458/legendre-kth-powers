"""A translated detector price for a specified high-ordinate annulus."""
import argparse
import json
from pathlib import Path
import sys
from flint import arb,ctx
from angular_bridge import menu,price
from angular_certificate import certify
from weighted_green import kernel
from exact_bridge import angular_edge,interpolated_point
from grid_target import weights,dot,chord_bounds
root=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(root/'round7'/'first_selected'))
from near_height import left,right,rings,H
from circle_mean import hinge_angular


def upper(lo,hi,first,last,delta,w,h,base,core,grid=2,phase=True,fourth=None,free=False):
    l,L=arb(lo),arb(hi);t0,t1=arb(first).exp(),arb(last).exp()
    # Room on both sides for horizontal extrema of the physical cosine.
    bottom=int(t0.lower().floor().unique_fmpz())-1
    top=int(t1.upper().ceil().unique_fmpz())+1
    size=top-bottom;R=arb(size)/2;U=R.log();d,W,lh=map(arb,(delta,w,h));q=2310
    assert H<bottom<top and U>20 and U+lh>16 and 0<2*d/U<arb('.1')
    assert core<R and arb.pi()/l<arb('.1')
    coeff=None
    if fourth:
        book=json.loads(Path(fourth).read_text(encoding='utf8'))
        logb=(arb(bottom)+arb('2.01')*R).log()
        k=int((logb*book['sub']).lower().floor().unique_fmpz())
        assert arb(k)/book['sub']<=logb and base==210
        row=book['rows'].get(str(k))
        if row is not None and 'uniform_fourth' in row:
            coeff=(row['uniform_fourth'],book['scale'])
    A=left(bottom,size,w,h,base,'1',core,ctx.prec,q,coeff)
    B=U*right(U,U,d,W,lh,64,q,causal='real',cutoff=95)
    edge=angular_edge(U,U,W,lh,height_top=arb(top),length_factor=2,q=q)
    frequency=arb((l+L)/2,(L-l+(4*(-l/4).exp()).log1p())/2)
    row=(d,2*A/(U**2*R),2*B/U,edge,arb(1)/2)
    s=[arb(i)/1000 for i in range(650,875,grid)]+[arb(7)/8]
    wt=weights([s],l)
    raw=[]
    for node in s[:-1]:
        nu,_,val,_,_=kernel(U,row[1],row[2],d,node,frequency)
        raw.append(val*interpolated_point(nu)+edge)
    hinges=chord_bounds(s,raw+[arb(0)])[:-1]
    o=arb(bottom);D=arb(size)
    # Difference of the Riemann--von Mangoldt main terms; both endpoints' errors.
    count=(arb(top)*((arb(top)/(2*arb.pi())).log()-1)-
           o*((o/(2*arb.pi())).log()-1))/(2*arb.pi())+arb('.15')*(o.log()+arb(top).log())+6
    plain=wt[0]*count+dot(wt[1:],hinges)
    pos=plain
    if phase:
        n=14;lines=menu(ctx.prec)
        # Choose exact millesimal nodes ending at the QRH boundary.
        stride=2 if grid==1 else 1
        cell=arb(stride*grid)/1000
        geom=certify(cell*frequency,n,True,3,weight_step=cell*l,details=True)
        for off in range(stride):
            # Skip the last point if its outgoing mesh is irregular.
            last_id=len(s)-2-off-(int(225%grid!=0))
            ids=[last_id-(n-1-j)*stride for j in range(n)]
            if not (s[ids[0]]+n*cell>=s[-1] or (s[ids[0]]+n*cell).overlaps(s[-1])):continue
            assert all(abs(wt[k+1]/wt[ids[0]+1]-v)<arb('1e-39') for k,v in zip(ids,geom[1],strict=True))
            pos-=wt[ids[0]+1]*price([s[k] for k in ids],[hinges[k] for k in ids],
                                    geom,[row],U,frequency,lines)
    absolute=plain
    if free:
        from free_green import FreeGreen
        from weighted_green import radial
        lines=menu(ctx.prec);columns={}
        def cap(i,family,harm):
            assert family==0 and harm==1
            if i not in columns:
                nu,p,v,ql,qr=kernel(U,row[1],row[2],d,s[i],frequency.lower())
                assert max(ql,qr)<arb('1e-6')
                v*=(1+ql)**p*(1+qr)**(1-p)
                columns[i]=[v*radial(line,nu) for line in lines]
            return columns[i]
        for positive in (True,False):
            cone=FreeGreen(s,wt[1:],frequency,2*grid,positive,tight=True)
            saved=cone.saving(U,hinges,[row],{0:[0]},cap)
            if positive:pos=pos.min(plain-saved)
            else:absolute=absolute.min(plain-saved)
    print('translated annulus',first,last,'L',lo,hi,'scalar',plain.str(15),'absolute cosine',absolute.str(15),
          'positive cosine',pos.str(15),flush=True)
    return absolute,pos


if __name__=='__main__':
    ctx.prec=160
    p=argparse.ArgumentParser()
    p.add_argument('--lo',default='139.2');p.add_argument('--hi',default='139.21')
    p.add_argument('--first',default='35');p.add_argument('--last',default='36')
    p.add_argument('--delta',default='1.1');p.add_argument('--w',default='8.5');p.add_argument('--h',default='-2.25')
    p.add_argument('--base',type=int,default=210);p.add_argument('--core',type=int,default=131072)
    p.add_argument('--grid',type=int,default=1)
    p.add_argument('--fourth',help='certified cumulative Euler-product fourth-moment table')
    p.add_argument('--free',action='store_true')
    args=vars(p.parse_args());upper(**args)
