"""Keep the physical cosine in the translated low-height zero term."""
import argparse
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx
from near_height import A,H,RESEARCH,left,right,rings,hinge_angular,weighted,old_weights
sys.path.insert(0,str(RESEARCH/'round7'/'spatial'))
from angular_bridge import menu,price
from angular_certificate import certify
from exact_bridge import angular_edge
from grid_target import chord_bounds,weights,dot


def rv_count(length):
    return (A('.3')*arb(H).log()+6+((H/(2*arb.pi())).log()/(2*arb.pi())+
            A('.15')/H)*length+length**2/(4*arb.pi()*H))


@lru_cache(None)
def geometry(lo,hi,spacing,count,precision):
    assert precision==ctx.prec
    l,h=map(arb,(lo,hi))
    width=(4*(-l/4).exp()).log1p()
    frequency=arb((l+h)/2,(h-l+width)/2)
    step=arb(spacing)/1000
    return frequency,certify(step*frequency,count,True,3,weight_step=step*l,details=True)


def cumulative(lo,hi,cut,base,q,spacing=3,count=14,free=False,original=False):
    # Horizontals at multiples of pi/frequency are picked inside this window.
    # The short omitted bottom portion is charged with the true counting theorem.
    size=cut+1
    U=(arb(size)/2).log()
    delta,W,lh=map(arb,('.73','7.5','-2.5'))
    l=arb(lo); freq,shape=geometry(lo,hi,spacing,count,ctx.prec)
    assert U>20 and 8192<arb(size)/2 and arb.pi()/freq<arb('.1')
    if original:
        assert base==6 and q==210
        W,lh=arb('7.8'),arb('-2.65')
        args,ring=old_weights(lo,size,'.73','7.8','-2.65',6,True)
        a,b=args[2:4]
    else:
        a=left(H,size,'7.5','-2.5',base,'1.25' if base==6 else '1.5',8192,ctx.prec,q)
        b=U*right(U,U,delta,W,lh,64,q,causal='real',cutoff=95)
        Y=(U+lh).exp()
        normal=(1+arb('1e-6'))**2/(1-1/arb(H))
        edge_r=size*(2*(Y.log()+2)/Y)**2/arb.pi()
        args=U,delta,a,b,normal,edge_r,arb(1)
        ring=rings(H,size,'7.5','-2.5',ctx.prec,q=q)
    real=[arb(i)/1000 for i in range(650,876)]
    ordinary=chord_bounds(real,[hinge_angular(s,args,ring) for s in real[:-1]]+[arb(0)])
    wt=weights([real],l)
    total=wt[0]*rv_count(arb(size))+dot(wt[1:],ordinary[:-1])
    # Moment inputs in kernel() are normalized differently. Both actual full
    # integrals here are twice the stored translated half integrals.
    edge=angular_edge(U,U,W,lh,height_top=arb(H+size),length_factor=2,q=q)
    rows=[(delta,2*a/(U**2*U.exp()),2*b/U,edge,arb(1)/2)]
    lines=menu(ctx.prec)
    saved=arb(0)
    for offset in range(spacing):
        end=len(real)-2-offset
        ids=[end-(count-1-j)*spacing for j in range(count)]
        assert ids[0]>0 and 650+ids[0]+spacing*count>=875
        assert all(abs(wt[j+1]/wt[ids[0]+1]-v)<arb('1e-39') for j,v in zip(ids,shape[1],strict=True))
        part=price([real[j] for j in ids],[ordinary[j] for j in ids],
                   shape,rows,U,freq,lines)
        saved+=wt[ids[0]+1]*part
    omitted=rv_count(arb('.1'))*(-l/8).exp()
    if free:
        from free_green import FreeGreen
        from weighted_green import kernel,radial
        # The full integrals, divided by 2*pi in the kernel, have already
        # been doubled to remove the half-line convention of the input.
        cache={}
        def cap(i,family,harm):
            assert family==0 and harm==1
            if i not in cache:
                d,L,R,_,ell=rows[0]
                nu,P,val,ql,qr=kernel(U,L,R,d,real[i],freq.lower(),ell)
                assert max(ql,qr)<arb('1e-6')
                val*=(1+ql)**P*(1+qr)**(1-P)
                cache[i]=[val*radial(line,nu) for line in lines]
            return cache[i]
        cone=FreeGreen(real,wt[1:],freq,2,True,tight=True,source_floor='.775')
        saved=saved.max(cone.saving(U,ordinary[:-1],rows,{0:[0]},cap))
    return total,total-saved+omitted


def charge(lo,hi,size,panels,base=30,q=2310,spacing=3,count=14):
    l,h=map(arb,(lo,hi))
    assert 114<l<h<116 and 0<size<=150000000000 and panels>=1
    K=arb(H+size);Q=arb(10000)
    a=(1-A('1e-12'))*K*(4*(-h/4).exp()).log1p()/2
    assert 0<a<arb.pi() and a*size/K<arb.pi()/2
    caps=[];bounds=[];raw=None
    for i in range(panels+1):
        pos=Fraction((size+1280000)*i,panels)
        if i<panels:
            y=(a*(size-A(str(pos)))/K).max(0)
            caps.append(y.sin()/a.sin())
        if i:
            D=-(-pos.numerator//pos.denominator)
            raw=old_weights(lo,D,'.73','7.8','-2.65',6)
            signed=raw
            if (arb(D)/2).log()>20:
                raw=raw.min(weighted(lo,D,'7.5','-2.5','.73',base,q,ctx.prec))
                other,cos=cumulative(lo,hi,D,base,q,spacing,count)
                raw=raw.min(other)
                signed=cos.min(raw)
            bounds.append(signed)
    differences=[v-w for v,w in zip(caps,caps[1:]+[arb(0)],strict=True)]
    assert all(d>=0 for d in differences)
    smooth=(1/(16*Q**2)).exp()*2*Q*a/(K*arb.pi().sqrt()*a.sin())
    total=2*(dot(differences,bounds)+smooth*raw)
    print('signed near-height charge',lo,hi,size,panels,'Gaussian error',
          (2*smooth*raw).str(10),'finite',total.str(17),flush=True)
    return total


if __name__=='__main__':
    ctx.prec=160
    parser=argparse.ArgumentParser()
    parser.add_argument('--lo',default='115.402'); parser.add_argument('--hi',default='115.412')
    parser.add_argument('--size',type=int,default=24000000000)
    parser.add_argument('--panels',type=int,default=6)
    parser.add_argument('--base',type=int,default=30);parser.add_argument('--q',type=int,default=2310)
    parser.add_argument('--spacing',type=int,default=3);parser.add_argument('--count',type=int,default=14)
    parser.add_argument('--upper')
    options=vars(parser.parse_args());upper=options.pop('upper')
    val=charge(**options)
    if upper is not None:assert val<arb(upper)
