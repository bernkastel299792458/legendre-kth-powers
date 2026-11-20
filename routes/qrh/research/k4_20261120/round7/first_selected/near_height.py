"""Use a translated detector with fixed right exponent on each near-H window."""
import argparse
from fractions import Fraction
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx
from selected import H,A,left,rings,RESEARCH,hinge_angular
sys.path.insert(0,str(RESEARCH/"round7"/"taper"))
from mellin_bridge import right
from low_replay import weights as old_weights


@lru_cache(None)
def weighted(location,size,w,h,delta,base,q,precision):
    assert ctx.prec==precision
    U=(arb(size)/2).log();d,W,lh=map(A,(delta,w,h))
    assert U>20 and U+lh>16 and 2*d/U<arb(".1")
    # Both vertical integrals are half of a full-axis translated mean.
    a=left(H,size,w,h,base,"1.25" if base==6 else "1.5",8192,precision,q)
    b=U*right(U,U,d,W,lh,64,q,causal="real",cutoff=95)
    geom=rings(H,size,w,h,precision,q=q)
    Y=(U+lh).exp();logx=A(location)
    assert 8192<arb(size)/2 and (1+2*(Y.log()+2)/Y)**15<A("1.5")
    normal=(1+A("1e-6"))**2/(1-1/arb(H))
    args=U,d,a,b,normal,size*(2*(Y.log()+2)/Y)**2/arb.pi(),arb(1)
    count=A(".3")*arb(H).log()+6+((H/(2*arb.pi())).log()/(2*arb.pi())+A(".15")/H)*size+arb(size)**2/(4*arb.pi()*H)
    real=[arb(i)/1000 for i in range(640,875,2)]+[A("7/8")]
    cost= ((real[0]-1)*logx).exp()*count
    from grid_target import chord_bounds,weights
    vals=chord_bounds(real,[hinge_angular(s,args,geom) for s in real[:-1]]+[arb(0)])
    coeffs=weights([real],logx)[1:]
    return cost+sum(v*c for v,c in zip(vals[:-1],coeffs,strict=True))


def charge(lo,hi,size,panels,base=30,q=2310):
    a=(1-A("1e-12"))*(H+size)*(4*(-A(hi)/4).exp()).log1p()/2
    K=arb(H+size);Q=arb(10000);height=arb(H)
    caps=[];values=[]
    for i in range(panels+1):
        t=Fraction((size+1280000)*i,panels)
        if i<panels:
            s=(a*(size-A(str(t)))/K).max(0).min(arb.pi()/2)
            caps.append((s.sin()+2*Q*a/(arb.pi().sqrt()*K)).min(1)/a.sin())
        if i:
            D=-(-t.numerator//t.denominator)
            original=old_weights(lo,D,".73","7.8","-2.65",6)
            val=original
            if (arb(D)/2).log()>20:
                val=val.min(weighted(lo,D,"7.5","-2.5",".73",base,q,ctx.prec))
            values.append(val)
    assert all(v>w for v,w in zip(caps,caps[1:]+[arb(0)]))
    total=2*(1/(16*Q**2)).exp()*sum((v-w)*b for v,w,b in zip(caps,caps[1:]+[arb(0)],values))
    print("near-height charge",lo,hi,size,panels,base,q,total.str(15),flush=True)
    return total


def reference_charge(lo,hi,size):
    bounds={16000000000:'0.005136954129',24000000000:'0.008863230454',
            32000000000:'0.012974040787',48000000000:'0.021994422840',60000000000:'0.030243530145',
            100000000000:'0.061018556407'}
    cap=arb(bounds[size]); l=arb(lo); h=arb(hi); k=arb(H+size)
    def radius(t):return (1-arb('1e-12'))*k*(4*(-t/4).exp()).log1p()/2
    a=radius(h); ref=radius(arb('115.412')); z=ref*size/k
    assert 0<a<arb.pi() and 0<ref<arb.pi() and z<arb.pi()/2 and a*size/k<arb.pi()/2
    assert z.sin()+2*10000*ref/(arb.pi().sqrt()*k)<1
    delta=l-arb('115.402')
    factor=(-(delta/8)).max(-delta).exp()*a/ref*ref.sin()/a.sin()*z/z.sin()
    value=cap*factor
    if size==16000000000:
        sys.path.insert(0,str(RESEARCH/'round7'/'physical'))
        from weighted_lobe import high_transfer
        value=value.min(arb('.005937108818')-high_transfer(lo,hi))
    return value


if __name__=="__main__":
    ctx.prec=160
    cli=argparse.ArgumentParser()
    cli.add_argument("--lo",default="115.4");cli.add_argument("--hi",default="115.42")
    cli.add_argument("--size",type=int,default=16000000000)
    cli.add_argument("--panels",type=int,default=8)
    cli.add_argument("--base",type=int,default=30);cli.add_argument("--q",type=int,default=2310)
    args=cli.parse_args()
    charge(**vars(args))
