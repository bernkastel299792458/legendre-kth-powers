"""Replace the first and secondary positive-lobe costs directly in the original formula."""
import argparse
from functools import partial
from pathlib import Path
import sys
from flint import arb,ctx
import grouped_lobes as grouped
from cover import H,budget


def original_charges(l,h,size):
    pi=arb.pi(); K=arb(H+size); radius=arb('1e-6'); eta=arb('1.16613')
    a=(1-arb('1e-12'))*K*(4*(-h/4).exp()).log1p()/2
    width=2*(pi-a); mass=pi*a.sin()/a
    def tangent(scale):
        v=l-K.log()+eta+scale.log()
        c=2*(l+radius)*(radius/2).exp()/(mass*v**2)
        return c*radius.exp()*(v-1), c*scale
    slope,intercept=tangent(arb('1.55'))
    # The 256 signed corrections and 64 peak caps occur in check_edge.budget.
    offset=arb(0); old=a.sin()/(2*a)
    for i in range(256):
        wl,wr=width*i/256,width*(i+1)/256
        v=a+wr
        nxt=(a.cos()-v.cos())/(v*v-a*a) if i<255 else arb(0)
        m,c=tangent((wl+wr)/2)
        offset+=2*(old-nxt)*(c+((m-slope)*wl).max((m-slope)*wr))
        old=nxt
    peaks=(1+a.cos())/(2*pi**2*64)
    for j in range(1,65):
        best=arb(0)
        for i in range(32):
            u=2*pi*j+a+width*i/32; v=2*pi*j+a+width*(i+1)/32
            num=(1+a.cos()).min(a.cos()-((u+v)/2).cos()+(v-u)/2)
            best=best.max(num/(u*u-a*a))
        peaks+=2*best
    return slope,intercept,offset,peaks,a


def verify(lo,hi,ratio,secondary_ratio,inside,lobes,qrh,size,panels,modulus,triangle='0',majorant=False,collisions=False,split=0,twice_moving=False):
    l,h=arb(lo),arb(hi)
    size=(16000000000 if qrh else -206000) if size is None else size
    assert (qrh and size>0) or (not qrh and size<0)
    assert 115<l<h<116 and 16<=lobes and modulus in (2,6,30,210)
    provider=partial(grouped.remainder,modulus=modulus,exact_harmonics=True,
                     triangle=triangle,sparse=3 if collisions else (2 if majorant else 1))
    cfg=dict(location_hi='116',energy=True,poisson=True,modulus=modulus,
             remainder_override=provider,sharp_variation=True,physical_terms=True)
    first_provider=provider
    if twice_moving:
        from lobe_variation import twice_moving as variation
        K=arb(H+size)
        radius=(1-arb('1e-12'))*K*(4*(-h/4).exp()).log1p()/2
        first_provider=partial(provider,moving_parts=variation(radius,K,0))
    if split:
        from endpoint_density import cost
        A1,e1=cost(lo,hi,size,ratio.split(','),inside.split(','),modulus,provider,split)
        s1=arb(0)
    else:
        cfg['remainder_override']=first_provider
        A1,s1,e1=grouped.base.first_charge(lo,hi,size,ratio,2**48,None,inside_width=inside,**cfg)
    if twice_moving:
        cfg['remainder_override']=partial(provider,moving_parts=variation(radius,K,lobes))
    A2,s2,e2=grouped.other.charge(lo,hi,size,secondary_ratio,2**48,None,lobes=lobes,**cfg)
    slope,intercept,offset,peaks,a=original_charges(l,h,size)
    total,original_edge=budget(l,h,arb('1.16613'),size)
    remaining_peak=(1+a.cos())/(2*arb.pi()**2*lobes)
    residual=total-offset+(remaining_peak-peaks)*intercept
    residual+=(s1-2*slope)*A1+e1+(s2-2*slope)*A2+e2
    if qrh:
        if panels or size!=16000000000:
            sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'first_selected'))
            from near_height import charge,reference_charge
            finite=charge(lo,hi,size,panels) if panels else reference_charge(lo,hi,size)
        else:
            assert size==16000000000
            finite=arb('.005937108818')-grouped.base.high_transfer(lo,hi)
        K=arb(H+size); Q=arb(10000); mass=arb.pi()*a.sin()/a
        assert 0<a<arb.pi()
        remote=2*K/mass*arb.pi()*(1-a.cos())/(a*a*arb.pi().sqrt()*Q)
        remote*=(1/(16*Q**2)).exp()*(K+128*Q)**2*(1+arb(4)/128**2)*(-arb(128)**2/4).exp()
        assert remote<arb('1e-1700')
        residual+=finite+remote-original_edge
    print('original lobe partition',lo,hi,'size',size,'secondary pairs',lobes,
          'first and secondary new charges', (s1*A1+e1).str(10), (s2*A2+e2).str(10),
          'full',residual.str(18),flush=True)
    return residual


if __name__=='__main__':
    ctx.prec=192
    parser=argparse.ArgumentParser()
    parser.add_argument('--lo',default='115.402');parser.add_argument('--hi',default='115.412')
    parser.add_argument('--ratio',default='138');parser.add_argument('--secondary-ratio',default='146')
    parser.add_argument('--inside',default='.0016');parser.add_argument('--modulus',type=int,default=30)
    parser.add_argument('--lobes',type=int,default=64);parser.add_argument('--qrh',action='store_true')
    parser.add_argument('--size',type=int);parser.add_argument('--panels',type=int,default=0)
    parser.add_argument('--triangle',default='0');parser.add_argument('--check',action='store_true')
    parser.add_argument('--majorant',action='store_true')
    parser.add_argument('--collisions',action='store_true')
    parser.add_argument('--split',type=int,default=0)
    parser.add_argument('--twice-moving',action='store_true')
    args=vars(parser.parse_args());check=args.pop('check')
    value=verify(**args)
    if check: assert value<1
