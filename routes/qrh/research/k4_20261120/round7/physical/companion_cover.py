"""Pointwise fourth-power budget with signed, equal-bandwidth Logan companions."""
import argparse
import json
from fractions import Fraction
from functools import partial
from pathlib import Path
import sys
from flint import arb,ctx,fmpz
from companion_shape import Shape
from direct_partition import original_charges,H,budget,grouped
from bilinear import rational
from odd_sieve import denominator
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'first_selected'))
from near_height import charge,reference_charge


def verify(lo,hi,size,count,weight,first,lobes,ratio,secondary_ratio,inside,
           panels,mesh,modulus=30,both=False,height_table=None,sieve_table=None,decay=0,plus_share='.5',weights=None,parts=False):
    l,h=map(arb,(lo,hi));K=arb(H+size);r=arb('1e-6');Q=arb(10000)
    assert 115<l<h<116 and 0<size<H//2 and count+first-1<=lobes<=512
    assert 2*arb.pi()*(lobes+2)<K*r and mesh>=24 and modulus in (2,6,30,210)
    cmax=h+(4*(-l/4).exp()).log1p()/2
    assert l-r>arb('114.98') and cmax+r<116
    slope,intercept,offset,peaks,a=original_charges(l,h,size)
    mix=Shape(a,count,weight,first,both,decay,plus_share,weights)
    mix.set_lobes(lobes)
    mass=arb.pi()*a.sin()/a
    base=2*(cmax+r)*(r/2).exp()/mass
    A,P,C=mix.lobe(0,K,max(512,mesh))
    rest=[arb(0),arb(0),arb(0)]
    for j in range(1,lobes+1):
        vals=mix.lobe(j,K,mesh)
        rest=[x+y for x,y in zip(rest,vals,strict=True)]
    rem=partial(grouped.remainder,modulus=modulus,exact_harmonics=True,sparse=3)
    common=json.loads(Path(sieve_table).read_text(encoding='utf8')) if sieve_table else None
    if common:
        assert Fraction(common['lo'])<=Fraction(lo)<Fraction(hi)<=Fraction(common['hi'])
        assert Fraction(common['rows'][0]['inside'])==Fraction(inside)
    def direct(sel,area,cap,osc,width):
        z=rational(Fraction(sel))*((l-K.log())/2).exp()
        G=denominator(z,modulus)
        assert 0<G and z<(l-r).exp() and cap>0 and area>0 and osc>0
        area=area if width is None else area+cap*width/2
        if common:
            from lobe_reference import transfer
            G,price=transfer(common,l,h,size,modulus,sel,area,cap,osc,width)
        else:
            err,_=rem(l,cmax,K,z,G,2**48,cap,osc,area,width is None,True,inside=width,poisson=True)
            price=K*(-l).exp()*cap*z*z*err
        return base*(r.exp()*int(fmpz(modulus).euler_phi())*area/(modulus*G)+price)
    eps=rational(Fraction(inside))
    assert 0<eps<a
    first_charge=direct(ratio,A,P,C,eps)
    rest_charge=direct(secondary_ratio,*rest,None)
    tail_area=(2*(arb.pi()-a)*a.cos()+2*a.sin())/(4*arb.pi()**2*lobes)
    tail_peak=(1+a.cos())/(2*arb.pi()**2*lobes)
    tail=mix.tail_ratio*(2*slope*tail_area+intercept*tail_peak)
    old,old_edge=budget(l,h,arb('1.16613'),size)
    small=old-old_edge-offset-slope*(1-a/arb.pi())*mass-intercept*peaks
    g0=(1-a.cos())/a**2
    reciprocal=sum((abs(e)/b for b,e in zip(mix.bs,mix.coefficients,strict=True)),arb(0))
    small_factor=arb(2).max(mix.tail_ratio).max(mix.c+reciprocal/g0).max(mix.c+a*reciprocal)
    assert small_factor<=4
    pole=16*arb.pi().sqrt()*Q/(K*mass)
    mult=mix.c+sum((abs(e)*b/2 for b,e in zip(mix.bs,mix.coefficients,strict=True)),arb(0))
    small=small_factor*small+(mult-small_factor).max(0)*pole
    scale=mix.spectral_ratio((size+128*Q)/K)
    if height_table:
        from companion_heights import charge as spectral_charge
        table=json.loads(Path(height_table).read_text(encoding='utf8'))
        assert table['size']==size
        high=spectral_charge(lo,mix,table,hi)
        if size in (16000000000,24000000000,32000000000):
            high=high.min(scale*reference_charge(lo,hi,size))
    else:
        original=charge(lo,hi,size,panels) if panels else reference_charge(lo,hi,size)
        high=scale*original
    # The bad Gaussian event inside the finite window costs at most the
    # first factor 100. Beyond the window the Gaussian density costs O(K/Q).
    remote=(100+20*K/Q)*(small_factor/2)*(K+128*Q)**2*(-arb(128)**2/4).exp()
    assert remote<arb('1e-1700') and a.sin()>arb('.5') and mass>1
    total=small+first_charge+rest_charge+tail+high+remote
    if parts:
        assert height_table and size==table['size']
        delta=l-arb(table['location'])
        total_mass=(-delta).max(-delta/8).exp()*table['rows'][-1]/table['scale']
        lipschitz=(mix.c+mix.mass)*a/(K*a.sin())
        gaussian=4*Q*(1/(16*Q**2)).exp()*lipschitz*total_mass/arb.pi().sqrt()
        return small+first_charge+rest_charge+tail+remote+gaussian,mix
    print('companion budget',lo,hi,size,'first',first_charge.str(10),'secondary',rest_charge.str(10),
          'tail',tail.str(9),'misc',small.str(9),'height ratio',scale.str(9),
          'height',high.str(9),'total',total.str(17),flush=True)
    return total


if __name__=='__main__':
    ctx.prec=192
    ap=argparse.ArgumentParser()
    ap.add_argument('--lo',default='115.404');ap.add_argument('--hi',default='115.410')
    ap.add_argument('--size',type=int,default=24000000000)
    ap.add_argument('--count',type=int,default=24);ap.add_argument('--weight',default='.3')
    ap.add_argument('--first',type=int,default=1);ap.add_argument('--lobes',type=int,default=64)
    ap.add_argument('--ratio',default='145');ap.add_argument('--secondary-ratio',default='146')
    ap.add_argument('--inside',default='.0016')
    ap.add_argument('--panels',type=int,default=0);ap.add_argument('--mesh',type=int,default=96)
    ap.add_argument('--modulus',type=int,default=30)
    ap.add_argument('--check',action='store_true')
    ap.add_argument('--both',action='store_true')
    ap.add_argument('--height-table')
    ap.add_argument('--sieve-table')
    ap.add_argument('--decay',type=int,default=0)
    ap.add_argument('--plus-share',default='.5')
    ap.add_argument('--weights',help='prescribed positive coefficients, e.g. 1-/0.02,3+/0.01')
    ap.add_argument('--weights-file',type=Path,help='fixed prescribed coefficients')
    params=vars(ap.parse_args());check=params.pop('check')
    file=params.pop('weights_file')
    if file:
        assert params['weights'] is None
        params['weights']=file.read_text(encoding='utf8').strip()
    value=verify(**params)
    if check:assert value<1
