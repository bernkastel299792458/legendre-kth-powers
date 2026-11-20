"""Charge all vertical source lines against the same two boundary amplitude distributions."""
from functools import lru_cache
from math import floor,ceil
import numpy as np
from flint import arb,ctx
from weighted_green import research
from radial_detectors import polynomials


@lru_cache(maxsize=16)
def radial_samples(polynomial,prec):
    assert prec==ctx.prec
    multiplicity,coef=list(polynomials())[polynomial]
    deg=len(coef)-1;delta=arb(2).log()/32;div=256
    cosines=[[2*(arb.pi()*j*k/div).cos() for k in range(1,deg+1)] for j in range(div+1)]
    peaks=[]
    for m in range(-128,129):
        y=m*delta;a=[c*(k*y).exp() for k,c in enumerate(coef)]
        h=[sum(a[k]*a[k+j] for k in range(deg+1-j)) for j in range(deg+1)]
        err=(arb.pi()/div)**2*sum(j*j*abs(h[j]) for j in range(1,deg+1))/4
        peak=max((h[0]+sum(u*v for u,v in zip(h[1:],row,strict=True))).upper() for row in cosines)
        peaks.append(((peak+err).log()/(2*multiplicity)).max(0).upper())
    small=sum(abs(c)*arb(16)**(2-k) for k,c in enumerate(coef[2:],2))/multiplicity
    large=sum(abs(c)*arb(16)**k for k,c in enumerate(coef)).log()/multiplicity
    return delta,peaks,small,large,arb(deg)/multiplicity


def radius(y,data):
    delta,peaks,c,A,d=data
    # The radial maximum is increasing. One real upper endpoint suffices.
    y=y.upper()
    cut=128*delta
    if y<=-cut:return c*(2*y).exp()
    if y>=cut:return A+d*(y-cut)
    # Near an exact grid knot use either adjacent secant or their upper
    # endpoint, preserving the maximum-modulus inequality on both sides.
    value=y/delta+128
    ix=int(value.lower().floor().unique_fmpz())
    end=int(value.upper().floor().unique_fmpz())
    if ix<0 or end>=256:
        if ix<0:return peaks[0].max(peaks[1]).max(c/256)
        return peaks[-1].max(A+d*(y-cut).max(0))
    if ix!=end:return max(peaks[ix:end+2])
    t=value-ix
    return (1-t)*peaks[ix]+t*peaks[ix+1]


def shared_charge(U,ell,delta,left,right,nodes,means,polynomial,mesh=8):
    """Inputs are a fixed taper, a fixed left line, outward squared moments and source means.

    means include the selected angular inflation, but exclude horizontal and right-edge costs.
    The returned independent suprema include the Green normalization 1/(2*pi).
    """
    L=left*U.exp()*U**2;R=right*U
    norm=((1+arb('1e-6'))**2/(1-1/arb(3*10**12))).log()
    leftlog=L.log();rightlog=R.log();r=1+delta/U
    terms=[]
    for a,b in zip(nodes,means,strict=True):
        if b.is_zero():continue
        t=(r-a)/(r-ell);nu=4/(2+t);P=3*t/(2+t)
        assert 0<t<1 and b>=0
        s=norm+3*t*leftlog/4+(1-t)*rightlog/2
        terms.append((s,nu,b*P,b*(1-P)))
    if not terms:return arb(0)
    data=radial_samples(polynomial,ctx.prec);cut=data[0]*128
    # All radii lie on the elementary quadratic branch on the far left,
    # and on the logarithmic polynomial bound on the far right.
    lo=floor(min(float((-cut-s)*nu) for s,nu,_,_ in terms))-1
    hi=ceil(max(float((cut-s)*nu) for s,nu,_,_ in terms))+1
    for s,nu,_,_ in terms:
        assert s+lo/nu<=-cut and s+hi/nu>=cut
        assert data[3]+data[4]*(s+hi/nu-cut)>=data[4]/nu
    mx1=arb(0);mx2=arb(0);dx=arb(1)/mesh
    for j in range(lo*mesh,hi*mesh+1):
        x=arb(j)/mesh;f=(-x).exp();l=arb(0);r=arb(0)
        for s,nu,u,v in terms:
            val=radius(s+x/nu,data);l+=u*val;r+=v*val
        mx1=mx1.max(f*l);mx2=mx2.max(f*r)
    # Convexity of the true sum in x permits secant interpolation in exp(x).
    correction=1+dx**2*dx.exp()/8
    return (mx1+mx2)*correction/(2*arb.pi())


_grids={}


def grid_key(U,ell,delta,left,right,nodes,polynomial,mesh):
    return (tuple(v.repr() for v in (U,ell,delta,left,right)),tuple(v.repr() for v in nodes),polynomial,mesh,ctx.prec)


def proposal_matrix(U,ell,delta,left,right,nodes,polynomial,mesh=8):
    array,l,r=_grids[grid_key(U,ell,delta,left,right,nodes,polynomial,mesh)]
    common=array.astype(float)/(2**21*2*np.pi)
    return common*np.array([float(x) for x in l]),common*np.array([float(x) for x in r])


def compiled_charge(U,ell,delta,left,right,nodes,means,polynomial,mesh=8):
    """Round the one-dimensional support matrix upwards, then reuse it for any source means."""
    key=grid_key(U,ell,delta,left,right,nodes,polynomial,mesh)
    scale=2**21
    if key not in _grids:
        r=1+delta/U;ll=(left*U.exp()*U**2).log();lr=(right*U).log()
        norm=((1+arb('1e-6'))**2/(1-1/arb(3*10**12))).log()
        points=[];coeff_l=[];coeff_r=[]
        for a in nodes:
            t=(r-a)/(r-ell);nu=4/(2+t);p=3*t/(2+t)
            assert 0<t<1
            s=norm+3*t*ll/4+(1-t)*lr/2
            e=(nu*s).exp()
            points.append((s,nu));coeff_l.append(e*p);coeff_r.append(e*(1-p))
        data=radial_samples(polynomial,ctx.prec);cut=data[0]*128
        lo=floor(min(float((-cut-s)*nu) for s,nu in points))-1
        hi=ceil(max(float((cut-s)*nu) for s,nu in points))+1
        for s,nu in points:
            assert s+lo/nu<=-cut and s+hi/nu>=cut
            assert data[3]+data[4]*(s+hi/nu-cut)>=data[4]/nu
        array=np.empty(((hi-lo)*mesh+1,len(nodes)),dtype=np.uint32)
        factors=[(-nu*s).exp() for s,nu in points]
        for ix,j in enumerate(range(lo*mesh,hi*mesh+1)):
            x=arb(j)/mesh;mult=scale*(-x).exp()
            row=[int((mult*z*radius(s+x/nu,data)).upper().ceil().unique_fmpz()) for (s,nu),z in zip(points,factors,strict=True)]
            assert min(row)>=0 and max(row)<2**30
            array[ix]=row
        if len(_grids)>=2400:_grids.pop(next(iter(_grids)))
        _grids[key]=(array,coeff_l,coeff_r)
    array,left_coeff,right_coeff=_grids[key]
    def maximum(coeff):
        v=[(b*c).upper() for b,c in zip(means,coeff,strict=True)]
        mass=sum(v,arb(0)).upper()
        if mass.is_zero():return arb(0)
        iq=np.array([int((x/mass*2**30).upper().ceil().unique_fmpz()) for x in v],dtype=np.int64)
        assert iq.min()>=0 and int(iq.sum())*int(array.max())<2**63
        return mass*int((array@iq).max())/(scale*2**30)
    dx=arb(1)/mesh
    return (maximum(left_coeff)+maximum(right_coeff))*(1+dx**2*dx.exp()/8)/(2*arb.pi())


def demo():
    from complete_green import weights,kernel,radial,radial_table
    from frozen_green import Book
    from free_green import FreeGreen
    from pathlib import Path
    U=arb(35);omega=arb(137);nodes=[arb(k)/2000 for k in range(1300,1750,4)]+[arb(7)/8]
    w=weights([nodes],omega)[1:]
    rows=Book(Path(__file__).with_name('phase_shift_extra.json'),'.012,.016').row(560)
    delta,left,right,edge,ell,f=next(v for v in rows if v[5]==5 and v[4].overlaps(arb('.484')))
    rad=radial_table(ctx.prec)
    for pos,poly in ((True,7),(False,6)):
        obj=FreeGreen(nodes,w,omega,4,pos,tight=True)
        unit=[]
        for a in obj.x:
            nu,p,base,ql,qr=kernel(U,left,right,delta,a,omega,ell)
            assert ql<arb('1e-6') and qr<arb('1e-6')
            unit.append(base*radial(rad[poly],nu))
        means,M,_=obj.train([float(v) for v in unit],sum(x*y for x,y in zip(w[obj.cut:],unit)))
        old=sum(x*y for x,y in zip(means,unit,strict=True))
        joint=shared_charge(U,ell,delta,left,right,obj.x,means,poly)
        frozen=compiled_charge(U,ell,delta,left,right,obj.x,means,poly)
        print('positive',pos,'individual',old.str(12),'shared',joint.str(12),
              'ratio',(joint/old).str(9),'edge',(M*edge).str(9),'compiled',frozen.str(12),flush=True)
        assert joint<old and frozen<old and abs(frozen-joint)<old*arb('.0001')


if __name__=='__main__':
    ctx.prec=160
    demo()
