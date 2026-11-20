"""Direct Selberg upper bound integrated against an exterior Logan lobe."""
from math import sqrt
from fractions import Fraction
from flint import arb,ctx,fmpz
from numba import njit
from bilinear import groups,lambdas,upper,lower,rational
from dilation import frequencies
from cover import H

@njit
def block_sum(gs,lam,zlo,zhi,tlo,thi,lg,nlo,nhi,derivative,fixed,moving_only):
    value=0.
    for ga,gb,gw in gs:
        for ha,hb,hw in gs:
            for i in range(len(lam)):
                for j in range(i+1):
                    dl=zlo/(gb*hb*2.**j)
                    el=zlo/(gb*hb*2.**i)
                    di=min(1.,.5+1/dl)
                    ei=min(1.,.5+1/el)
                    q=2.**(i+j)
                    kinv=zhi**2/(nlo*tlo*ga*q)
                    ktop=nhi*thi*gb*q/zlo**2
                    spec=(1+4*ktop/dl)*max(kinv,4*(1+1/dl)/el)
                    reverse=(1+4*ktop/el)*max(kinv,4*(1+1/el)/dl)
                    older=di*(1/el+32*nhi*thi*gb**3*hb**2*q*q/zlo**4*ei)
                    older+=4*lg*(kinv+32*ei/dl)
                    bound=min(di*ei,sqrt(di*ei*min(older,1.06*min(spec,reverse))))
                    smooth=min(1.,derivative/(nlo*ga*q))
                    value+=gw*hw*lam[i]*lam[j]*bound/q*(1 if i==j else 2)*(smooth if moving_only else (min(1.,fixed/(nlo*ga*q))+smooth)/2)
    return value


from extras.weight_energy import paley

@njit
def block_energy(gs,energies,weighted,zlo,zhi,tlo,thi,lg,nlo,nhi,derivative,fixed,moving_only,phase):
    val=0.
    diff=0.
    for a in range(len(gs)):
        ga,gb,gw=gs[a]
        for b in range(len(gs)):
            ha,hb,hw=gs[b]
            for i in range(energies.shape[2]):
                for j in range(i+1):
                    dl=zlo/(gb*hb*2.**j)
                    el=zlo/(gb*hb*2.**i)
                    di=min(1.,.5+1/dl)
                    ei=min(1.,.5+1/el)
                    q=2.**(i+j)
                    kinv=zhi**2/(nlo*tlo*ga*q)
                    ktop=nhi*thi*gb*q/zlo**2
                    spec=paley(ktop,kinv,dl,el)
                    rev=paley(ktop,kinv,el,dl)
                    old=di*(1/el+32*nhi*thi*gb**3*hb**2*q*q/zlo**4*ei)
                    old+=4*lg*(kinv+32*ei/dl)
                    op=min(di*ei,old,spec,rev)
                    smooth=min(1.,derivative/(nlo*ga*q))
                    v=sqrt(energies[a,b,i]*energies[a,b,j]*op)*(smooth if moving_only else (min(1.,fixed/(nlo*ga*q))+smooth)/2)
                    der=sqrt(weighted[a,b,i]*weighted[a,b,j]*op)*phase*nhi*gb*q
                    fac=gw*hw/q*(1 if i==j else 2)
                    val+=fac*v
                    diff+=fac*min(v,der)
    return val,diff



def sieve_remainder(l,cmax,K,z,G,order,f0,osc,rough_area,moving_only,energy,inside=None,poisson=False):
    r=arb("1e-6");pi=arb.pi()
    ps=arb(1)
    for p in range(2,1001):
        if fmpz(p).is_prime():ps*=1+arb(2)/(p*(p-1))
    ps*=arb(".002").exp()
    blocks=34;trunc=2**24
    gs=groups(trunc)
    assert len(gs)**2*blocks*(blocks+1)/2<2**23
    lam=lambdas(G,z,blocks)
    if energy:
        from extras.weight_energy import squarefree_groups,factors,zero_frequency
        blocks=44 if poisson else 38;trunc=2**40 if poisson else 2**32
        gs=squarefree_groups(trunc)
        assert len(gs)**2*blocks*(blocks+1)//2<2**24
        en,weighted=factors(gs,blocks,G,z,z)[:2]
        ps=zero_frequency(z,z)
    tail=(1+arb(2).zeta())/trunc+2*arb(2).zeta()**2/2**blocks
    err=arb(0) if poisson else (ps/G)**2/(order+1)
    factor=K*(r-l).exp()*z**2/(2*pi*f0)*osc
    phase=pi*(cmax+r).exp()/K/z**2*rough_area/f0
    assert 1<=order<=(2**52 if poisson else 2**24) and 0<z and z<arb(2)**80
    # n<=2^24, g<=2^32 and i+j<=74. The unsmoothed cap is exactly one.
    fixed_up=upper(K*(r-l).exp()*z**2*(2+inside/K)/(2*pi*inside)) if inside is not None else 2.**150
    def absolute_groups():
        n=1
        while n<=order:
            last=min(order,max(n,5*n//4))
            coef=2*(arb(last+1).digamma()-arb(n).digamma())/pi
            yield n,last,coef
            n=last+1
    if poisson:
        assert moving_only or inside is not None
        envelope=factor if moving_only else (factor+arb(fixed_up))/2
        err+=2/pi*(ps/G)**2*envelope/order
    for n,last,multiplier in (absolute_groups() if poisson else frequencies(order,True,ctx.prec)):
        args=(lower(z),upper(z),lower((l-r).exp()),upper((cmax+r).exp()),
              upper(1+z.log()),n,last,upper(factor),fixed_up,moving_only)
        if energy:
            val,diff=block_energy(gs,en,weighted,*args,upper(phase))
            assert 0<diff<=val<1
            fejer=arb(0) if poisson else arb(2*(last-n+1))/(order+1)*(1-arb(last+n)/(2*(order+1)))
            coeff=fejer*arb(val)+(multiplier-fejer)*arb(diff)
            assert fejer>=0 and multiplier>fejer
        else:
            val=block_sum(gs,lam,*args)
            assert 0<val<1
            coeff=multiplier*arb(val)
        tailfactor=arb(1).min(envelope/n) if poisson else arb(1)
        err+=coeff*(1+arb("1e-7"))+multiplier*tail*tailfactor
    return err,factor


def first_charge(lo,hi,size,ratio,order,cell_bounds,location_hi="115.4",energy=False,inside_width="0",poisson=False,modulus=1,remainder_override=None,sharp_variation=False,physical_terms=False):
    """Return former first-pair upper charge minus new candidate upper charge."""
    l,h=arb(lo),arb(hi)
    pi=arb.pi();r=arb("1e-6");K=arb(H+size)
    cmax=h+(4*(-l/4).exp()).log1p()/2
    a=(1-arb("1e-12"))*K*(4*(-h/4).exp()).log1p()/2
    width=2*(pi-a);f0=a.sin()/(2*a);mass=pi*a.sin()/a
    assert l-r>arb("114.98") and cmax+r<arb(location_hi) and 2*pi/K<r
    assert 0<a and a<pi and order>=32
    # These fixed weights do not depend on either integration variable.
    z=rational(Fraction(ratio))*((l-K.log())/2).exp()
    G=z.log()+arb("1.331")
    remainder_fn=sieve_remainder
    if modulus>1:
        from odd_sieve import denominator
        from grouped_lobes import remainder
        from functools import partial
        G=denominator(z,modulus)
        remainder_fn=partial(remainder,modulus=modulus)
    if remainder_override is not None:remainder_fn=remainder_override
    assert z<(l-r).exp() and arb("1.33258")-arb("2.44")/z.sqrt()>arb("1.331")
    rough_area=f0
    for j in range(1,128):
        w=width*j/128
        rough_area+=(a.cos()-(a+w).cos())/(w*(2*a+w))
    rough_area*=width/128
    if sharp_variation:
        rough_area-=width*f0/256
        rough_area+=width**3/(144*128**2)
    inside=rational(Fraction(inside_width))
    assert inside>=0 and inside<a
    rough_area+=f0*inside/2
    osc=arb(1)/3+width*(arb(1)/12+1/(6*K))
    if sharp_variation:
        from lobe_variation import first
        osc=osc.min(first(a,width,K,f0))
    err,factor=remainder_fn(l,cmax,K,z,G,order,f0,osc,rough_area,False,energy,inside if inside>0 else None,poisson)
    # Use a common enclosure of the trapezoid integral so that
    # the normalization in the older charge cancels in the difference.
    base=2*(cmax+r)*(r/2).exp()/mass
    slope_new=base*r.exp()*int(fmpz(modulus).euler_phi())/(modulus*G)
    cost_new=base*K*(-l).exp()*f0*z**2*err+slope_new*f0*inside/2
    if physical_terms:
        area=width/8192*(f0/2+sum((a.cos()-(a+width*i/8192).cos())/
                      ((width*i/8192)*(2*a+width*i/8192)) for i in range(1,8192)))
        return area+arb(0,width**3/(144*8192**2)),slope_new,cost_new
    sm=(l-r).exp()/K;sp=(cmax+r).exp()/K
    cut=[arb(i).exp() for i in range(83,90)]
    def line(s,eta):
        v=l-K.log()+arb(eta)+s.log()
        assert v>4 and K.log()-arb(eta)-s.log()+r>2
        B=2*(l+r)*(r/2).exp()/(mass*v*v)
        return B*r.exp()*(v-1), B*s
    slope=line(arb("1.55"),"1.16613")[0]
    offset=arb(0);old=f0
    left_area=arb(0);right_area=arb(0)
    for i in range(8192):
        wl,wr=width*i/8192,width*(i+1)/8192
        new=(a.cos()-(a+wr).cos())/(wr*(2*a+wr)) if i+1<8192 else arb(0)
        dh=old-new
        assert dh>0
        s=(wl+wr)/2
        m,t=line(s,"1.16613")
        offset+=2*dh*(t+((m-slope)*wl).max((m-slope)*wr))
        yl,yh=sm*wl,sp*wr
        if yl>cut[0] and yh<cut[-1]:
            tag=min((cell_bounds[j] for j in range(6)
                     if not (yh<cut[j] or yl>cut[j+1])),key=Fraction)
            mn,tn=line(s,tag)
            offset-=2*dh*(t-tn+((m-mn)*wl).min((m-mn)*wr)).max(arb(0))
        left_area+=old*width/8192
        right_area+=new*width/8192
        old=new
    area=(right_area+left_area)/2 + arb(0,width**3/(144*8192**2))
    gain=(2*slope-slope_new)*area+offset-cost_new
    return gain, slope_new*area+cost_new, err, factor


def high_transfer(lo,hi):
    """Lower the fixed height-charge cap on later slabs, pointwise in height."""
    l,h=arb(lo),arb(hi)
    l0,h0=arb("115.040500"),arb("115.041000")
    assert Fraction(lo)>=Fraction("115.040500") and Fraction(hi)>=Fraction("115.041000")
    size=16000000000;K=arb(H+size);Q=arb(10000)
    def radius(t):
        return (1-arb("1e-12"))*K*(4*(-t/4).exp()).log1p()/2
    a,a0=radius(h),radius(h0)
    v=a0*size/K
    assert arb.pi()/2<a and a0<arb.pi() and 0<v and v<arb.pi()/2
    assert v.sin()+2*Q*a0/(arb.pi().sqrt()*K)<1
    ratio=(-(l-l0)/8).exp()*(a/a0)*(a0.sin()/a.sin())*(v/v.sin())
    return arb(".005937108818")*(1-ratio.min(arb(1)))


if __name__=="__main__":
    import argparse
    from dilated_cover import TABLE,WEIGHTED
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("--lo",default="115.13")
    arg.add_argument("--hi",default="115.132")
    arg.add_argument("--size",type=int,default=-206000)
    arg.add_argument("--ratio",default="7")
    arg.add_argument("--order",type=int,default=8192)
    arg.add_argument("--gain")
    arg.add_argument("--energy",action="store_true")
    arg.add_argument("--older-table",action="store_true")
    arg.add_argument("--complete",action="store_true")
    arg.add_argument("--secondary",action="store_true")
    arg.add_argument("--secondary-ratio")
    arg.add_argument("--inside-width",default="0")
    arg.add_argument("--poisson",action="store_true")
    arg.add_argument("--transfer",action="store_true")
    arg.add_argument("--check",action="store_true")
    a=arg.parse_args();ctx.prec=192
    table=tuple(b[2] for b in (TABLE if a.older_table else WEIGHTED))
    vals=first_charge(a.lo,a.hi,a.size,a.ratio,a.order,table,energy=a.energy,inside_width=a.inside_width,poisson=a.poisson)
    print("gain, new first charge, Fourier error/z^2, derivative factor",*(v.str(16) for v in vals))
    if a.gain is not None:assert vals[0]>arb(a.gain)

    savings=vals[0].max(arb(0))
    if a.secondary:
        from secondary_lobes import charge
        extra=charge(a.lo,a.hi,a.size,a.secondary_ratio or a.ratio,a.order,table,a.energy,poisson=a.poisson)
        print("secondary saving", extra.str(18),flush=True)
        savings+=extra.max(arb(0))
    if a.complete:
        from cover import full
        high=".005937108818" if a.size==16000000000 else None
        total=full(a.lo,a.hi,a.size,"auto",high,table,"115.4")[0]-savings
        if a.transfer:
            assert high is not None
            saving=high_transfer(a.lo,a.hi)
            print("high transfer gain",saving.str(15),flush=True)
            total-=saving
        print("Complete cost",total.str(18),flush=True)
        if a.check:assert total<1
    else:assert not a.check
