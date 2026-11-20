"""Absolute Fourier groups for directly smoothed Selberg test functions."""
from fractions import Fraction
from math import gcd,isqrt,sqrt
from functools import lru_cache
from types import FunctionType
from functools import partial
from flint import arb,ctx,fmpz
from numba import njit,prange
import numpy as np
import weighted_lobe as base
import secondary_lobes as other
from extras.weight_energy import paley, squarefree_groups,factors,zero_frequency
from bilinear import lower,upper,lambdas,rational


@njit
def unit_paley(K,inv,D,F,modulus,grouped,colors,rational_colors,majorant=False):
    best=1.e200
    for b,c in ((.03125,1.001),(.125,1.014),(.25,1.06),(.5,1.235),(.75,1.627)):
        x=(K+b)/D
        y=1/(b*F)
        sample=.5+x
        frequencies=max(inv,y) if grouped else max(inv/2,y)
        for size,slope in colors:
            sample=min(sample,slope+size*x)
            if not grouped:frequencies=min(frequencies,max(slope*inv,size*y))
        if grouped:
            for size,slope in rational_colors:
                frequencies=min(frequencies,max(slope*inv,size*y))
        best=min(best,c*sample*frequencies)
    if majorant:
        # Use the interval majorant of mass 1+1/b, with b cut off at
        # the within-class separation. Its square root is a spectral factor.
        for b in (1.,4.,16.,128.,1024.,sqrt(D+K)):
            x=(K+b)/D
            y=1/(b*F)
            sample=.5+x
            freq=1/F+(max(inv,y) if grouped else max(inv/2,y))
            for size,slope in colors:
                sample=min(sample,slope+size*x)
                if not grouped:freq=min(freq,size/F+max(slope*inv,size*y))
            if grouped:
                for size,slope in rational_colors:
                    freq=min(freq,size/F+max(slope*inv,size*y))
            best=min(best,sample*freq)
    return best


@njit(parallel=True)
def multi_band(gs,E,weights,lam,zlo,zhi,tlo,thi,lg,nlo,nhi,osc,fixed,sec,phase,mass,modulus,colors,cover,twice,rational_colors,sparse,move_boundary,move_twice,linear=False):
    total=0.
    on_cap=0.;on_variation=0.;on_area=0.
    for a in prange(len(gs)):
        ga,gb,gw=gs[a]
        for b in range(len(gs)):
            ha,hb,hw=gs[b]
            if E[a,b,0]==0 and E[a,b,-1]==0 and not E[a,b].any():continue
            for i in range(E.shape[2]):
                if zhi*1.00000001<ga*ha*2.**i:continue
                for j in range(i+1):
                    D=zlo/(gb*hb*2.**j)
                    F=zlo/(gb*hb*2.**i)
                    d=min(1.,.5+1/D)
                    f=min(1.,.5+1/F)
                    q=2.**(i+j)
                    inv=zhi**2/(nlo*tlo*ga*q)
                    k=nhi*thi*gb*q/zlo**2
                    old=d*(1/F+32*nhi*thi*gb**3*hb**2*q*q/zlo**4*f)
                    old+=4*lg*(inv+32*f/D)
                    op=min(d*f,old,paley(k,inv,D,F),paley(k,inv,F,D))
                    if modulus>1:
                        dx=min(d,.25+1/D,cover[0]+cover[1]/D)
                        dy=min(f,.25+1/F,cover[0]+cover[1]/F)
                        op=min(op,dx*dy,unit_paley(k,inv,D,F,modulus,False,colors,rational_colors,sparse>=2),
                               unit_paley(k,inv,F,D,modulus,False,colors,rational_colors,sparse>=2))
                    ux,uy=E[a,b,j],E[a,b,i]
                    wx,wy=weights[a,b,j],weights[a,b,i]
                    if modulus>1:
                        ux=min(ux,dx*lam[j]**2)
                        uy=min(uy,dy*lam[i]**2)
                        wx=min(wx,4*dx*lam[j]**2)
                        wy=min(wy,4*dy*lam[i]**2)
                    common=sqrt(ux*uy*op)
                    shifted=sqrt(wx*wy*op)
                    plain=common;high=common;low=shifted
                    if nlo!=nhi:
                        kinv=zhi**2/(tlo*ga*q)
                        gtop=(2*nhi-nlo)*thi*gb*q/zlo**2
                        cf=paley(gtop,kinv,D,F);cd=paley(gtop,kinv,F,D)
                        if modulus>1:
                            cf=min(cf,unit_paley(gtop,kinv,D,F,modulus,True,colors,rational_colors,sparse>=2))
                            cd=min(cd,unit_paley(gtop,kinv,F,D,modulus,True,colors,rational_colors,sparse>=2))
                        ax=lam[j]*lam[j];ay=lam[i]*lam[i]
                        if sparse:
                            ax*=min(1.,cover[0]+cover[1]*nhi/D)
                            ay*=min(1.,cover[0]+cover[1]*nhi/F)
                        plain=min(plain,sqrt(min(ux*cf*(uy*mass[2]+ay*mass[3]),
                                                 uy*cd*(ux*mass[2]+ax*mass[3]))))
                        high=min(high,sqrt(min(ux*cf*(uy*mass[4]+ay*mass[5]),
                                               uy*cd*(ux*mass[4]+ax*mass[5]))))
                        low=min(low,sqrt(min(wx*cf*(wy*mass[0]+4*ay*mass[1]),
                                             wy*cd*(wx*mass[0]+4*ax*mass[1]))))
                        if sparse>=3:
                            plain=min(plain,sqrt(min(ux*cf*(uy*mass[10]+ay*mass[11]),
                                                     uy*cd*(ux*mass[10]+ax*mass[11]))))
                            high=min(high,sqrt(min(ux*cf*(uy*mass[12]+ay*mass[13]),
                                                   uy*cd*(ux*mass[12]+ax*mass[13]))))
                            low=min(low,sqrt(min(wx*cf*(wy*mass[8]+4*ay*mass[9]),
                                                 wy*cd*(wx*mass[8]+4*ax*mass[9]))))
                    right=min(plain,high*osc*mass[6]/(ga*q))
                    if move_twice>0:
                        right=min(right,high*mass[6]/(ga*q)*(move_boundary+move_twice/(nlo*ga*q)))
                    left=min(plain,high*fixed*mass[6]/(ga*q))
                    if twice>0:
                        left=min(left,high*twice*mass[6]/(nlo*(ga*q)**2))
                    val=min(right if sec else (right+left)/2,low*phase*gb*q*mass[7])
                    total+=gw*hw*val/q*(1 if i==j else 2)
                    if linear:
                        weight=gw*hw/q*(1 if i==j else 2)
                        spatial=low*phase*gb*q*mass[7]
                        if spatial<=(right if sec else (right+left)/2):
                            on_area+=weight*spatial
                        else:
                            wp=weight if sec else weight/2
                            if plain<=high*osc*mass[6]/(ga*q):on_cap+=wp*plain
                            else:on_variation+=wp*right
                            if not sec:on_cap+=wp*left
    return total,on_cap,on_variation,on_area


def unit_spacing(modulus):
    units=[j for j in range(modulus) if gcd(j,modulus)==1]
    m=len(units)
    extended=units+[modulus+j for j in units]
    out=[];best=Fraction(2)
    for k in range(1,m+1):
        distance=min(extended[i+k]-x for i,x in enumerate(units))
        if Fraction(k,distance)<best:
            out.append((k,upper(arb(k)/distance)))
            best=Fraction(k,distance)
    count=high=low=0
    for j in range(1,modulus+1):
        low=min(low,modulus*count-m*j)
        count+=int(gcd(j,modulus)==1)
        high=max(high,modulus*count-m*j)
    return np.array(out,dtype=np.float64), (upper(arb(m)/(2*modulus)),upper(arb(high-low)/modulus))


@lru_cache(None)
def progression(modulus):
    m=int(fmpz(modulus).euler_phi())
    count=high=low=0
    for j in range(1,modulus+1):
        low=min(low,modulus*count-j*m)
        count+=int(gcd(j,modulus)==1)
        high=max(high,modulus*count-j*m)
    return Fraction(m,modulus),Fraction(high-low,modulus)


def moments(n,last,modulus=1,sieve=1,sparse=False):
    N=arb(n);J=arb(last);length=last-n+1
    span=arb(last-n)/(2 if sparse and modulus%2==0 else 1)
    h=arb(last+1).digamma()-N.digamma()
    # A simple decreasing integral safely avoids cancellation of a tiny interval
    # in the large harmonic-square ranges.
    h2=(1/N**2+1/N-1/J).min(arb(length)/N**2)
    count=length
    if sieve>1:
        count=0;h=h2=arb(0)
        for d in range(1,sieve+1):
            if sieve%d:continue
            mu=int(fmpz(d).moebius_mu())
            a,b=1+(n-1)//d,last//d+1
            if a==b:continue
            count+=mu*(b-a)
            h+=mu*(arb(b).digamma()-arb(a).digamma())/d
            h2+=mu*(arb(2).zeta(arb(a))-arb(2).zeta(arb(b)))/d**2
        assert count>0 and h>0 and h2>0
    if last<=4096:
        rows=[k for k in range(n,last+1) if gcd(k,sieve)==1]
        other=[sum((arb(int(fmpz(d).euler_phi()))/d for d in range(2,k+1)
                    if k%d==0 and gcd(d,modulus)==1),arb(0)) for k in rows]
        sums=[sum((arb(k)**(-p) for k in rows),arb(0)) for p in range(5)]
        out=[]
        for p in (0,1,2):
            second=sums[2*p]/sums[p]**2
            kernel=[arb(k)**(-2*p-1) for k in rows]
            second+=span*sum(kernel)/sums[p]**2
            extra=sum((w*v for w,v in zip(kernel,other)),arb(0))
            out.extend([upper(second),upper(span*extra/sums[p]**2)])
        h2=sums[2]
    else:
        divsum=2*(length*(1+J.log()/2)+J.sqrt())
        root=isqrt(last);S=arb(root)
        eta,disc=map(rational,progression(modulus))
        es,ds=map(rational,progression(sieve))
        # Every factorization k=r*d has r<=sqrt(last) or d<=sqrt(last).
        # The unit restriction on r applies to both triangles.
        harmonic=eta*(1+S.log())+disc
        Hs=1+S.log() if sieve==1 else es*(1+S.log())+ds
        divsum=divsum.min(length*(es*harmonic+eta*Hs)+ds*(eta*S+disc)+disc*(es*S+ds))
        divsum-=count
        out=[]
        for p in (0,1,2):
            ratio=(J/N)**(2*p)/count
            out.extend([upper(ratio*(1+span/N)),upper(ratio*span*divsum/(count*N))])
    out.extend([upper(h2/h),upper(arb(count)/h)])
    if sparse>=3:
        from rational_collisions import collision_masses
        eta,disc=map(rational,progression(modulus))
        out.extend(collision_masses(n,last,modulus,sieve,eta,disc))
    return h,np.array(out)


def remainder(l,cmax,K,z,G,order,f0,osc,rough_area,moving_only,energy,inside=None,poisson=False,modulus=1,exact_harmonics=False,triangle="0",sparse=False,moving_parts=None,linear=False):
    assert energy and poisson and (moving_only or inside is not None)
    assert modulus==1 or (modulus%2==0 and 2310%modulus==0)
    pi=arb.pi();r=arb("1e-6");trunc=2**40;blocks=44
    gs=squarefree_groups(trunc)
    assert len(gs)**2*blocks*(blocks+1)//2<2**23
    if modulus>1:
        from odd_sieve import unit_factors,unit_groups,harmonics,suprema
        gs=unit_groups(gs,modulus)
        en,weighted=unit_factors(gs,blocks,G,z,modulus)[:2]
        parts=[(d,w,1) for d,w in harmonics(modulus)]
        if exact_harmonics:
            odd=modulus//2
            parts=[(modulus//m,arb(int(fmpz(m).euler_phi()))/m,odd//m)
                   for m in range(1,odd+1) if odd%m==0]
        lam=suprema(G,z,blocks,modulus)
    else:
        en,weighted=factors(gs,blocks,G,z,z)[:2]
        parts=[(1,arb(1),1)]
        lam=lambdas(G,z,blocks)
    konst=zero_frequency(z,z,modulus)
    factor=K*(r-l).exp()*z**2/(2*pi*f0)*osc
    move_boundary=move_twice=arb(0)
    if moving_parts is not None:
        first,second=moving_parts
        frequency_unit=K*(r-l).exp()*z**2/(2*pi)
        move_boundary=frequency_unit*first/f0
        move_twice=frequency_unit**2*second/f0
    fixed=K*(r-l).exp()*z**2*(2+inside/K)/(2*pi*inside) if inside is not None else arb(0)
    twice=arb(0)
    if triangle!="0" and not moving_only:
        fraction=rational(Fraction(triangle))
        assert 0<fraction and fraction<=arb(1)/2 and inside>0
        fixed=K*(r-l+inside/K).exp()*z**2/(pi*inside*(1-fraction))
        twice=fixed**2*(1-fraction)/fraction
    phase=pi*(cmax+r).exp()/K/z**2*rough_area/f0
    envelope=factor if moving_only else (factor+fixed)/2
    initial=2/pi*(konst/G)**2/order*sum(d*w for d,w,_ in parts)
    err=initial*envelope
    if linear:
        assert moving_parts is None and triangle=="0" and f0==1
        split=(arb(0) if moving_only else fixed/2,factor if moving_only else factor/2,arb(0))
        coeff=[initial*v for v in split]
    tail=(1+arb(2).zeta())/trunc+2*arb(2).zeta()**2/2**blocks
    n=1
    colors,cover=unit_spacing(modulus)
    while n<=order:
        last=min(order,max(n,5*n//4))
        cache={}
        for dilation,weight,sieve in parts:
            first=n;end=last
            while first<=end and gcd(first,sieve)!=1:first+=1
            while first<=end and gcd(end,sieve)!=1:end-=1
            if end<first:continue
            if sieve not in cache:
                harmonic,stat=moments(first,end,modulus,sieve,sparse)
                divisors=[s for s in range(1,sieve+1) if sieve%s==0] if sparse else [1]
                rational_colors=np.array([(int(fmpz(s).euler_phi()),upper(arb(int(fmpz(s).euler_phi()))/s))
                                          for s in divisors],dtype=np.float64)
                cache[sieve]=harmonic,stat,rational_colors
            harmonic,stat,rational_colors=cache[sieve]
            val,*charged=multi_band(gs,en,weighted,lam,lower(z),upper(z),lower((l-r).exp()/dilation),
                           upper((cmax+r).exp()/dilation),upper(1+z.log()),first,end,upper(factor*dilation),
                           upper(fixed*dilation),moving_only,upper(phase/dilation),stat,modulus,colors,cover,
                           upper(twice*dilation**2),rational_colors,sparse,
                           upper(move_boundary*dilation),upper(move_twice*dilation**2),linear)
            assert 0<val<1
            err+=weight*2/pi*harmonic*(arb(val)*(1+arb("1e-7"))+tail*arb(1).min(dilation*envelope/n))
            if linear:
                assert all(x>=0 for x in charged) and abs(sum(charged)-val)<=1e-7*val
                rest=[v*dilation/n for v in split] if dilation*envelope<n else [arb(1),arb(0),arb(0)]
                for j in range(3):
                    coeff[j]+=weight*2/pi*harmonic*(arb(charged[j])*(1+arb("1e-7"))+tail*rest[j])
        n=last+1
    return (coeff if linear else err),factor


def replace(fn):
    namespace=dict(fn.__globals__);namespace['sieve_remainder']=remainder
    return FunctionType(fn.__code__,namespace,fn.__name__,fn.__defaults__)


if __name__=="__main__":
    import argparse
    from cover import full
    from dilated_cover import WEIGHTED
    ctx.prec=192;ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--lo",default="115.29");ap.add_argument("--hi",default="115.305")
    ap.add_argument("--ratio",default="110");ap.add_argument("--secondary-ratio",default="130")
    ap.add_argument("--inside",default=".0001");ap.add_argument("--qrh",action="store_true")
    ap.add_argument("--location-hi",choices=("115.4","116"),default="115.4")
    ap.add_argument("--check",action="store_true");ap.add_argument("--first-only",action="store_true")
    ap.add_argument("--odd",action="store_true")
    ap.add_argument("--exact-harmonics",action="store_true")
    ap.add_argument("--sharp-variation",action="store_true")
    ap.add_argument("--triangle",default="0")
    ap.add_argument("--sparse",action="store_true")
    ap.add_argument("--lobes",type=int,default=64)
    ap.add_argument("--order",type=int,default=2**48)
    ap.add_argument("--modulus",type=int,default=1)
    a=ap.parse_args()
    modulus=2 if a.odd else a.modulus
    provider=partial(remainder,modulus=modulus,exact_harmonics=a.exact_harmonics,triangle=a.triangle,sparse=a.sparse)
    assert not a.odd or a.modulus in (1,2)
    table=tuple(t[2] for t in WEIGHTED)
    if a.location_hi=="116":
        # Each of the six location-116 additions in extras/GROUPS.md is >8.
        assert max(map(Fraction,table))<8
    size=16000000000 if a.qrh else -206000;order=a.order
    primary=base.first_charge(a.lo,a.hi,size,a.ratio,order,table,location_hi=a.location_hi,energy=True,
                              inside_width=a.inside,poisson=True,modulus=modulus,remainder_override=provider,sharp_variation=a.sharp_variation)[0]
    print("direct grouped first saving",primary.str(18),flush=True)
    if not a.first_only:
        sc=other.charge(a.lo,a.hi,size,a.secondary_ratio,order,table,True,location_hi=a.location_hi,poisson=True,modulus=modulus,remainder_override=provider,sharp_variation=a.sharp_variation,lobes=a.lobes)
        high=".005937108818" if a.qrh else None
        total=full(a.lo,a.hi,size,"auto",high,table,a.location_hi)[0]-primary.max(arb(0))-sc.max(arb(0))
        if a.qrh:total-=base.high_transfer(a.lo,a.hi)
        print("direct secondary saving",sc.str(15),"total",total.str(18),flush=True)
        if a.check:assert total<1
    else:assert not a.check
