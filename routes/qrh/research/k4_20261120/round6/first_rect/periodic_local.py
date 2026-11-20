"""A finite frozen fourth mean for the two periodic branches of the asymmetric AFE."""
from functools import lru_cache
from math import gcd
from itertools import product
from pathlib import Path
import sys
import numpy as np
from flint import arb,ctx
research=Path(__file__).resolve().parents[2]
for p in ("round5/low","round5/left","round6/phase"):
    sys.path.insert(0,str(research/p))
from periodic_fourth import period,diagonal,fourth
from center_fold import folded
from prefix_fourth import half_cost


@lru_cache(maxsize=1000)
def mass(q,dual,Y):
    w=period(q,dual)
    # Restricted coprimality in the two gcd parameters is an upper bound.
    ds={1:1}
    for p in (2,3,5,7,11,13):
        ds.update({p*k:-sg for k,sg in ds.items()})
    vmax=max(map(abs,w))
    assert 2*vmax**4*Y**2*(1+Y.bit_length())<2**63
    result=0
    for v0,sg in ds.items():
        nmax=Y//v0
        if not nmax:continue
        v=v0%q
        # For max(i,j)=i, group j by residue modulo q. The entire k sum
        # has period q and length floor(nmax/i), independent of j.
        gram=0
        for ir in range(q):
            i=np.arange(ir if ir else q,nmax+1,q,dtype=np.int64)
            if not i.size:continue
            m=nmax//i
            cycles,resid=np.divmod(m,q)
            for jr in range(q):
                numbers=[w[(v*ir*k)%q]*w[(v*jr*k)%q] for k in range(1,q+1)]
                prefix=np.array([0]+list(np.cumsum(numbers)),dtype=np.int64)
                inner=cycles*int(prefix[-1])+prefix[resid]
                first=jr if jr else q
                copies=2*((i+q-first)//q)-(ir==jr)
                gram+=int((copies*(inner*inner)).sum())
        result+=sg*gram
    assert result>=0
    return result


def short_norm(scale,C,J,q,dual,power,with_prefix=False):
    pi=arb.pi()
    y0=scale*(C/(2*pi)).sqrt()
    y=int(y0.floor().unique_fmpz())
    assert y>=96**2
    raw=diagonal(q,dual,96,ctx.prec)(arb(y).log())
    from exact_harm import uniform_harm
    bucket=((y+131071)//131072)*131072
    raw=raw.min(uniform_harm(q,dual,bucket,ctx.prec))
    unit=arb(q).sqrt() if dual else arb(1)
    eu=arb(mass(q,dual,y))
    # Product frequencies are units in the forward branch.
    # For q=30 the density mode has smaller Hilbert defect.
    args=(arb(1),pi) if dual else ((arb(1),pi/3) if q==6 else (arb("1.082"),pi*8/q))
    assert q in (6,30)
    mn=folded(J*raw,eu,J,arb(1),*args)
    if power.is_zero():
        center=mn**(arb(1)/4)/unit
        return (center,arb(0),y) if with_prefix else center
    yl=y0*(1-J/C)**power; yh=y0*(1+J/C)**power
    left=int(yl.lower().floor().unique_fmpz())+1
    right=int(yh.upper().floor().unique_fmpz())
    # Squared frequency norm of the moving prefix. Weight max bounds every
    # diagonal, and every unequal-product term before its absolute estimate.
    vmax=max(map(abs,period(q,dual)))
    moving=(half_cost(left,y,J)+half_cost(y+1,right,J))/2
    from prefix_energy import local_half
    exact=(local_half(left,y,J,q,dual)+local_half(y+1,right,J,q,dual))/2
    prefix=(vmax*moving**(arb(1)/4)).min(exact**(arb(1)/4))
    # Pointwise absolute prefix uses the density-weighted periodic counts.
    weights=list(map(abs,period(q,dual))); total=sum(weights)
    def abspref(n):
        c,r=divmod(n,q)
        return c*total+sum(weights[i%q] for i in range(1,r+1))
    amp=max(abspref(y)-abspref(left-1),abspref(right)-abspref(y))
    prefix=prefix.min(amp*J**(arb(1)/4)/yl.sqrt())
    result=(mn**(arb(1)/4)+prefix)/unit
    return (result,prefix/unit,y) if with_prefix else result


def effective_mass(size,q,alpha,panels,power=arb("0.5")):
    H=arb(3000175332800);D=arb(size);R=D/2;C=H+R
    pi=arb.pi();v=arb("1.01");M=2048;outer=arb("1.012")
    J=outer*v*R;step=2*J/panels;B=C+v*R;p=1+4/B.log()
    root=arb(q).sqrt();a=root*alpha;b=root/alpha
    assert q/a*(2*pi/1000).sqrt()<=1 and q/b*(2*pi/1000).sqrt()<=1
    K=16*(2*pi)**(arb(1)/4)*sum((arb(d)/a).sqrt().max((a/d).sqrt())/arb(d).sqrt()
           for d in range(1,q+1) if q%d==0)
    assert C-J>1000
    core=arb(0)
    for i in range(panels):
        cc=C-J+step*(arb(i)+arb(1)/2);half=step/2
        fwd,ef,yf=short_norm(a,cc,half,q,False,power,True)
        dual,ed,yd=short_norm(b,cc,half,q,True,1-power,True)
        from local_harmonic import bound
        mixed=bound(cc,half,q,a,b,power)
        val=(fwd+dual).min((fwd**2+dual**2+(2*(fwd**2*dual**2+mixed)).sqrt()).sqrt())
        if (1-power).is_zero():
            from frozen_mix import gram
            energy,harm=gram(q,yf,yd,ctx.prec)
            z0=folded(half*harm,energy,half,arb(1),arb(1),pi)/q
            product=(z0.sqrt()+ef*dual)**2
            product=product.min(fwd**2*dual**2)
            val=val.min(((fwd**4+dual**4+2*product).sqrt()+(2*(product+mixed)).sqrt()).sqrt())
        # The pointwise AFE has a(t) shifted by (t/cc)^(power-1/2).
        variation=((1-half/cc)**(-abs(power-arb(".5")))).sqrt()
        assert a.min(b)*((cc-half)/(2*pi)).sqrt()/variation**2>q
        val+=K*variation*(half/(cc-half))**(arb(1)/4)
        core+=val**4
    tail=(fourth(B.log(),q,alpha)*B*B.log()**4)*M/(M-p)*outer**(p-M)
    return core+tail


if __name__=="__main__":
    ctx.prec=192
    for q in (6,30):
        for dual in (False,True):
            w=period(q,dual);Y=22
            d=sum(sum(w[(i*k)%q]*w[(j*k)%q] for k in range(1,Y//max(i,j)+1))**2
                for i in range(1,Y+1) for j in range(1,Y+1) if gcd(gcd(i,j),30030)==1)
            assert d==mass(q,dual,Y)
    size=int((arb(3000175332800)*(arb(1)/4).expm1()).ceil().unique_fmpz())
    q=int(sys.argv[1]) if len(sys.argv)>1 else 6
    alpha=arb(sys.argv[2]) if len(sys.argv)>2 else arb(1)
    for panels in ([int(sys.argv[3])] if len(sys.argv)>3 else [1,2,3,4,6,8]):
        print(q,alpha.str(4),panels,effective_mass(size,q,alpha,panels,arb(sys.argv[4]) if len(sys.argv)>4 else arb(".5")).str(16),flush=True)
