"""A compact spatial autocorrelation with a nonnegative centered spectrum."""
from functools import lru_cache
from flint import arb,ctx
import height_profile as spatial

UNIFORM=(1,)
SHOULDERS=(5,)*18+(6,6)


def peak(heights):
    n=len(heights)
    return arb(2*n*sum(h*h for h in heights))/sum(heights)**2


@lru_cache(maxsize=8)
def spectrum(heights,step,tail,precision):
    n=len(heights)
    assert all(h>0 for h in heights) and ctx.prec==precision and step%2==0
    w=arb(1)/(4*n);mass=sum(heights)
    jumps=[(i+1,arb(h-(heights[i+1] if i+1<n else 0))/(w*mass))
           for i,h in enumerate(heights) if i+1==n or h!=heights[i+1]]
    v=sum(abs(c) for _,c in jumps)
    v1=sum(abs(c)*j*w for j,c in jumps)
    v2=sum(abs(c)*(j*w)**2 for j,c in jumps)
    e2=(v1**2+v*v2)/(4*step**2)
    moment=2*w*w*sum(h*(3*j*j+3*j+1) for j,h in enumerate(heights))/(3*mass)
    e1=moment/(8*step**2)
    def squared_numerator(k):
        return sum(c*(j*w*k/step).sin() for j,c in jumps)**2
    a=squared_numerator(step//2)
    raw=[]
    for k in range(step//2,tail*step):
        b=squared_numerator(k+1)
        lo=arb(k)/step;hi=arb(k+1)/step
        raw.append((a/lo**2).max(b/hi**2)+e1)
        raw[-1]=raw[-1].min((a.max(b)+e2)/lo**2)
        a=b
    return raw,v*v


def cap(d,heights=UNIFORM,step=256,tail=192):
    raw,variation=spectrum(heights,step,tail,ctx.prec)
    unit=spatial.polygon.SCALE;ceil=spatial.polygon._ceiling
    last=rest=ceil(variation*unit/tail**2)
    ticks=[unit]*(tail*step+1)
    ticks[-1]=last
    for k in range(tail*step-1,step//2-1,-1):
        x=arb(k)/step
        upper=(raw[k-step//2]+d/2).min(1).min(variation/x**2)
        last=max(last,ceil(upper*unit))
        ticks[k]=last
    def value(y):
        if y>tail:return arb(rest)/unit*(tail/y)**2
        k=int((y*step).lower().floor().unique_fmpz())
        return arb(ticks[max(0,min(k,tail*step))])/unit
    return value


if __name__=="__main__":
    ctx.prec=144
    for heights in (UNIFORM,SHOULDERS):
        val=cap(arb("1e-13"),heights)
        print("peak",peak(heights).str(12),"spectral caps",
              *(val(arb(y)).str(9) for y in (2,4,8,12,50,192,240)),flush=True)
