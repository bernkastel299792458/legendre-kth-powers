"""Directional decreasing envelopes of the real centered spatial transform."""
from functools import lru_cache
from flint import arb,ctx
import height_profile as spatial


@lru_cache(maxsize=4)
def tables(step,tail,precision,local=False,heights=None,normalization=None):
    assert precision==ctx.prec
    heights=spatial.NUM if heights is None else heights
    n=len(heights)-1
    net=2*sum(heights)-heights[0]
    total=net if normalization is None else normalization
    assert total>0 and heights[-1]==0
    mass=arb(2*sum(map(abs,heights))-abs(heights[0]))/total
    jumps=[2*(heights[1]-heights[0])]+[2*(heights[k-1]-2*heights[k]+
           (heights[k+1] if k<n else 0)) for k in range(1,n+1)]
    scale=arb((2*n)**2)/total
    variation=scale*sum(abs(x) for x in jumps)
    moment=(mass/6+2*sum(abs(h)*k*k for k,h in enumerate(heights))/arb(total))/(2*n)**2
    curvature=sum(abs(x)*k*k for k,x in enumerate(jumps))/arb(total)
    e1,e2=moment/(8*step**2),curvature/(8*step**2)
    def numerator(k):
        z=2*(arb(k)/(step*2*n)).cos()
        prev=last=arb(0)
        for a in reversed(jumps[1:]):prev,last=z*prev-last+a,prev
        return -scale*(jumps[0]+z*prev/2-last)
    unit=spatial.polygon.SCALE
    ceil=spatial.polygon._ceiling
    top=step*tail
    rest=ceil(variation*unit/tail**2)
    rows=[[rest]*(top+1) for _ in range(2)]
    b=numerator(top)
    for k in range(top-1,step//2-1,-1):
        a=numerator(k);lo,hi=arb(k)/step,arb(k+1)/step
        for sign,ticks in zip((1,-1),rows):
            # For the quotient alternative only a positive numerator matters.
            num=(sign*a).max(sign*b)+e2
            bound=((sign*a/lo**2).max(sign*b/hi**2)+e1).min(num.max(arb(0))/lo**2)
            val=bound.max(arb(0)).min(mass).min(variation/lo**2)
            ticks[k]=ceil(val*unit) if local else max(ticks[k+1],ceil(val*unit))
        b=a
    # On |y|<.5 the real cosine is positive on the whole spatial support.
    for j in range(step//2-1,-1,-1):
        if min(heights)<0 or normalization is not None:
            loss=moment*(arb(j+1)/step)**2/2
            base=arb(net)/total
            for tick,cap in zip(rows,((base+loss).max(0).min(mass),(loss-base).max(0).min(mass)),strict=True):
                cover=ceil(cap*unit)
                tick[j]=cover if local else max(cover,tick[j+1])
        else:
            rows[0][j]=unit
            rows[1][j]=0 if local else rows[1][step//2]
    return rows,rest


def local_caps(lo,hi,step=256,tail=192,heights=None,normalization=None):
    rows,rest=tables(step,tail,ctx.prec,True,heights,normalization)
    unit=spatial.polygon.SCALE
    left=max(0,int((lo*step).lower().floor().unique_fmpz()))
    right=min(step*tail-1,int((hi*step).upper().floor().unique_fmpz()))
    extra=arb(0)
    if not hi<tail:
        extra=arb(rest)/unit*(tail/lo.max(tail))**2
    if left>right:return extra,extra
    return tuple((arb(max(v[left:right+1]))/unit).max(extra) for v in rows)


def caps(step=256,tail=192):
    rows,rest=tables(step,tail,ctx.prec)
    unit=spatial.polygon.SCALE
    def cap(y):
        if y>tail:
            v=arb(rest)/unit*(tail/y)**2
            return v,v
        k=int((y*step).lower().floor().unique_fmpz())
        return tuple(arb(r[max(0,min(k,len(r)-1))])/unit for r in rows)
    return cap


def positive_radius(step=256,tail=192):
    # Independently use a positive lower bound on the numerator's two
    # endpoint values and its curvature to cover the whole first lobe.
    h=spatial.NUM;n=len(h)-1;total=2*sum(h)-h[0]
    moment=(arb(1)/6+2*sum(v*j*j for j,v in enumerate(h))/arb(total))/(2*n)**2
    for k in range(step//2,tail*step):
        low,high=arb(k)/step,arb(k+1)/step
        def transform(x):
            return (h[0]+2*sum(h[j]*(x*j/(2*n)).cos() for j in range(1,n+1)))/total*(x/(4*n)).sinc()**2
        if not transform(low).min(transform(high))>moment/(8*step**2):
            return low
    return arb(tail)


if __name__=="__main__":
    ctx.prec=144
    f=caps()
    print("first positive radius",positive_radius().str(12))
    for j in (0,3,6,8,10,12,20,50,192,240):
        print(j,*(v.str(10) for v in f(arb(j))),flush=True)
