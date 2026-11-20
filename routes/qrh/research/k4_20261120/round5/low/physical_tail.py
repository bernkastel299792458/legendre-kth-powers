from flint import arb,ctx
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round2"/"local"))
from check_edge import budget
A=arb
def refine(lo,hi,extension,parts=256,res=128,J=64,addition="1.1328"):
    assert parts % 2 == 0 and 0 < J <= 64 and parts >= 2 and res >= 1
    pi=A.pi()
    l,h=A(lo),A(hi)
    K=A(3000175332800)+extension
    a=(1-A("1e-12"))*K*(4*(-h/4).exp()).log1p()/2
    r=A("1e-6")
    eta=A(addition)
    I=pi*a.sin()/a
    width=2*(pi-a)
    base,edge=budget(l,h,eta,extension)
    # Inherited tangent over short physical intervals is valid even at the
    # smallest new scale. Bound all short lengths by counting in length e^70.
    min_scale=width/(2*8192)
    assert 2*(l-K.log()+min_scale.log()).exp()/120**2 > 2*A(70).exp()/(70+eta)+1
    assert l>115 and h<116 and A(116)+A(7).log()+eta<120
    assert width>2 and K*r>2*pi*(J+1) and width<7
    def coeff(s):
        v=l-K.log()+eta+s.log()
        Jv=K.log()-eta-s.log()+r
        assert v>4 and Jv>2
        C=2*(l+r)*(r/2).exp()/(I*v**2)
        return C*r.exp()*(v-1),C*s
    slope,intercept=coeff(A("1.55"))
    # Stronger peak enclosures by a derivative inequality on each angular cell.
    original_sum=A(0)
    new_sum=A(0)
    level_gain=A(0)
    scales=[A(i)*width/40 for i in range(1,40)]
    fine=[coeff(s) for s in scales]
    def first(slabs):
        old=a.sin()/(2*a)
        cost=A(0)
        for k in range(slabs):
            wl,wr=width*k/slabs,width*(k+1)/slabs
            cr,br=coeff((wl+wr)/2)
            right=(a.cos()-(a+wr).cos())/(wr*(2*a+wr)) if k+1<slabs else A(0)
            dh=old-right
            assert dh>0
            cost+=2*dh*(br+((cr-slope)*wl).max((cr-slope)*wr))
            old=right
        return cost
    first_gain=first(256)-first(8192)
    for j in range(1,J+1):
        start=2*pi*j+a
        def oldpeak():
            best=A(0)
            for k in range(32):
                u0,u1=start+width*k/32,start+width*(k+1)/32
                numerator=(1+a.cos()).min(a.cos()-((u0+u1)/2).cos()+(u1-u0)/2)
                best=best.max(numerator/(u0**2-a**2))
            return best
        original_sum+=2*oldpeak()
        # On a cell, the maximum numerator is either the value at the endpoint
        # closer to the center or its value 1+cos a if it straddles the center.
        # The mirrored endpoints have identical numerator before division.
        vals=[A(0)]+[(a.cos()-(a+width*k/parts).cos())/((start+width*k/parts)**2-a**2)
                      for k in range(1,parts)]+[A(0)]
        upper=[]
        lower=[]
        for k in range(parts):
            u0=start+width*k/parts
            idx=k+1 if 2*k<parts else k
            vmax=a.cos()-(a+width*idx/parts).cos()
            upper.append(vmax/(u0**2-a**2))
            lower.append(vals[k].min(vals[k+1]))
        peak=A(0)
        for ub in upper:
            peak=peak.max(ub)
        new_sum+=2*peak
        h0=vals[parts//2]
        for n in range(res):
            # True superlevel length is enclosed using all angular cells,
            # irrespective of how the two components vary with the level.
            wlo=width*sum(int(t>h0*(n+1)/res) for t in lower)/parts
            whi=width*sum(int(not (t<h0*n/res)) for t in upper)/parts
            # Any scale gives a valid tangent; choose one before the verified min.
            sidx=int(float((wlo+whi)/(2*width))*40+.5)
            rows=range(max(1,sidx-1),min(39,sidx+1)+1)
            gain=A(0)
            for i in rows:
                m,b=fine[i-1]
                gain=gain.max(intercept-b+((slope-m)*wlo).min((slope-m)*whi))
            level_gain+=2*h0*gain/res
    pg=(original_sum-new_sum)*intercept
    gain=first_gain+pg+level_gain
    return base-gain,first_gain,pg,level_gain
if __name__=="__main__":
    ctx.prec=192
    for lo,hi,ext in [("115.033338","115.033646",-1280000),
                      ("115.033646","115.033660",-1280000),
                      ("115.033660","115.033663",300000)]:
        vals=refine(lo,hi,ext)
        n=(A(hi)/4).exp().floor().unique_fmpz()
        assert vals[0]<1 and 4*A(n).log()<A(hi) and A(hi)<4*A(n+1).log()
        print(lo,hi,ext,vals[0].str(18),n,flush=True)
