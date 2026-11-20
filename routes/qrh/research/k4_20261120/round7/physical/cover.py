"""Subtract a location-sensitive physical-side sieve saving on the two first positive lobes."""
import argparse,sys
from fractions import Fraction
from pathlib import Path
from flint import arb,ctx
research=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(research/"round5"/"low"))
from physical_tail import refine
from check_edge import budget

H=3000175332800
def first_save(lo,hi,size,eta="2.10",cell_bounds=None,location_hi="115.12"):
    A=arb; l,h=map(A,(lo,hi)); K=A(H+size);pi=A.pi();rad=A("1e-6")
    a=(1-A("1e-12"))*K*(4*(-h/4).exp()).log1p()/2
    I=pi*a.sin()/a; width=2*(pi-a);cmax=h+(4*(-l/4).exp()).log1p()/2
    if cell_bounds is None:assert Fraction(location_hi)<=Fraction("115.12")
    assert l-rad>A("114.98") and cmax+rad<A(location_hi)
    assert 2*pi<K*rad
    def coeff(s,et):
        v=l-K.log()+s.log()+A(et)
        assert v>4 and K.log()-s.log()-A(et)+rad>2
        base=2*(l+rad)*(rad/2).exp()/(I*v*v)
        return base*rad.exp()*(v-1),base*s
    bounds=("2.1607","2.3060","2.3779","2.4070","2.4073","2.3825") if cell_bounds is None else tuple(cell_bounds)
    assert len(bounds)==6 and all(A(s)>1 for s in bounds)
    # Convert the extreme log-coordinate lengths back to ordinary real lengths.
    sm=(l-rad).exp()/K;sp=(cmax+rad).exp()/K
    cut=[A(i).exp() for i in range(83,90)]
    def local_eta(w0,w1):
        ylo,yhi=sm*w0,sp*w1
        if not (ylo>cut[0] and yhi<cut[-1]):return None
        if eta!="auto":
            assert Fraction(eta)<=Fraction("2.10")
            return eta
        return min((bounds[i] for i in range(6) if not (yhi<cut[i] or ylo>cut[i+1])),key=lambda s:A(s))
    old=a.sin()/(2*a);gain=A(0)
    for i in range(8192):
        wl,wr=width*i/8192,width*(i+1)/8192
        u=a+wr
        new=(a.cos()-u.cos())/(wr*(2*a+wr)) if i+1<8192 else A(0)
        dh=old-new;old=new
        tag=local_eta(wl,wr)
        if tag is None:continue
        s=(wl+wr)/2
        c,d=coeff(s,"1.16613");cc,dd=coeff(s,tag)
        deduct=(d-dd+((c-cc)*wl).min((c-cc)*wr)).max(A(0))
        gain+=2*dh*deduct
    if eta=="auto":
        slope,intercept=coeff(A("1.55"),"1.16613")
        scales=[width*i/40 for i in range(1,40)]
        previous=[coeff(s,"1.16613") for s in scales]
        stronger={e:[coeff(s,e) for s in scales] for e in bounds}
        parts,res=256,128
        assert K*rad>2*pi*66
        for j in range(1,65):
            u=2*pi*j+a
            val=[A(0)]+[(a.cos()-(a+width*k/parts).cos())/((u+width*k/parts)**2-a**2)
                        for k in range(1,parts)]+[A(0)]
            hi=[];low=[]
            for k in range(parts):
                idx=k+1 if 2*k<parts else k
                hi.append((a.cos()-(a+width*idx/parts).cos())/((u+width*k/parts)**2-a**2))
                low.append(val[k].min(val[k+1]))
            midpoint=val[parts//2]
            for j0 in range(res):
                wl=width*sum(int(v>midpoint*(j0+1)/res) for v in low)/parts
                wr=width*sum(int(not(v<midpoint*j0/res)) for v in hi)/parts
                tag=local_eta(wl,wr)
                if tag is None:continue
                sel=int(float((wl+wr)/(2*width))*40+.5)
                loc=range(max(1,sel-1),min(39,sel+1)+1)
                def extra(row):
                    saved=A(0)
                    for i in loc:
                        slope1,int1=row[i-1]
                        saved=saved.max(intercept-int1+((slope-slope1)*wl).min((slope-slope1)*wr))
                    return saved
                new_gain=extra(stronger[tag]);old_gain=extra(previous)
                gain+=2*midpoint/res*(new_gain-old_gain).max(A(0))
    return gain


def full(lo,hi,size,eta,charge=None,cell_bounds=None,location_hi="115.12"):
    base=refine(lo,hi,size,addition="1.16613")[0]
    gain=first_save(lo,hi,size,eta,cell_bounds,location_hi)
    if charge is not None:
        assert size==16000000000 and Fraction(lo)>=Fraction("115.040500") and Fraction(hi)>=Fraction("115.041000")
        # Certified reference charge in round7/first_selected/LOW_CONTINUATION.md.
        # A user-supplied smaller number is not a valid substitute.
        assert Fraction(charge)>=Fraction(".005937108818")
        finite=arb(charge)
        base-=budget(arb(lo),arb(hi),arb("1.16613"),size)[1]
        # The Gaussian tail at K+128Q is bounded uniformly as before.
        Q=arb(10000);K=arb(H+size)
        a=(1-arb("1e-12"))*K*(4*(-arb(hi)/4).exp()).log1p()/2
        assert arb.pi()/2<a<arb.pi()
        old=(1-arb("1e-12"))*K*(4*(-arb("115.041")/4).exp()).log1p()/2
        assert arb.pi()/2<old<arb.pi()
        if Fraction(hi)>Fraction("115.041000"):assert a<old and a.sin()>old.sin()
        tail=2*K/(arb.pi()*a.sin()/a)*(arb.pi()*(1-a.cos())/a**2)/(arb.pi().sqrt()*Q)
        tail*=(1/(16*Q**2)).exp()*(K+128*Q)**2*(1+arb(4)/128**2)*(-arb(128)**2/4).exp()
        assert tail<arb("1e-1700")
        base+=finite+tail
    return base-gain,gain


if __name__=='__main__':
    ap=argparse.ArgumentParser()
    ap.add_argument("--lo",default="115.041002");ap.add_argument("--hi",default="115.05")
    ap.add_argument("--size",type=int,default=-206000);ap.add_argument("--eta",default="2.10")
    ap.add_argument("--high");ap.add_argument("--check",action="store_true")
    a=ap.parse_args();ctx.prec=192
    value,gain=full(a.lo,a.hi,a.size,a.eta,a.high)
    print(a.lo,a.hi,a.size,"total",value.str(18),"saved",gain.str(16),flush=True)
    if a.check:assert value<1
