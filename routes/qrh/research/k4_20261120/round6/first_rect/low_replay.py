"""Use the projected, fixed-dual fourth moment on each genuine near-H density window."""
from fractions import Fraction
from functools import lru_cache
import argparse
from flint import arb,ctx
from first_bounds import A,H,affine_calibrated
from circle_mean import means,hinge_angular
from narrow_cover import exact_right
from periodic_local import effective_mass
from physical_tail import refine
from check_edge import budget


@lru_cache(maxsize=None)
def local4(size,base):
    return effective_mass(size,base,A("1.25") if base==6 else A("1.5"),1,A(1))


@lru_cache(maxsize=None)
def weights(lo,size,ds,ws,hs,base,return_inputs=False):
    L=A(lo);R=arb(size)/2;U=R.log();d,w,h=map(A,(ds,ws,hs))
    ybar=A("1.01")*2048/2047
    assert 8192/R<1 and ((1+2/R)/A("1.01"))**2048<A(".000001")
    assert 1/(1-(A(".5")+2/R)**2048)<1+A(".000001")
    Y=R*h.exp()
    norm=(1+A(".000001"))**2/(1-A(1)/H)
    A4=local4(size,base)
    cm=affine_calibrated(U,w,h,base) if U>20 else None
    if cm is None:
        # At smaller widths use the fully explicit affine squarefree head.
        if base!=6:raise ValueError("choose modulus 6 below exp(20)")
        from narrow_cover import affine_mean
        cm=affine_mean(U,w,h)
    left=(A4**A(".25")*(cm*R*U).sqrt()+(ybar*R)**A(".75"))**A("4/3")
    from local_short import left_split
    left=left.min(left_split(size,210,cm,A4,U,w,h,base,[(512,2),(2048,3),(8192,3)]))
    right=exact_right(U,d,w,h)
    a2=2*(Y.log()+2)/Y
    assert (1+a2)**15<A("1.5")
    args=U,d,left,right,norm,size*a2**2/arb.pi(),arb(1)
    rings=means(str(size),ws,hs)
    if return_inputs:return args,rings
    count=A(".3")*arb(H).log()+6+((H/(2*arb.pi())).log()/(2*arb.pi())+A(".15")/H)*size+arb(size)**2/(4*arb.pi()*H)
    keep=[]
    for i in list(range(640,875,2))+[875]:
        s=A(i)/1000
        val=arb(0) if i==875 else hinge_angular(s,args,rings)
        while len(keep)>=2:
            a,ha=keep[-2];b,hb=keep[-1]
            if not (hb-ha)*(s-b)>(val-hb)*(b-a):break
            keep.pop()
        keep.append((s,val))
    total=((keep[0][0]-1)*L).exp()*count
    old=arb(0)
    for (s,v),(t,_) in zip(keep,keep[1:]):
        slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        assert slope>old
        total+=(slope-old)*v;old=slope
    return total


def certify(lo,hi,size,panels,case,mesh="1/4",base=6):
    k=arb(H+size);Q=A(10000)
    a=(1-A("1e-12"))*k*(4*(-A(hi)/4).exp()).log1p()/2
    I=arb.pi()*a.sin()/a
    plus="1.16613"
    arith=refine(lo,hi,size,addition=plus)[0]-budget(A(lo),A(hi),A(plus),size)[1]
    costs=[];caps=[];w=Fraction(mesh)
    assert 0<=w<=1
    for i in range(panels+1):
        z=Fraction(i,panels)
        t=(size+1280000)*z*(w+(1-w)*z)
        if i<panels:
            s=(a*(1-(H+A(str(t)))/k)).max(A(0)).min(arb.pi()/2)
            caps.append((s.sin()+2*Q*a/(arb.pi().sqrt()*k)).min(A(1))/a.sin())
        if i:
            D=(t.numerator+t.denominator-1)//t.denominator
            costs.append(weights(lo,D,*case.split(","),base))
    eps=1/(16*Q**2)
    assert all(b>c for b,c in zip(caps,caps[1:]+[arb(0)]))
    charge=2*eps.exp()*sum((b-c)*v for b,c,v in zip(caps,caps[1:]+[arb(0)],costs))
    top=k+128*Q;g0=(1-a.cos())/a**2
    tail=2*k/I*(2*arb.pi()*g0)/(2*arb.pi().sqrt()*Q)*eps.exp()*top**2*(1+A(4)/128**2)*(-A(128)**2/4).exp()
    assert tail<A("1e-1700")
    return arith+charge+tail,charge,arith


if __name__=="__main__":
    ap=argparse.ArgumentParser()
    ap.add_argument("--lo",default="115.036065");ap.add_argument("--hi",default="115.040000")
    ap.add_argument("--size",type=int,default=10000000000);ap.add_argument("--panels",type=int,default=24)
    ap.add_argument("--case",default=".68,8,-3");ap.add_argument("--mesh",default="1/4")
    ap.add_argument("--base",type=int,default=6);ap.add_argument("--check",action="store_true")
    ap.add_argument("--check-high")
    a=ap.parse_args();ctx.prec=192
    total,high,arith=certify(a.lo,a.hi,a.size,a.panels,a.case,a.mesh,a.base)
    print(a.lo,a.hi,a.size,a.panels,"total",total.str(17),"high",high.str(17),"other",arith.str(17),flush=True)
    if a.check:assert total<1
    if a.check_high:assert high<A(a.check_high)
