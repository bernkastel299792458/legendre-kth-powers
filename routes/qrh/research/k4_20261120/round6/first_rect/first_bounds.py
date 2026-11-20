"""Centered zero counts on the first genuine geometric-height rectangle."""
from pathlib import Path
from functools import lru_cache
import sys
from flint import arb,arb_series,ctx
RESEARCH=Path(__file__).resolve().parents[2]
sys.path.insert(0,str(RESEARCH/"round5"/"low"))
from finite_points import A,fixed_right,detector_floor
from narrow_cover import affine_mean,exact_right
from circle_mean import means,hinge_angular
from compressed_fourth import compressed
from critical_mean import critical_mean
from unit_diagonal import fourth
from local_energy import local_right_rows
from mixed_low import mixed_low_rows
from direct_high import direct_high
from center_fold import folded

H=3000175332800
NODES=(800,820,837,852,865)


def delta_height():
    return int((arb(H)*(arb(1)/4).expm1()).upper().ceil().unique_fmpz())


@lru_cache(maxsize=None)
def moment(size,panels=0):
    R=arb(size)/2;C=H+R;v=A("1.01");M=2048;B=C+v*R
    p=1+4/B.log()
    cumulative=fourth(B.log())*B*B.log()**4*M/(M-p)
    global_mean=cumulative*(1+(v*R/C)**(M-p))/2
    if panels==0:return global_mean.min(compressed(arb(H),arb(size)))
    J=A("1.015")*v*R
    sub=2*J/panels
    local=sum(compressed(C-J+sub*i,sub) for i in range(panels))
    tail=cumulative*A("1.015")**(p-M)
    return (local+tail).min(global_mean)


@lru_cache(maxsize=None)
def periodic_mass(size,qbase,alpha,panels):
    from periodic_local import effective_mass
    return effective_mass(size,qbase,A(alpha),panels,A(1))


def affine_calibrated(U,w,h,qbase):
    r=U.exp();y=r*h.exp()
    z=arb_series([2,1],prec=2).zeta()
    rho=1/z[0]
    c=arb.const_euler()-2*z[1]/z[0]
    prod=arb(1);num=1
    for p in (2,3,5,7):
        rho*=arb(p)/(p+1);c+=arb(p).log()/(p+1)
        if qbase%p:prod*=1+1/arb(p);num*=2
    harm=rho*(U+h+w/3+c)+54/y.sqrt()
    xmax=y*w.exp()
    count=2*rho*xmax/w**2*(1-(1+w)*(-w).exp())+18*xmax.sqrt()
    assert qbase in (6,30)
    opts=[(A(1),arb.pi()/3)] if qbase==6 else [(A(1),arb.pi()*A("8.405125")/30),
        (A("1.05"),arb.pi()*A("8.155125")/30),(A("1.082"),arb.pi()*8/30)]
    values=[folded(prod*harm,num*count/r,A("1.01")*r,A("1.01")*2048/2047,slope,defect)/U
            for slope,defect in opts]
    best=values[0]
    for x in values[1:]:best=best.min(x)
    if qbase==6:best=best.min(critical_mean(U,w,h,q=210))
    return best


def compute(size,ds,ws,hs,panels=0):
    R=arb(size)/2;U=R.log();d,w,h=map(A,(ds,ws,hs));q=210
    v=A("1.01");M=2048;ybar=v*M/(M-1);Y=R*h.exp()
    assert 4*M/R<1 and ((1+2/R)/v)**M<A(".000001") and 1/(1-(A(".5")+2/R)**M)<1+A(".000001")
    norm=(1+A(".000001"))**2/(1-A(1)/H)
    cm=affine_mean(U,w,h).min(critical_mean(U,w,h,q=q))
    left=(moment(size,max(0,panels))**(A(1)/4)*(cm*R*U).sqrt()+(ybar*R)**(A(3)/4))**A("4/3")
    right=exact_right(U,d,w,h).min(fixed_right(U,d,w,h,q))
    n=65536;e=2*d/U
    low=mixed_low_rows(U,d,w,w,A(0),h,q,cells=n,tight=True,first=n-1)[0]*U
    high=direct_high(U,d,w,h,q)*(2+e).zeta()/arb(2).zeta()
    right=right.min((-e*Y.log()).exp()*folded(high,low,v*R,ybar,A("1.274"),arb.pi()*48/210))
    if panels<0:
        from local_short import left_split
        for base,alpha,cells in ((6,"1.25",8),(30,"1.5",6)):
            m4=periodic_mass(size,base,alpha,cells)
            cmean=affine_calibrated(U,w,h,base)
            better=left_split(size,q,cmean,m4,U,w,h,base,
                                  [(4096,2),(32768,3),(65536,3),(131072,6)])
            left=left.min(better)
    a2=2*(Y.log()+2)/Y
    args=(U,d,left,right,norm,size*a2**2/arb.pi(),arb(1))
    rings=means(str(size),ws,hs)
    return args,rings


def samples(cases,panels=0):
    size=delta_height()
    W=arb(H)*(arb(1)/4).exp()
    record={}
    for ds,ws,hs in cases:
        args,rings=compute(size,ds,ws,hs,panels)
        for j in NODES:
            sigma=A(j)/1000
            floor,r=detector_floor(sigma,*args[:4])
            center=int(float(r)*10000+.5);best=None
            for m in range(center-55,center+32,2):
                s=A(m)/10000
                if s>=sigma:continue
                n=hinge_angular(s,args,rings)/(sigma-s)
                if best is None or n<best[0]: best=(n,m)
            if j not in record or best[0]<record[j][0]:
                record[j]=(*best,ds,ws,hs)
        print("parameters",ds,ws,hs,"L",args[2].str(8),"R",args[3].str(8),flush=True)
    for j,(n,m,*parameters) in record.items():
        sigma=A(j)/1000
        goal=6*W.log()*W**(3*(1-sigma)/(3*sigma-1))
        print(j,"upper",n.str(14),"goal",goal.str(13),"ratio",(n/goal).str(10),"knot",m,parameters,flush=True)
    return record


if __name__=="__main__":
    ctx.prec=192
    options=[(".80","8","-2.5"),(".86","8.5","-2.8"),(".90","8.5","-3"),(".94","8.8","-3.1")]
    mode=int(sys.argv[1]) if len(sys.argv)>1 else -1
    record=samples(options,mode)
    if mode<0:
        for j,cap in zip(NODES,(243733500,70533811,24420595,9064416,3815142)):
            assert record[j][0]<cap
