"""Finite exponent, translated half means and convex spectral sums for the low endpoint."""
from functools import lru_cache
from fractions import Fraction
import argparse
from flint import arb, arb_series, ctx
from moving_window import A, budget, refine, linear_mean_coefficients
from finite_points import local_right_rows, direct_high
from variance import low_saving

from verify_fine import finite_data, signed_low_norm
from critical_mean import critical_mean
from circle_mean import means, hinge_angular
from center_fold import folded

H=3000175332800


def affine_mean(U,W,Lh):
    r=U.exp(); h=Lh.exp(); y=r*h
    cd,ch=linear_mean_coefficients(6,A("1.01")*r,A("1.01")*2048/2047)
    z=arb_series([2,1],prec=2).zeta()
    rho=1/z[0]; c=arb.const_euler()-2*z[1]/z[0]
    for p in (2,3,5,7):
        rho*=arb(p)/(p+1)
        c+=arb(p).log()/(p+1)
    harm=rho*(U+Lh+W/3+c)+3*18/y.sqrt()
    X=y*W.exp()
    unweighted=rho*2*X/W**2*(1-(1+W)*(-W).exp())+18*X.sqrt()
    mass=(1+A(1)/5)*(1+A(1)/7)*harm
    energy=4*unweighted/r
    return (cd*mass+ch*energy).min(folded(mass,energy,A("1.01")*r,
        A("1.01")*2048/2047,arb(1),arb.pi()/3))/U


def exact_right(U,delta,W,Lh):
    r=U.exp(); y=r*Lh.exp(); e=2*delta/U
    assert y>2048 and 0<e and e<=A(".1")
    S,heads,_,fe,table=finite_data(W,y,True)
    head,mid=signed_low_norm(table,e,e,W,y)
    z=(1+e).zeta()
    err=A(".011")
    basic=sum(m*(v+2*e*t+err/(1+arb(10**14).log()))**2 for m,v,t in heads)
    head=head.min(basic)
    shape=1/(1+S)+1/(1+y.log())**2+32/y
    from window_variance import components
    extra,short=components(e,W,y)
    mid=(head+mid).min(short)
    head=((1+e*W)*fe.sqrt()/W+2*err*shape.sqrt())**2
    low=z*(head+mid)+(-e*W).exp()*(1+e/y)/(e*z)
    # Low is S_Q(1+e) divided by Y^-e; CM, bands and tail have actual-height units.
    hilb,bands,remote=local_right_rows(U,delta,W,Lh,210,cells=16)
    low-=extra.max(U*low_saving(U,delta,W,Lh,210))
    assert low>0
    high=direct_high(U,delta,W,Lh,210)*(2+e).zeta()/arb(2).zeta()
    cd,ch=linear_mean_coefficients(210,A("1.01")*r,A("1.01")*2048/2047,"density")
    discount=(-e*y.log()).exp()
    return (discount*(hilb*low+bands[-1])+remote*r*arb(2).zeta()**4).min(
        discount*(ch*low+cd*high)).min(discount*folded(high,low,A("1.01")*r,
        A("1.01")*2048/2047,A("1.274"),arb.pi()*48/210))


@lru_cache(maxsize=None)
def window_mass(size):
    from compressed_fourth import compressed
    return compressed(arb(H),A(size))


@lru_cache(maxsize=None)
def boundary(size,delta,width,logh):
    d,w,h=map(A,(delta,width,logh))
    D=A(size);R=D/2;U=R.log();T=H+D;Y=R*h.exp()
    v=A("1.01");m=2048;ybar=v*m/(m-1)
    assert 4*m/R<1 and ((1+2/R)/v)**m<A(".000001")
    assert 1/(1-(A(".5")+2/R)**m)<1+A(".000001")
    norm=(1+A(".000001"))**2/(1-A(1)/H)
    cm=affine_mean(U,w,h)
    if U>20:cm=cm.min(critical_mean(U,w,h,q=210))
    left=(window_mass(size)**A(".25")*(cm*R*U).sqrt()+(ybar*R)**A(".75"))**A("4/3")
    right=exact_right(U,d,w,h)
    a2=2*(Y.log()+2)/Y
    assert (1+a2)**9<arb(3)/2
    outer=11*(210*Y*w.exp()).sqrt()*(T+6)
    return U,d,left,right,norm,D*a2**2/arb.pi(),outer


@lru_cache(maxsize=None)
def weighted(lo,size,case):
    L=A(lo);D=A(size)
    count=A(".3")*arb(H).log()+6+((H/(2*arb.pi())).log()/(2*arb.pi())+A(".15")/H)*D+D**2/(4*arb.pi()*H)
    if case=="old":
        from moving_window import centered_boundary
        inputs=[(centered_boundary(size,frozen=True),means(size,"8","-2.8"))]
    else:
        rows=[row.split(",") for row in case.split(":")]
        inputs=[(boundary(size,d,w,h),means(size,w,h)) for d,w,h in rows]
    keep=[]
    for i in list(range(640,875,2))+[875]:
        s=A(i)/1000
        if i==875:
            val=arb(0)
        else:
            vals=[hinge_angular(s,args,ring) for args,ring in inputs]
            val=vals[0]
            for v in vals[1:]: val=val.min(v)
        while len(keep)>=2:
            a,ha=keep[-2]; b,hb=keep[-1]
            if not (hb-ha)*(s-b)>(val-hb)*(b-a):break
            keep.pop()
        keep.append((s,val))
    total=((keep[0][0]-1)*L).exp()*count
    last=arb(0)
    for (s,val),(t,_) in zip(keep,keep[1:]):
        slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        assert slope>last
        total+=(slope-last)*val;last=slope
    return total


def certificate(lo,hi,S,count,case,mesh="1",addition="1.1328"):
    k=arb(H+S); q=A(10000)
    a=(1-A("1e-12"))*k*(4*(-A(hi)/4).exp()).log1p()/2
    assert 0<a and a<arb.pi()/2+arb.pi()/2
    I=arb.pi()*a.sin()/a
    _,old=budget(A(lo),A(hi),A(addition),S)
    arithmetic=refine(lo,hi,S,addition=addition)[0]-old
    top=S+1280000
    caps=[]; amounts=[]
    lin=Fraction(mesh)
    assert 0<=lin<=1
    for i in range(count+1):
        z0=Fraction(i,count)
        pos=top*z0*(lin+(1-lin)*z0)
        if i<count:
            z=(a*(1-(H+A(str(pos)))/k)).max(A(0)).min(arb.pi()/2)
            caps.append((z.sin()+2*q*a/(arb.pi().sqrt()*k)).min(A(1))/a.sin())
        if i:
            amounts.append(weighted(lo,str(pos),case))
    eps=1/(16*q*q)
    high=2*eps.exp()*sum((b-c)*v for b,c,v in zip(caps,caps[1:]+[arb(0)],amounts))
    assert all(b>c for b,c in zip(caps,caps[1:]+[arb(0)]))
    t=k+128*q;g0=(1-a.cos())/a**2
    tail=2*k/I*(2*arb.pi()*g0)/(2*arb.pi().sqrt()*q)*eps.exp()
    tail*=t**2*(1+A(4)/128**2)*(-A(128)**2/4).exp()
    assert tail<A("1e-1700")
    return arithmetic+high+tail,high,arithmetic


if __name__=="__main__":
    cli=argparse.ArgumentParser()
    cli.add_argument("--hi",default="115.034900");cli.add_argument("--lo",default="115.034000")
    cli.add_argument("--size",type=int,default=3200000000);cli.add_argument("--parts",type=int,default=32)
    cli.add_argument("--case",default=".64,8,-2.8");cli.add_argument("--check",action="store_true")
    cli.add_argument("--mesh",default="1")
    cli.add_argument("--eta",default="1.1328",help="proved uniform sieve addition for interval lengths >= exp(70)")
    cli.add_argument("--check-high",help="independently verify an upper bound for the finite high-zero charge")
    args=cli.parse_args();ctx.prec=192
    total,high,base=certificate(args.lo,args.hi,args.size,args.parts,args.case,args.mesh,args.eta)
    n=(A(args.hi)/4).exp().floor().unique_fmpz()
    assert 4*arb(n).log()<A(args.hi)<4*arb(n+1).log()
    print(args.lo,args.hi,args.size,args.parts,args.case,args.mesh,args.eta,"total",total.str(18),"high",high.str(18),"other",base.str(18),"n",n,flush=True)
    if args.check: assert total<1
    if args.check_high: assert high<A(args.check_high)
