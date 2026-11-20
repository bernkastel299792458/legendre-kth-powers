"""Compact, rectangle-free bridge with the cumulative detector applied at actual heights."""
import argparse
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,arb_mat,ctx
from tables import A,H,angular_edge
from finite_anchor import row_constants,REGISTERED,modest_right
from short_block import cm_local,normalized_row
from grid_target import cap_table,weights,dot,chord_bounds,curves,tail_coefficients
from radial_detectors import caps as radial_table, LOW as RLOW, HIGH as RHIGH

@lru_cache(maxsize=512)
def point_radial(k,j,prec):
    assert k>=RLOW and j<=RHIGH and prec==ctx.prec
    arr=radial_table(prec)
    choices=[r[k-RLOW].max(r[j-RLOW]) for r in arr]
    best=choices[0]
    for c in choices[1:]:best=best.min(c)
    return best

def point(nu):
    k=int((nu*200).lower().floor().unique_fmpz())
    j=int((nu*200).upper().ceil().unique_fmpz())
    return point_radial(k,j,ctx.prec)

@lru_cache(maxsize=256)
def radial_lines(k,j,prec):
    assert k>=RLOW and j<=RHIGH and k<j and prec==ctx.prec
    rows=radial_table(prec)
    ends=[(r[k-RLOW].log(),r[j-RLOW].log()) for r in rows]
    return [(a,b-a) for a,b in ends
            if not any(c<a and d<b for c,d in ends)]

def interpolated_point(nu):
    k=int((nu*200).lower().floor().unique_fmpz())
    j=int((nu*200).upper().ceil().unique_fmpz())
    if k==j:
        return point_radial(k,j,ctx.prec)
    x=(nu*200-k)/(j-k)
    # Log-convexity in nu of each polynomial's exact radial supremum.
    vals=[a+x*t for a,t in radial_lines(k,j,ctx.prec)]
    best=vals[0]
    for v in vals[1:]:
        best=best.min(v)
    return best.exp()

@lru_cache(maxsize=512)
def periodic_cached(index,alpha,prec):
    assert prec==ctx.prec and index>20*10**6
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"phase"))
    from periodic_fourth import fourth
    return fourth(arb(index)/10**6,6,A(alpha))

@lru_cache(maxsize=512)
def smooth_cached(index,base,prec,method="basic"):
    assert prec==ctx.prec
    sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"phase"))
    if method=="centered":
        from centered_phase import fourth
        return fourth(arb(index)/10**6,base,arb(1),A(".04"),384)
    if method=="projected":
        from mixed_product import projected_fourth
        return projected_fourth(arb(index)/10**6,base,arb(1),A(".04"),384)
    if method in ("shifted","disjoint"):
        from shifted_harmonic import fourth,disjoint_fourth
        func=disjoint_fourth if method=="disjoint" else fourth
        return func(arb(index)/10**6,base,A("1.25"),A(".06"),384)
    from smooth_cut import smooth_fourth
    return smooth_fourth(arb(index)/10**6,base,arb(1),A(".06"),384)

def finite_row(U,V,delta,w,lh,core,cells,alpha,extra_base,smooth=False,q=210):
    if q==2310:
        assert extra_base==210 and core*q<2**32 and smooth and (V-U)<=arb(1)/2
        sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"folds"))
        from fold_mean import source
        def residual(u,ww,logh,mod):
            return source(u,ww,logh,mod,extra_base,12)
        def periodic(u):
            i=int((u*10**6).lower().floor().unique_fmpz())
            return smooth_cached(i,extra_base,ctx.prec,smooth)
        left=normalized_row(U,V,q,core,w,lh,residual,fourth_fn=periodic,
                            sieve_base=extra_base,small_factor=arb(1)/12)[0]
        return left,modest_right(U,V,delta,w,lh,cells,q=q,frequency_cut="100")
    if not alpha:
        _,left,right,_=row_constants(U,V,delta,w,lh,core,True,True,cells)
        return left,right
    def fourth(u):
        j=int((u*10**6).lower().floor().unique_fmpz())
        return periodic_cached(j,alpha,ctx.prec)
    pieces=int((2*(V-U)).upper().ceil().unique_fmpz())
    left=arb(0)
    for j in range(pieces):
        low,high=U+(V-U)*j/pieces,U+(V-U)*(j+1)/pieces
        val=normalized_row(low,high,210,core,w,lh,cm_local,fourth_fn=fourth)[0]
        if extra_base:
            sys.path.insert(0,str(Path(__file__).resolve().parents[1]/"folds"))
            from fold_mean import joint,source
            val=val.min(joint(low,high,w,lh,ncore=core,base=extra_base)[0])
            if smooth:
                def cm(u,width,logh,q):
                    return source(u,width,logh,q,extra_base,12)
                def m4(u):
                    idx=int((u*10**6).lower().floor().unique_fmpz())
                    return smooth_cached(idx,extra_base,ctx.prec,smooth)
                other=normalized_row(low,high,210,core,w,lh,cm,fourth_fn=m4,
                                     sieve_base=extra_base,small_factor=arb(1)/12)[0]
                val=val.min(other)
        left=left.max(val)
    return left,modest_right(U,V,delta,w,lh,cells)

def test(first,last,param,nheight,mesh,step,cells,core,alpha,sub,extra_base,smooth,modulus,lo=36,hi=50,
         interpolate=False,spectrum_data=None,tight_rows=False,observe_cell=None):
    L0,L1=A(first),A(last)
    assert 140<=L0 and L0<L1 and L1<=163 and nheight>0 and mesh>0 and step>0 and sub>0
    d0=(4*(-L0/4).exp()).log1p()
    lo=min(lo,int((A(".5")/d0).log().lower().floor().unique_fmpz()))
    cap=cap_table(d0)
    assert d0*arb(lo).exp()<A(".5") and (4*(-L1/4).exp()).log1p()*arb(hi).exp()>192
    Hlog=arb(H).log()
    assert Hlog<lo
    T0=arb(lo).exp()
    assert 8192/T0<1 and ((1+2/T0)/A("1.01"))**2048<A("1e-6")
    assert 1/(1-(A(".5")+2/T0)**2048)<1+A("1e-6")
    normlog=((1+A("1e-6"))**2/(1-1/arb(3*10**12))).log()
    abscissae=[arb(i)/2000 for i in range(1300,1750,step)]+[A("7/8")]
    args=[tuple(map(A,row.split(","))) for row in param.split(";")]
    right_rows=[]
    Tvals=[arb(lo).exp()]
    counts=[]
    fH=arb(H)*((arb(H)/(2*arb.pi())).log()-1)/(2*arb.pi())
    for k in range(lo*sub,hi*sub):
        uk,vk=arb(k)/sub,arb(k+1)/sub
        choices=[]
        for delta,w,lh in args:
            left,right=finite_row(uk,vk,delta,w,lh,core,cells,alpha,extra_base,smooth,modulus)
            edge=angular_edge(uk,vk,w,lh,q=modulus)
            choices.append((delta,left.log(),right.log(),edge))
        for i in range(1,nheight+1):
            u=(k+arb(i)/nheight)/sub
            t=u.exp()
            Tvals.append(t)
            counts.append(t*((t/(2*arb.pi())).log()-1)/(2*arb.pi())-fH+A(".15")*(Hlog+u)+6)
            known=[]
            logu=u.log()
            for s in abscissae[:-1]:
                best=None
                for delta,ll,rr,edge in choices:
                    den=2-s+3*delta/u
                    nu=(2+4*delta/u)/den
                    p=3*(1-s+delta/u)/den
                    assert 0<p and p<1
                    detector=interpolated_point(nu) if interpolate else point(nu)
                    z=detector*(nu*normlog+p*(ll+u+2*logu)+(1-p)*(rr+logu)).exp()/(2*arb.pi())+edge
                    best=z if best is None else best.min(z)
                known.append(best)
            right_rows.append(chord_bounds(abscissae,known+[arb(0)])[:-1])
    if tight_rows:
        # Every true hinge sum is nondecreasing with height. Later upper
        # bounds apply to earlier heights, before any physical weight is chosen.
        for k in range(len(right_rows)-2,-1,-1):
            right_rows[k]=[v.min(w) for v,w in zip(right_rows[k],right_rows[k+1],strict=True)]
    C=arb_mat(right_rows).transpose()
    F=curves(arb(hi),False,32768)
    final=tail_coefficients(F,arb(hi))
    final=[final[0]]+chord_bounds(F[0],final[1:]+[arb(0)])[:-1]
    if spectrum_data is not None:
        return spectrum_data(Tvals,counts,abscissae,right_rows,F,final)
    dx=arb(1)/mesh
    ncell=int(((L1-L0)*mesh).upper().ceil().unique_fmpz())
    cells=[(L0+i*dx,(L0+(i+1)*dx).min(L1)) for i in range(ncell)]
    ww=[weights([abscissae],a) for a,b in cells]
    Z=arb_mat([w[1:] for w in ww])*C
    maxcost=arb(0)
    for j,(a,b) in enumerate(cells):
        eps=4*(-a/4).exp()
        d=(4*(-b/4).exp()).log1p()
        E=[cap(d*t) for t in Tvals]
        total=E[-1]*dot(weights(F,a),final)
        for k,(v,w) in enumerate(zip(E,E[1:])):
            dep=(v-w).max(arb(0))
            if not dep.is_zero():total+=dep*(Z[j,k]+ww[j][0]*counts[k])
        total=2*(total+(-a/2).exp()*arb(H)*Hlog)
        total+=(1+eps)**A("1.5")*(b+eps.log1p())**2*(-a/4).exp()/(6*arb(2).log())
        total+=(-3*a).exp()/(1-(-2*a).exp())
        if observe_cell is not None:observe_cell(a,b,total)
        if total>maxcost: arg=a
        maxcost=maxcost.max(total)
    print("rectangle-free bridge",first,last,"full budget",maxcost.str(18),"worst",arg.str(12),flush=True)
    return maxcost

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--first",default="161.8")
    cli.add_argument("--last",default="162.3")
    cli.add_argument("--param",default=REGISTERED)
    cli.add_argument("--nheight",type=int,default=64)
    cli.add_argument("--mesh",type=int,default=64)
    cli.add_argument("--step",type=int,default=2)
    cli.add_argument("--cells",type=int,default=128)
    cli.add_argument("--core",type=int,default=2097152)
    cli.add_argument("--alpha",default="")
    cli.add_argument("--sub",type=int,default=1)
    cli.add_argument("--extra-base",type=int,choices=(0,6,30,210),default=0)
    cli.add_argument("--smooth",nargs="?",const="basic",choices=("basic","shifted","disjoint","projected","centered"))
    cli.add_argument("--modulus",type=int,choices=(210,2310),default=210)
    cli.add_argument("--interpolate",action="store_true")
    cli.add_argument("--top",dest="hi",type=int,default=50)
    cli.add_argument("--diagnose",action="store_true")
    if len(sys.argv)==1:
        cli.set_defaults(first="154.6",last="155",alpha="1.5",extra_base=30,
                         nheight=48,sub=2,cells=128,mesh=64)
    args=vars(cli.parse_args());diagnose=args.pop("diagnose")
    ctx.prec=160
    z=test(**args)
    if not diagnose:
        assert z<1
        anchor=A(args["first"])
        n=(anchor/4).exp().ceil().unique_fmpz()
        assert n is not None and 4*arb(n-1).log()<anchor<4*arb(n).log()
        print("first integer at the compact anchor",n,flush=True)
