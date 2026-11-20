"""Finite cumulative zero-count targets integrated directly against the polygon."""

import argparse
from pathlib import Path
import sys
from flint import arb, ctx

here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent/"spectrum"))
from density_target import A, boundary_data, detector, moments
from verify_euler import coefficient,quintic_bound
from polygon import envelope,SCALE


def cap_table(d,step=256,tail=192):
    jumps,rest=envelope(d,step,tail)
    top=step*tail
    ticks=[0]*(top+1)
    for y,w in jumps:
        i=int((y*step).unique_fmpz())
        ticks[i]+=int((w*SCALE).unique_fmpz())
    carry=int((rest*SCALE).unique_fmpz())
    for i in range(top,-1,-1):
        carry+=ticks[i]
        ticks[i]=carry
    def cap(y):
        if y>tail:
            return rest*(tail/y)**2
        n=int((y*step).lower().floor().unique_fmpz())
        return arb(ticks[min(top,n)])/SCALE
    return cap


def curves(upper,low,short_core=0):
    if low:
        U,delta,left,right,norm,ec,es=boundary_data()
        knots=[arb(i)/1000 for i in range(650,801,2)]
    else:
        U=upper
        delta,W,logh=map(A,(".92","9.5","-3.5"))
        short=None
        if short_core:
            from short_block import split_endpoint,cm_local
            def short(u,w,l,q):
                return split_endpoint(u,w,l,q,short_core,cm_local)[0]
        left,right=moments(U,delta,W,logh,210,"100",short=short,tight=bool(short_core))
        _,_,_,_,norm,_,es=boundary_data()
        j=A("15/14").log()
        ec=162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+
           9*(11*arb(210).sqrt()*((W+logh)/2).exp()).log())/j)
        knots=[arb(i)/1000 for i in range(650,871,2)]+[A("7/8")]
        if not (U>29 and 9/((U+logh)/2).exp()<A("1/4")):
            raise ValueError("remote detector domain")
    ratio=left/right
    rows=[]
    for s in knots[:-1]:
        p=3*(1-s)/(2-s)
        c,k=3*delta/(2-s),3*delta*(2*s-1)/(2-s)**2
        lo,hi=(2+4*delta/U)/(2-s+3*delta/U),2/(2-s)
        if not (c+1+c/U<(U*ratio).log() and A("1.4")<=lo and hi<=A("16/9")):
            raise ValueError("hinge normalization")
        if low:
            cd=detector(int((s*1000).unique_fmpz()))
        else:
            cd=coefficient(lo,hi)
            quin=quintic_bound(lo,hi)
            if quin is not None:
                cd=cd.min(quin)
        B=cd*norm**hi*right*ratio**p*(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
        rows.append((B,p))
    return knots,rows,ec,es


def cumulative_coefficients(curve,u):
    _,rows,ec,es=curve
    # The common rectangular edge is included in each hinge.
    return [u.exp()*u]+[B*(p*u).exp()*u**(1+p)+ec+es*u for B,p in rows]


def tail_coefficients(curve,u):
    """Conditional expectation for log(T/T_f) exponential with rate 2."""
    _,rows,ec,es=curve
    def bound(p,r):
        denominator=2-p-r/u
        if not denominator>0:
            raise ValueError("nonintegrable frequency tail")
        return 2*(p*u).exp()*u**r/denominator
    return [bound(arb(1),arb(1))]+[B*bound(p,1+p)+ec+es*bound(arb(0),arb(1)) for B,p in rows]


def weights(curve,a):
    knots=curve[0]
    out=[((knots[0]-1)*a).exp()]
    last=arb(0)
    for s,t in zip(knots,knots[1:]):
        current=((s-1)*a).exp()*((t-s)*a).expm1()/(t-s)
        if not current>last:
            raise ArithmeticError("nonpositive chord jump")
        out.append(current-last)
        last=current
    return out


def dot(w,v):
    return sum((a*b for a,b in zip(w,v,strict=True)),arb(0))


def chord_bounds(knots,values):
    """Any chord joining upper bounds majorizes the intervening actual convex hinges."""
    stack=[]
    for i in range(len(knots)):
        while len(stack)>=2:
            j,k=stack[-2:]
            if not (values[k]-values[j])*(knots[i]-knots[k]) > (values[i]-values[k])*(knots[k]-knots[j]):
                break
            stack.pop()
        stack.append(i)
    out=values.copy()
    for j,k in zip(stack,stack[1:]):
        for i in range(j+1,k):
            rate=(knots[i]-knots[j])/(knots[k]-knots[j])
            out[i]=out[i].min((1-rate)*values[j]+rate*values[k])
    return out


def test(upper_log="41.6",count=8,beta_step=13,cell="1/8",height_sub=10,constant="6",
         warp="2",last="167.4",short_core=0,convex=False,beta_list=None,quarter_indices=None):
    L0,L1,star,hc,model,shape=map(A,("115.033663",last,upper_log,cell,constant,warp))
    H=arb(3000175332800)
    logH=H.log()
    if quarter_indices:
        qidx=[int(x) for x in quarter_indices.split(",")]
        if not all(j>i>=0 for i,j in zip([0]+qidx[:-1],qidx,strict=True)):
            raise ValueError("positive increasing height indices")
        cond_u=[logH]+[logH+arb(j)/4 for j in qidx]
        star,count=cond_u[-1],len(qidx)
    else:
        cond_u=[logH+(star-logH)*(arb(i)/count)**shape for i in range(count+1)]
    if not (star>logH and hc>0 and count>0 and height_sub>=1 and 1<=beta_step<=75 and
            model>=0 and shape>=1 and L1>L0):
        raise ValueError("box geometry")
    indices=range(800,875,beta_step) if beta_list is None else [int(x) for x in beta_list.split(",")]
    if not indices or indices[0]!=800 or not all(800<=x<y<=875 for x,y in zip(indices,list(indices[1:])+[875])):
        raise ValueError("increasing real-part knots beginning at .800")
    beta=[arb(i)/1000 for i in indices]+[A("7/8")]
    end=arb(55)
    if not star<end:
        raise ValueError("final logarithmic height")
    # Separated directions: actual counts at coarse proved/tested ordinates,
    # integration on the finer mesh. Early bins are capped at the next test.
    inner=[cond_u[j]+(cond_u[j+1]-cond_u[j])*k/height_sub
           for j in range(count) for k in range(height_sub)]+[star]
    nfar=int((4*(end-star)).upper().ceil().unique_fmpz())
    rest=[star+(end-star)*i/nfar for i in range(1,nfar+1)]
    all_u=inner+rest
    heights=[u.exp() for u in all_u]
    low,far=curves(star,True),curves(star,False,short_core)
    cheap=[cumulative_coefficients(low,u) for u in inner[1:]]
    known=[cumulative_coefficients(far,u) for u in rest]
    final=tail_coefficients(far,end)
    conditional=[]
    for u in cond_u[1:]:
        conditional.append([model*u*(3*(1-s)/(3*s-1)*u).exp() for s in beta[:-1]])
    joint=low[0][:-1]+beta
    if convex:
        for j,c in enumerate(cheap):
            upper=conditional[j//height_sub]
            hs=[arb(0)]
            for si,ti,z in reversed(list(zip(beta,beta[1:],upper))):
                hs.append(hs[-1]+(ti-si)*z)
            cheap[j]=[c[0]]+chord_bounds(joint,c[1:]+list(reversed(hs)))[:-1]
        known=[[c[0]]+chord_bounds(far[0],c[1:]+[arb(0)])[:-1] for c in known]
        final=[final[0]]+chord_bounds(far[0],final[1:]+[arb(0)])[:-1]
    d0=(4*(-L0/4).exp()).log1p()
    cap=cap_table(d0)
    if not (4*(-L1/4).exp()).log1p()*heights[-1]>192:
        raise ArithmeticError("the continuous last tail must be quadratic")
    maximum=arb(0)
    ncell=int(((L1-L0)/hc).upper().ceil().unique_fmpz())
    worst=None
    for k in range(ncell):
        a,b=L0+k*hc,(L0+(k+1)*hc).min(L1)
        d=(4*(-b/4).exp()).log1p()
        small,large=weights(low,a),weights(far,a)
        # The last lower-strip chord continues linearly above .800, so only
        # the successive increments of the positive residual are still owed.
        final_slope=sum(small[1:])
        bdiff=[((s-1)*a).exp()*((t-s)*a).expm1()-final_slope*(t-s)
               for s,t in zip(beta,beta[1:])]
        if not all(w>0 for w in bdiff):
            raise ArithmeticError("positive increments of the high-strip residual")
        vcond=[dot(bdiff,c) for c in conditional]
        if convex:
            small=weights([joint],a)
        caps=[cap(d*t) for t in heights]
        total=arb(0)
        for i in range(len(caps)-1):
            jump=(caps[i]-caps[i+1]).max(arb(0))
            if jump.is_zero():
                continue
            if i<len(cheap):
                z=dot(small,cheap[i])+(0 if convex else vcond[i//height_sub])
            else:
                z=dot(large,known[i-len(cheap)])
            total+=jump*z
        total+=caps[-1]*dot(large,final)
        total=2*(total+(-a/2).exp()*H*logH)
        eps=4*(-a/4).exp()
        powers=(1+eps)**A("1.5")*(b+eps.log1p())**2*(-a/4).exp()/(6*arb(2).log())
        total+=powers+(-3*a).exp()/(1-(-2*a).exp())
        if total>maximum:
            maximum=total
            worst=(a,b)
        else:
            maximum=maximum.max(total)
    print("upper log height",star.str(14),"rectangles",count*(len(beta)-1),"budget",maximum.str(16),
          "worst cell",tuple(x.str(11) for x in worst),flush=True)
    return maximum


if __name__=="__main__":
    cli=argparse.ArgumentParser()
    cli.add_argument("--upper-log",default="41.6")
    cli.add_argument("--count",type=int,default=8)
    cli.add_argument("--beta-step",type=int,default=13)
    cli.add_argument("--cell",default="1/8")
    cli.add_argument("--height-sub",type=int,default=10)
    cli.add_argument("--constant",default="6")
    cli.add_argument("--warp",default="2")
    cli.add_argument("--last",default="167.4")
    cli.add_argument("--short-core",type=int,default=0)
    cli.add_argument("--convex",action="store_true")
    cli.add_argument("--beta-list")
    cli.add_argument("--quarter-indices")
    cli.add_argument("--diagnose",action="store_true")
    if len(sys.argv)==1:
        cli.set_defaults(quarter_indices="1,4,9,17,30,51",beta_list="800,820,837,852,865",
                         height_sub=12,convex=True,short_core=32768,cell="1/16")
    args=vars(cli.parse_args())
    diagnose=args.pop("diagnose")
    ctx.prec=160
    result=test(**args)
    if not diagnose and not result<1:
        raise ArithmeticError("finite rectangles do not give a strict unit budget")
