"""Compact bridge using local height ranges and rowwise minima of complete detectors."""

import argparse
from functools import lru_cache
from pathlib import Path
import sys
from flint import arb,ctx

here=Path(__file__).resolve().parent
sys.path.insert(0,str(here.parent/"spectrum"))
from verify import A,moments,local_right_rows,direct_high
from height_budget import select_knots,coefficient,quintic_bound
from short_block import cm_local,normalized_row,split_endpoint
from mixed_low import mixed_low_rows
from polygon import envelope


REGISTERED=".92,9.5,-3.5;1,9.25,-3.5;1.1,8.75,-3.5;.96,9.5,-3.65;1.04,9,-3.4"


def modest_right(U,V,delta,W,logh,cells,*,q=210,frequency_cut="100"):
    first=min(cells-1,int((cells*U/V).lower().floor().unique_fmpz()))
    low=mixed_low_rows(U,delta,W,W,arb(0),logh,q,cells=cells,tight=True,first=first)
    extra={} if q==210 else dict(spacing=210,outer_spacing=q,frequency_cut=frequency_cut)
    hilbert,rows,tail=local_right_rows(U,delta,W,logh,q,cells=cells,**extra)
    high=direct_high(U,delta,W,logh,q)
    best=arb(0)
    for i,(l,r) in enumerate(zip(low,rows[first:],strict=True),start=first):
        e=2*delta*(i+1)/(U*cells)
        if e<2*delta/V:
            continue
        z=(-2*delta-e*logh).exp()*(hilbert*l+(r+tail*high)*e/(2*delta))
        best=best.max(z)
    assert best>0
    return best


@lru_cache(maxsize=512)
def cached_fourth(index,prec,use_unit):
    if use_unit:
        from unit_diagonal import fourth
    else:
        from off_fourth import fourth
    assert prec==ctx.prec
    return fourth(arb(index)/10**6)


def corrected_fourth(U,use_unit=False):
    index=int((U*10**6).lower().floor().unique_fmpz())
    return cached_fourth(index,ctx.prec,use_unit)


def row_constants(U,V,delta,W,logh,ncore,use_off,use_unit,cells):
    opts=dict(fourth_fn=lambda u:corrected_fourth(u,use_unit)) if use_off or use_unit else {}
    if V is None:
        def short(u,w,h,q):
            return split_endpoint(u,w,h,q,ncore,cm_local,**opts)[0]
        left,right=moments(U,delta,W,logh,210,"100",short=short,tight=True)
    else:
        pieces=int((2*(V-U)).upper().ceil().unique_fmpz())
        left=arb(0)
        for j in range(pieces):
            l,h=U+(V-U)*j/pieces,U+(V-U)*(j+1)/pieces
            left=left.max(normalized_row(l,h,210,ncore,W,logh,cm_local,**opts)[0])
        right=modest_right(U,V,delta,W,logh,cells)
    assert left>right>0 and 9/((U+logh)/2).exp()<arb(1)/4 and 210*(W+logh).exp()>=1
    edge=162*(-logh).exp()/(2*arb.pi())
    edge+=2*(2+(arb(2).log()+9*(11*arb(210).sqrt()*((W+logh)/2).exp()).log())/A("15/14").log())
    return delta,left,right,edge


def spectrum(d,dend,subdivide=1):
    floor=A("1.45")
    base=[floor,arb(2),arb(4),arb(8),arb(16),arb(64),arb(192)]
    cuts=[floor]
    for l,h in zip(base,base[1:]):
        cuts.extend(l+(h-l)*m/subdivide for m in range(1,subdivide))
        cuts.append(h)
    jump,res=envelope(d,256,192)
    blocks=[[] for _ in cuts]
    for y,w in jump:
        y=y.max(floor)
        j=next(j for j,end in enumerate(cuts[1:]) if y<=end)
        blocks[j].append(((y/4).log(),w))
    u=(4/d).log()
    def weights(p,r):
        h=p+r/u
        assert h<2
        scale=(p*u+r*u.log()).exp()
        out=[scale*sum((w*(h*x).exp() for x,w in row),arb(0)) for row in blocks[:-1]]
        return out+[scale*res*(h*(cuts[-1]/4).log()).exp()*2/(2-h)]
    windows=[((l/d).log()-A("1e-7"),(h/dend).log()+A("1e-7")) for l,h in zip(cuts,cuts[1:])]
    return weights,windows+[((cuts[-1]/d).log()-A("1e-7"),None)]


def verify(anchor="162.3",last="167.4",param=REGISTERED,core=2097152,step=2,radial=True,off=True,unit=True,cells=128,subdivide=1,*,row_provider=None):
    L,end=A(anchor),A(last)
    assert 0<L<end and core>0 and step>=1 and cells>=1 and subdivide>=1
    eps=4*(-L/4).exp()
    d=eps.log1p()
    weight,windows=spectrum(d,(4*(-end/4).exp()).log1p(),subdivide)
    umin=windows[0][0]
    T=umin.exp()
    assert T>arb(3000175332800) and 8192/T<1 and ((1+2/T)/A("1.01"))**2048<A("1e-6")
    assert 1/(1-(A(".5")+2/T)**2048)<1+A("1e-6")
    norm=(1+A("1e-6"))**2/(1-1/arb(3*10**12))
    args=[tuple(map(A,k.split(","))) for k in param.split(";")]
    provider=row_constants if row_provider is None else row_provider
    constants=[[provider(U,V,*pars,core,off,unit,cells) for pars in args] for U,V in windows]
    zero,logs=weight(arb(0),arb(0)),weight(arb(0),arb(1))
    g=27/A("15/14").log()
    rows=[[] for _ in windows]
    knots=[arb(i)/2000 for i in range(1300,1750,step)]+[A("7/8")]
    for s in knots[:-1]:
        p=3*(1-s)/(2-s)
        wt=weight(p,1+p)
        for i,((U,V),choices) in enumerate(zip(windows,constants,strict=True)):
            best=None
            for delta,left,right,ec in choices:
                c=3*delta/(2-s)
                k=3*delta*(2*s-1)/(2-s)**2
                lo=(2+4*delta/U)/(2-s+3*delta/U)
                hi=2/(2-s) if V is None else (2+4*delta/V)/(2-s+3*delta/V)
                assert A("1.4")<=lo and hi<=A("16/9") and c+1+c/U<(U*left/right).log()
                cd=None
                if radial:
                    from radial_detectors import bound
                    cd=bound(lo,hi)
                if cd is None:
                    cd=coefficient(lo,hi)
                    alt=quintic_bound(lo,hi)
                    if alt is not None:
                        cd=cd.min(alt)
                B=cd*norm**hi*right*(left/right)**p
                B*=(k*(U+(U*left/right).log())/(U+c)).exp()/(2*arb.pi())
                cost=B*wt[i]+ec*zero[i]+g*logs[i]
                best=cost if best is None else best.min(cost)
            rows[i].append((s,best))
    total=2*((knots[0]-1)*L).exp()*sum(weight(arb(1),arb(1)))
    assert knots[0]-1+A("1/4")+1/(4*umin)<0
    for row in rows:
        selected=select_knots(row+[(knots[-1],arb(0))])
        old=arb(0)
        for (s,val),(t,_) in zip(selected,selected[1:]):
            p=3*(1-s)/(2-s)
            slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
            assert slope>old and t-1+2/L+p/4+(1+p)/(4*umin)<0 and t-1+2/L+1/(4*umin)<0
            total+=2*(slope-old)*val
            old=slope
    assert 2/L<arb(1)/4
    total+=(1+eps)**A("1.5")*(L+d)**2*(-L/4).exp()/(6*arb(2).log())
    total+=(-3*L).exp()/(1-(-2*L).exp())
    print("bridge",anchor,"through",last,"total",total.str(18),flush=True)
    return total


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",default="162.3")
    cli.add_argument("--last",default="167.4")
    cli.add_argument("--param",default=REGISTERED)
    cli.add_argument("--core",type=int,default=2097152)
    cli.add_argument("--step",type=int,default=2)
    cli.add_argument("--cells",type=int,default=128)
    cli.add_argument("--subdivide",type=int,default=1)
    cli.add_argument("--diagnose",action="store_true")
    cli.add_argument("--radial",action=argparse.BooleanOptionalAction,default=True)
    cli.add_argument("--off",action=argparse.BooleanOptionalAction,default=True)
    cli.add_argument("--unit",action=argparse.BooleanOptionalAction,default=True)
    args=vars(cli.parse_args())
    diagnose=args.pop("diagnose")
    ctx.prec=160
    result=verify(**args)
    if not diagnose and not result<1:
        raise ArithmeticError("no strict bridge")
    if not diagnose:
        L=A(args["anchor"])
        first=(L/4).exp().ceil().unique_fmpz()
        assert first is not None and 4*arb(first-1).log()<L<4*arb(first).log()
        print("first integer",first,flush=True)
