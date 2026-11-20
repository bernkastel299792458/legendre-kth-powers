"""Certify an irregular finite subset of the C=6 zero-count target."""
from pathlib import Path
import argparse
from flint import arb,arb_mat,ctx
from tables import (A,H,LOW,LAST,conditions,get_data,validate_slabs,short_caps,horizons)
from grid_target import cap_table,weights,dot,chord_bounds

# Strict subset of the former thirty rectangles. Each pair is (quarter-height, milli-abscissa).
OLD_TWENTY=([(k,s) for k in (4,9,17) for s in (800,820,837,852,865)]+
            [(30,s) for s in (837,852,865)]+[(51,s) for s in (852,865)])
ELEVEN=[(5,867),(7,833),(7,852),(8,820),(10,862),(13,809),(13,846),(20,831),
        (23,864),(29,852),(46,856)]
NINE=[(5,866),(6,828),(7,849),(10,860),(11,814),(14,844),(20,833),(23,863),(37,854)]
EIGHT=[(5,854),(7,835),(9,867),(10,815),(13,848),(17,830),(22,863),(36,854)]
SEVEN=[(5,854),(7,866),(9,835),(12,847),(14,825),(20,863),(33,853)]

def necessary_nine():
    h=arb(H).log()
    minimum=[]
    for k,m in NINE:
        rhs=conditions(h+arb(k)/4,arb(m)/1000)
        n=rhs.floor().unique_fmpz()+1
        assert n is not None and n-1<rhs and rhs<n
        minimum.append(int(n))
    assert minimum==[339119,6660579,1375091,755166,36857291,3650124,15924519,1544814,9613571]
    top=arb(H)*(arb(37)/4).exp()
    assert 31215521411322038<top and top<31215521411322039
    print("least count at a failing rectangle",min(minimum),"strict common ordinate ceiling",
          31215521411322039,"floor-plus-one at each rectangle",*minimum,flush=True)

def parse_grid(text):
    return [tuple(map(int,word.split(":"))) for word in text.split(",")]

def call_rows(marks,heights,rows,s,nheight,conditions_fn=conditions):
    assert len(marks)==len(set(marks)) and all(1<=k<=66 and 800<=m<=874 for k,m in marks)
    h=heights[0]
    tested=[(k,m,arb(conditions_fn(h+arb(k)/4,arb(m)/1000))) for k,m in marks]
    assert all(c>=0 for _,_,c in tested)
    out=[]
    for ix,(index,known) in enumerate(zip(horizons(heights,nheight),rows,strict=True)):
        cap=None
        at={}
        for k,m,c in tested:
            if index<=k*(nheight//4):
                at[m]=c if m not in at else at[m].min(c)
        by_real=[]
        for j in range(650,875):
            if j in at: cap=at[j] if cap is None else at[j].min(cap)
            if index<0:
                c=short_caps(index,j,h)
                if c is not None: cap=c if cap is None else cap.min(c)
            by_real.append(cap)
        val=known.copy()
        for j in range(len(s)-2,-1,-1):
            if by_real[j] is not None:
                val[j]=val[j].min(val[j+1]+(s[j+1]-s[j])*by_real[j])
        out.append(chord_bounds(s,val)[:-1])
    return out

def certify(marks,nheight=16,cell="1/8",first=LOW,last=LAST,details=False,folded=False,moving=False,
            conditions_fn=conditions,phased=False,fine=False,symmetric=False):
    A0,A1,width=A(first),A(last),A(cell)
    assert A0>=arb(115) and A0<A1 and A1<=arb(163) and width>0
    hs,base,s,z,far,final=get_data(nheight,folded=folded,moving=moving,phased=phased,fine=fine)
    rows=call_rows(marks,hs,z,s,nheight,conditions_fn=conditions_fn)
    C=arb_mat(rows).transpose()
    h=hs[0]
    height=[u.exp() for u in hs]
    cap=cap_table((4*(-A0/4).exp()).log1p())
    assert (4*(-A1/4).exp()).log1p()*height[-1]>192
    ncell=int(((A1-A0)/width).upper().ceil().unique_fmpz())
    high=arb(0)
    worst=0
    # Multiply only small batches of real cells so large grids have bounded memory use.
    for i in range(0,ncell,48):
        cells=[(A0+j*width,(A0+(j+1)*width).min(A1)) for j in range(i,min(ncell,i+48))]
        W=[weights([s],a) for a,b in cells]
        if symmetric:
            for w,(a,_) in zip(W,cells,strict=True):
                w[0]=(w[0]+(-s[0]*a).exp())/2
        Z=arb_mat([w[1:] for w in W])*C
        for j,(a,b) in enumerate(cells):
            eps=4*(-a/4).exp()
            d=(4*(-b/4).exp()).log1p()
            E=[cap(d*t) for t in height]
            total=E[-1]*dot(weights(far,a),final)
            for k,(l,r) in enumerate(zip(E,E[1:])):
                if l.is_exact() and r.is_exact() and l==r: continue
                total+=(l-r).max(arb(0))*(Z[j,k]+W[j][0]*base[k])
            total=2*(total+(-a/2).exp()*arb(H)*h)
            total+=(1+eps)**A("1.5")*(b+eps.log1p())**2*(-a/4).exp()/(6*arb(2).log())
            total+=(-3*a).exp()/(1-(-2*a).exp())
            if total>high: worst=i+j
            high=high.max(total)
    print("rectangles",len(marks),"interval",first,last,"full budget",high.str(18),
          "worst-cell left endpoint",(A0+worst*width).str(12),flush=True)
    if details: print(" ".join(f"{k}:{m}" for k,m in sorted(marks)),flush=True)
    return high

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--grid")
    cli.add_argument("--old-twenty",action="store_true")
    cli.add_argument("--nine",action="store_true")
    cli.add_argument("--eight",action="store_true")
    cli.add_argument("--seven",action="store_true")
    cli.add_argument("--nheight",type=int,default=32)
    cli.add_argument("--cell",default="1/32")
    cli.add_argument("--first",default=LOW)
    cli.add_argument("--last",default=LAST)
    cli.add_argument("--diagnose",action="store_true")
    cli.add_argument("--folded",action="store_true")
    cli.add_argument("--moving",action="store_true")
    cli.add_argument("--phased",action="store_true")
    cli.add_argument("--fine",action="store_true")
    cli.add_argument("--symmetric",action="store_true")
    args=cli.parse_args()
    ctx.prec=160
    assert sum((args.old_twenty,args.nine,args.eight,args.seven,args.grid is not None))<=1
    if args.nine:
        assert not args.old_twenty and not args.eight and args.grid is None
        args.last,args.folded,args.nheight,args.cell="155",True,48,"1/48"
    if args.eight:
        assert not args.old_twenty and args.grid is None
        args.last,args.phased,args.nheight,args.cell="152",True,24,"1/24"
    if args.seven:
        args.last,args.phased,args.fine,args.nheight,args.cell="150",True,True,32,"1/32"
    validate_slabs(args.folded,args.phased)
    assert not (args.old_twenty and args.grid is not None)
    marks=(parse_grid(args.grid) if args.grid is not None else
           OLD_TWENTY if args.old_twenty else SEVEN if args.seven else
           EIGHT if args.eight else NINE if args.nine else ELEVEN)
    value=certify(marks,args.nheight,args.cell,args.first,args.last,True,args.folded,args.moving,
                  phased=args.phased,fine=args.fine,symmetric=args.symmetric)
    if not args.diagnose: assert value<1
    if args.nine:
        ctx.prec=200
        necessary_nine()
    if args.eight:
        ctx.prec=200
        u=arb(H).log()
        targets=[int(conditions(u+arb(k)/4,arb(m)/1000).floor().unique_fmpz())+1 for k,m in EIGHT]
        upper=(u+9).exp().ceil().unique_fmpz()
        assert targets==[805225,4129646,419084,30338374,2425723,15807615,1437583,8903719]
        assert upper==24310672519119809 and upper-1<(u+9).exp() and (u+9).exp()<upper
        print("necessary count in the common strip",min(targets),"strict common ordinate ceiling",upper)
    if args.seven:
        ctx.prec=200
        u=arb(H).log()
        rhs=[conditions(u+arb(k)/4,arb(m)/1000) for k,m in SEVEN]
        targets=[805225,390987,4947660,2421680,18554685,1244734,7746164]
        assert all(t-1<v and v<t for v,t in zip(rhs,targets,strict=True))
        top=(u+arb(33)/4).exp()
        assert 11483548572672344<top and top<11483548572672345
        print("necessary count in the common strip",min(targets),
              "strict common ordinate ceiling",11483548572672345,
              "floor-plus-one at each rectangle",*targets,flush=True)
