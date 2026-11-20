"""Height and abscissa tables used by exact certification and optional search."""
from math import ceil
from flint import arb
from slabs import A,H,LOW,LAST,SLABS,TRIPLE,SCALE,radial
from grid_target import curves,cap_table,tail_coefficients,chord_bounds
from finite_anchor import row_constants

LEFT=(246094407789,221798112260,163227791432,140878203063,128140105297,119316835255,
      112684955423,107444942869,103151967776,99536939851,96429995917,93719209568,
      91327103519,89197811456)
RIGHT=(7236977625,6667947916,6271839263,6107842821,6027002799,5978069811,5942947646,
       5914216006,5890225199,5869087796,5848057061,5827886809,5808832222,5790755175)
EC=2983725290305253
EXTRA=(153327569938,125409170936,98726915274,82563196445,71421610838,64633886617,
       60695856290,58139459016,56305097840,54890461456,53742514721,52776337203,
       51941668597,51206989219)

PHASED=(92127253944,74094359024,60604863935,53162011676,48508739973,45223436642,
        43033287582,41426731091,40143012559,39067171024,38141894002,37333733860,
        36620458189,35985962207)

def validate_slabs(folded=False,phased=False):
    for (lo,hi),l,r in zip(SLABS,LEFT,RIGHT,strict=True):
        U=A("28.7") if lo==28 else arb(lo)
        delta,x,y,ec=row_constants(U,arb(hi),*map(A,TRIPLE),32768,True,True,16)
        assert x*SCALE<l and y*SCALE<r and ec*SCALE<EC
    if phased or folded:
        from slabs import extra_constants
        for (_,_,bound),cap in zip(extra_constants(phased),PHASED if phased else EXTRA,strict=True):
            assert bound<=cap

def angular_edge(U,V,w=None,lh=None,height_top=None,length_factor=1,q=210):
    """Complete horizontal and right edges uniform on U <= log(T) <= V."""
    pi=arb.pi()
    if w is None: _,w,lh=map(A,TRIPLE)
    yl=(U+lh).exp()
    xu=(V+lh+w).exp()
    top=(V.exp() if height_top is None else height_top)+7
    Hlo=arb(H)-2
    assert q in (210,2310)
    r=A("1.86")
    d=A("1.35")
    a2=2*(yl.log()+2)/yl
    assert (1+a2)**15<arb(3)/2 and U+lh+2>2
    right=length_factor*4*(U+lh+2)**2*(-U-2*lh).exp()/pi
    mean=arb(0)
    for k in range(1,97):
        s=2+r*(pi*k/96).cos()
        assert s>0
        e=(1-s).max(arb(0))
        z=top**e*(1+top.log()+1/Hlo+1/s)
        poly=xu**e*(1+xu.log())
        euler=arb(1)
        for p in (2,3,5,7,11):
            if q%p==0:euler*=1+arb(p)**(-s)
        f=1+z*poly*euler
        if s>1:
            diff=s-1
            f=f.min(yl**(-diff)*s*((1+yl.log())/diff+1/diff**2))
        mean+=f.log1p()/96
    geo=d/48*sum(1/(r/(d*j/48)).log() for j in range(1,49))
    return right+2*d+geo*(arb(2).log()+8*mean)

def get_data(nheight=16,nreal=1,terminal=55,folded=False,moving=False,phased=False,fine=False):
    assert nheight>0 and nheight%4==0 and nreal==1 and terminal==55
    h=arb(H).log()
    zero_free,short1,short2=[(arb(H)+d).log() for d in (32,5000000,6500000)]
    periods=int(((terminal-h)*nheight).lower().floor().unique_fmpz())
    heights=[h,zero_free,short1,short2]+[h+arb(i)/nheight for i in range(1,periods+1)]+[arb(terminal)]
    knots=list(range(650,876))
    real=[arb(i)/1000 for i in knots]
    norm=(1+A("1e-6"))**2/(1-1/arb(3*10**12))
    delta=A(TRIPLE[0])
    base=[]
    rows=[]
    g=27/A("15/14").log()
    edges=[angular_edge(A("28.7") if lo==28 else arb(lo),arb(hi)) for lo,hi in SLABS]
    for j,u in enumerate(heights[1:]):
        i=next(i for i,(_,hi) in enumerate(SLABS) if u<=hi)
        T=u.exp()
        def F(t):
            return t*((t/(2*arb.pi())).log()-1)/(2*arb.pi())
        base.append(F(T)-F(arb(H))+A(".15")*(u+h)+6)
        ls=PHASED if phased else EXTRA if folded else LEFT
        l,r=arb(min(LEFT[i],ls[i]))/SCALE,arb(RIGHT[i])/SCALE
        edge=(arb(EC)/SCALE+g*u).min(edges[i])
        logleft=(T*u**2*l).log()
        logright=(r*u).log()
        assert 8192/H<1 and ((1+arb(2)/H)/A("1.01"))**2048<A("1e-6")
        assert 1/(1-(A(".5")+arb(2)/H)**2048)<1+A("1e-6")
        out=[]
        for s in real[:-1]:
            den=2-s+3*delta/u
            nu=(2+4*delta/u)/den
            p=3*(1-s+delta/u)/den
            cd=radial(nu,nu)
            assert cd is not None and 0<p and p<1
            out.append(cd*(nu*norm.log()+p*logleft+(1-p)*logright).exp()/(2*arb.pi())+edge)
        out.append(arb(0))
        if fine:
            from fine_intervals import improve
            out=improve(u,real,out)
        if moving and u-h<2:
            from centered import centered
            from flint import ctx
            k=max(1,(8*max(0,j-2)+nheight-1)//nheight)
            out=[x.min(y) for x,y in zip(out,centered(k,8,ctx.prec),strict=True)]
        rows.append(out)
    far=curves(arb(terminal),False,32768)
    final=tail_coefficients(far,arb(terminal))
    final=[final[0]]+chord_bounds(far[0],final[1:]+[arb(0)])[:-1]
    return heights,base,real,rows,far,final

def conditions(u,s,coefficient=6):
    return coefficient*u*(3*(1-s)/(3*s-1)*u).exp()

def horizons(heights,nheight):
    # short cells use indices -3,-2,-1, every positive index is in units 1/nheight.
    return [-3,-2,-1]+list(range(1,len(heights)-3))

def short_caps(index,s,h):
    if index==-3 and s>=800:
        return arb(0)
    if index<=-2 and s>=800:
        return conditions(h,arb(s)/1000,7)
    if index<=-1:
        marked=[j for j in (800,813,826,839,852,865) if j<=s]
        if marked:
            return conditions(h,arb(marked[-1])/1000)
    return None
