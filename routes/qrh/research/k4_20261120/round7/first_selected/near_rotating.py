"""Cumulative zero mass above H using a rotating polynomial on a translated strip."""
from flint import arb,ctx
from near_phase import H,RESEARCH,rv_count,angular_edge,old_weights,chord_bounds,weights,dot
from near_height import left,right
import sys
sys.path.insert(0,str(RESEARCH/'round8'/'zero_strip'))
from rotating import price


def cumulative(location,cut,signed=False):
    size=cut+1
    R=arb(size)/2
    U=R.log()
    assert U>20 and 8192<R
    flat=((1+2/R)/arb('1.01'))**2048
    # Normalize the analytic window by 1+eps so that the tabulated edge
    # moments majorize its full-axis norms without an extra multiplicative cost.
    assert (1+arb('1e-6'))*(1+flat)*(1+1/(arb(H)-1))-1<arb('2e-6')
    # Both actual axis integrals are twice the stored translated half moments.
    old,_=old_weights(location,size,'.73','7.8','-2.65',6,True)
    sources=[(arb('.73'),arb('7.8'),arb('-2.65'),210,*old[2:4])]
    d,w,h=arb('.88'),arb(8),arb('-2.5')
    lm=left(H,size,'8','-2.5',30,'1.5',8192,ctx.prec,210)
    rm=U*right(U,U,d,w,h,64,210,causal='real',cutoff=95)
    sources.append((d,w,h,210,lm,rm))
    nodes=[arb(i)/1000 for i in range(650,875,2)]+[arb(7)/8]
    values=[]
    for d,w,h,q,l,r in sources:
        # The archived Jensen edge uses degree per target root eight, whereas
        # (1+z)(1-z/8)^8 has degree nine and a simple root at -1.
        edge=9*angular_edge(U,U,w,h,height_top=arb(H+size),length_factor=2,q=q)/8
        lm,rm=2*l/(U**2*R),2*r/U
        row=[price(U,arb(1)/2,d,lm,rm,s)[0] for s in nodes[:-1]]
        if signed:
            from rotating_signed import signed_price
            V=U.max(25).max(((H+3*R+4)/4).log())
            assert q*(U+w+h).exp()<=(3*V).exp()
            assert H+3*R+3<4*V.exp()
            row=[x.min(signed_price(U,arb(1)/2,d,lm,rm,s,V=V)[0])
                 for x,s in zip(row,nodes[:-1],strict=True)]
        values.append([x+edge for x in row])
    vals=chord_bounds(nodes,[a.min(b) for a,b in zip(*values,strict=True)]+[arb(0)])
    l=arb(location)
    wt=weights([nodes],l)
    # The lower edge lies in [H,H+.1] and the upper edge can be taken above
    # H+cut inside H+size. Pay the possibly omitted lower strip separately.
    return wt[0]*rv_count(arb(size))+dot(wt[1:],vals[:-1])+rv_count(arb('.1'))*(-l/8).exp()
