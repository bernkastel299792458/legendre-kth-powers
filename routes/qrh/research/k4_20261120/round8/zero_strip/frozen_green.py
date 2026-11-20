"""Scalar and cosine-weighted Gabriel rows from a certified moving-line export."""
from functools import lru_cache
import json
from pathlib import Path

from flint import arb

from weighted_green import H,interpolated_point
from grid_target import chord_bounds,curves,tail_coefficients


class Book:
    def __init__(self,filename,shifts='all',rotate=False):
        data=json.loads(Path(filename).read_text(encoding='utf8'))
        self.scale=data['scale'];self.sub=data['sub']
        self.rotate=rotate
        assert self.scale>0 and self.sub>0
        self.rows={int(k):v for k,v in data['rows'].items()}
        self.params=[tuple(map(arb,t)) for t in data['triples']]
        supplied=data['steps']
        requested=supplied if shifts=='all' else shifts.split(',')
        self.shifts=[(i,arb(h)) for i,h in enumerate(supplied) if h in requested]
        assert all(h in supplied for h in requested)

    @lru_cache(maxsize=None)
    def row(self,k):
        data=self.rows[k];out=[]
        for idx,(pars,pair,shifted,edge) in enumerate(zip(self.params,data['moments'],data['left_shifts'],data['angular_edges'],strict=True)):
            d=pars[0];l,r=(arb(n)/self.scale for n in pair);edge=arb(edge)/self.scale
            assert min(l,r,edge)>0
            out.append((d,l,r,edge,arb(1)/2,idx))
            if shifted:
                for j,h in self.shifts:
                    assert 0<h<arb('.1') and shifted[j]>0
                    out.append((d,arb(shifted[j])/self.scale,r,edge,arb(1)/2-h,idx))
        return out

    def at(self,U):
        # The Green rectangle uses exp(U)=T+.1, strictly inside its own slab.
        ix=(U*self.sub).floor().unique_fmpz()
        assert ix is not None and U>=arb(ix)/self.sub and U<=arb(ix+1)/self.sub
        if int(ix) not in self.rows:return []
        return self.row(int(ix))

    @lru_cache(maxsize=2)
    def spectrum(self,low,high,nh,sub,step):
        assert nh>0 and sub>0 and step>0
        nodes=[arb(i)/2000 for i in range(1300,1750,step)]+[arb(7)/8]
        pi=arb.pi();logh=arb(H).log();known=arb(H)*((arb(H)/(2*pi)).log()-1)/(2*pi)
        norm=((1+arb('1e-6'))**2/(1-1/arb(3*10**12))).log()
        assert logh<low and 8192<arb(low).exp()
        assert ((1+2/arb(low).exp())/arb('1.01'))**2048<arb('1e-6')
        if self.rotate:assert ((1+2/arb(low).exp())/arb('1.01'))**2048<arb('1e-7')
        assert 1/(1-(arb('.5')+2/arb(low).exp())**2048)<1+arb('1e-6')
        T=[arb(low).exp()];counts=[];rows=[]
        for j in range(1,(high-low)*sub*nh+1):
            u=low+arb(j)/(sub*nh);t=u.exp();T.append(t)
            # The nominal scalar freeze at a shared endpoint may use the slab on its left.
            k=low*self.sub+(j*self.sub-1)//(sub*nh)
            assert arb(k)/self.sub<=u<=arb(k+1)/self.sub
            counts.append(t*((t/(2*pi)).log()-1)/(2*pi)-known+arb('.15')*(logh+u)+6)
            data=[]
            for d,l,r,e,ell,family in self.row(k):
                if self.rotate=='signed':
                    _,width,logh0=self.params[family]
                    assert arb(2310).log()+u+width+logh0<3*u and 2*t+3<4*t
                R=1+d/u;data.append((R,R-ell,ell,l.log()+u+2*u.log(),r.log()+u.log(),e))
            vals=[]
            for s in nodes[:-1]:
                best=None
                for R,span,ell,ll,lr,edge in data:
                    if ell<arb(1)/2 and not s>arb(3)/4:continue
                    th=(R-s)/span;P=3*th/(2+th);nu=4/(2+th)
                    assert 0<P<1
                    value=interpolated_point(nu)*(nu*norm+P*ll+(1-P)*lr).exp()/(2*pi)+edge
                    if self.rotate:
                        from rotating import logprice
                        if self.rotate=='signed':
                            from rotating_signed import signed_logprice
                            candidate=signed_logprice(u,ell,R,ll,lr,s)[0]
                        else:candidate=logprice(ell,R,ll,lr,s)[0]
                        value=value.min(candidate+9*edge/8)
                    best=value if best is None else best.min(value)
                vals.append(best)
            rows.append(chord_bounds(nodes,vals+[arb(0)])[:-1])
        for j in range(len(rows)-2,-1,-1):
            rows[j]=[a.min(b) for a,b in zip(rows[j],rows[j+1],strict=True)]
        F=curves(arb(high),False,32768);final=tail_coefficients(F,arb(high))
        final=[final[0]]+chord_bounds(F[0],final[1:]+[arb(0)])[:-1]
        return (T,counts,nodes,rows,F,final),self.at
