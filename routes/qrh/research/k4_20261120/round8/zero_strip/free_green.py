"""Optimize every source mean and nodal harmonic of a single Green detector."""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csr_matrix,hstack,vstack
from flint import arb
from functools import lru_cache
from types import FunctionType

_proposals={}


@lru_cache(maxsize=1)
def extended_table(prec):
    from radial_detectors import caps
    original=caps.__wrapped__
    fn=FunctionType(original.__code__,dict(original.__globals__,LOW=350,HIGH=378),original.__name__,original.__defaults__)
    return fn(prec)


def extended_radial(allrad,nu,prec):
    from weighted_green import radial,RLOW
    if nu*200<=356:return [radial(line,nu) for line in allrad]
    assert nu*200>=350 and nu*200<=378
    return [radial([arb(0)]*(350-RLOW)+line,nu) for line in extended_table(prec)]


class FreeGreen:
    def __init__(self,nodes,weight,frequency,step,positive,extend=0,tight=False,source_floor='.795',more=False,scalar_mix=False,reuse_fit=False):
        assert arb(source_floor)>arb(3)/4
        self.cut=next(i for i,s in enumerate(nodes) if s>=arb(source_floor));self.x=nodes[self.cut:]
        self.w=weight[self.cut:];self.physical=len(self.w)
        assert len(self.x)==self.physical+1+extend
        self.n=n=len(self.x)-1;self.sc=self.w+[self.w[-1]]*(1+extend)
        self.R=[sum((w*(t-a).max(0) for w,a in zip(self.w,self.x)),arb(0)) for t in self.x]
        self.has_pos=positive;self.modes=(1,2,4,6) if positive else (2,4,6,8);self.plans={}
        self.sharing=False;self.reopt=False;self.rotating=False;self.optimize_rotation=False
        self.jointplans={};self.jump_data={};self.rotate_plans={}
        self.reuse_fit=reuse_fit
        self.layout=(int(float(frequency)),step,self.cut,n,positive,extend,more,scalar_mix)
        if more:self.modes+=(8,12) if positive else (12,16)
        assert all(96%m==0 for m in self.modes)
        self.cos={m:[(arb.pi()*i*m/192).cos() for i in range(193)] for m in set(self.modes)|{1}}
        self.f=frequency;self.fac={m:(m*frequency*step/2000)/(m*frequency*step/2000).sinh() for m in self.modes}
        self.h=[b-a for a,b in zip(self.x,self.x[1:])]
        self.sinh={m:[(m*frequency*g).sinh() for g in self.h] for m in self.modes}
        self.cosh={m:[(m*frequency*g).cosh() for g in self.h] for m in self.modes}
        self.tight=tight;self.derivative_coeff={}
        if tight:
            for m in self.modes:
                lo=m*frequency.lower();hi=m*frequency.upper();assert lo>0
                self.derivative_coeff[m]=[]
                for h in self.h:
                    # nu*csch(nu*h) decreases, nu*coth(nu*h) increases.
                    # Both are near 1/h on a short real-part interval.
                    cs=(lo/(lo*h).sinh()).union(hi/(hi*h).sinh())
                    ct=(lo/(lo*h).tanh()).union(hi/(hi*h).tanh())
                    self.derivative_coeff[m].append((cs,ct))
        # Proposal matrix columns are source means, then positive/negative
        # nodal amplitudes per harmonic, with natural physical scalings.
        shape=np.array([[float(w*(s-a).max(0)/r) for w,a in zip(self.sc,self.x,strict=True)] for s,r in zip(self.x[1:],self.R[1:],strict=True)])
        jumps={}
        for m in self.modes:
            q=np.zeros((n+1,n));nu=m*float(frequency)
            for j,g in enumerate(self.h):
                h=float(g);c=np.cosh(nu*h);d=nu/np.sinh(nu*h)
                if j:q[j,j-1]-=d*c;q[j+1,j-1]+=d
                q[j,j]+=d;q[j+1,j]-=d*c
            q[-1,-1]-=nu
            jumps[m]=q*np.array([float(v) for v in self.R[1:]])[None,:]/np.array([float(v) for v in self.sc])[:,None]
        self.dmat=jumps
        rows=[];rhs=[];scalar_rows=[];local_rows=[];I=np.eye(n);self.scalar_mix=scalar_mix
        phase_div=48 if more else 24
        for j in range(phase_div+1):
            t=np.pi*j/phase_div;d=[np.eye(n+1)];loc=[shape]
            for m in self.modes:
                c=np.cos(m*t);alpha=float(self.fac[m]);d.extend((c*jumps[m],-c*jumps[m]));loc.extend((min(c,alpha*c)*I,min(-c,-alpha*c)*I))
            rows.append(np.hstack(d));rhs.extend([0]*(n+1))
            if scalar_mix:scalar_rows.append(np.zeros((n+1,self.physical)))
            if positive or j<=phase_div//2:
                rows.append(np.hstack(loc));rhs.extend([max(0,np.cos(t))]*self.physical+[0]*(n-self.physical))
                if scalar_mix:scalar_rows.append(shape[:,:self.physical]);local_rows.append(rows[-1])
        self.A=csr_matrix(-np.vstack(rows));self.rhs=-np.array(rhs)
        if scalar_mix:
            alone=csr_matrix(-np.vstack(local_rows))
            self.A=vstack((hstack((self.A,csr_matrix(-np.vstack(scalar_rows)))),hstack((alone,csr_matrix((alone.shape[0],self.physical))))),format='csr')
            self.rhs=np.concatenate((self.rhs,np.zeros(alone.shape[0])))

    def train(self,estimate,normal,scalars=None,bucket=None,grid=None,rotate_grid=None):
        n=self.n
        price=np.concatenate((np.array([float(w)*v for w,v in zip(self.sc,estimate,strict=True)])/float(normal),np.full(2*n*len(self.modes),1e-9)))
        if self.scalar_mix:price=np.concatenate((price,np.array([float(z/normal) for z in scalars])))
        A,rhs=self.A,self.rhs
        original_n=len(price)
        if grid is not None:
            ml,mr=grid
            base=np.array([float(w/normal) for w in self.sc]);c=base.size
            def epigraph(mat,side):
                cols=np.zeros((len(mat),2));cols[:,side]=-1
                return hstack((csr_matrix(mat*base),csr_matrix((len(mat),A.shape[1]-c)),csr_matrix(cols)),format='csr')
            erows=[epigraph(ml,0),epigraph(mr,1)]
            A=vstack((hstack((A,csr_matrix((len(rhs),2)))),*erows),format='csr')
            rhs=np.concatenate((rhs,np.zeros(len(ml)+len(mr))))
            price[:c]*=.01;price=np.concatenate((price,[1,1]))
        if rotate_grid is not None:
            from rotating_bins import epigraph
            A,rhs,price=epigraph(A,rhs,price,self.sc,self.dmat,self.modes,rotate_grid,normal)
        key=(self.layout,bucket,grid is not None,rotate_grid is not None)
        candidate=_proposals.get(key) if self.reuse_fit else None
        if candidate is None:
            fit=linprog(price,A_ub=A,b_ub=rhs,bounds=(0,None),method='highs')
            if not fit.success:return None
            candidate=fit.x[:original_n]
            if self.reuse_fit:_proposals[key]=candidate
        src=[w*arb(float(max(0,v))) for w,v in zip(self.sc,candidate[:n+1],strict=True)];at=n+1
        V={};jump={};deriv=arb(0)
        for m in self.modes:
            a,b=candidate[at:at+n],candidate[at+n:at+2*n];at+=2*n
            v=[arb(0)]+[(arb(float(p))-arb(float(q)))*r for p,q,r in zip(a,b,self.R[1:],strict=True)];V[m]=v
            nu=m*self.f;sh=self.sinh[m];ch=self.cosh[m]
            if self.tight:
                dis=self.derivative_coeff[m]
                left=[arb(0)]+[ct*v[j+1]-cs*v[j] for j,(cs,ct) in enumerate(dis)]
                right=[cs*v[j+1]-ct*v[j] for j,(cs,ct) in enumerate(dis)]+[-nu*v[-1]]
            else:
                left=[arb(0)]+[nu*(v[j+1]*ch[j]-v[j])/sh[j] for j in range(n)]
                right=[nu*(v[j+1]-v[j]*ch[j])/sh[j] for j in range(n)]+[-nu*v[-1]]
            jump[m]=[r-l for l,r in zip(left,right,strict=True)]
            peak=arb(0)
            # Where V changes sign, V' may have an internal extremum at V=0;
            # there |V'| is a minimum, by (V'^2-nu²V²)'=0.
            for l,r,v0 in zip(left,right,v,strict=True):peak=peak.max(abs(l)).max(abs(r)).max(nu*abs(v0))
            deriv+=peak
        arc=arb.pi()**2/(8*192**2)
        for i,b in enumerate(src):
            lower=arb(0)
            for j in range(193):lower=lower.max(-sum((jump[m][i]*self.cos[m][j] for m in self.modes),arb(0)))
            err=arc*sum(m*m*abs(jump[m][i]) for m in self.modes)
            src[i]=b.max(lower+err).upper()
        separate=[arb(float(max(0,v))) for v in candidate[at:]] if self.scalar_mix else []
        G=arb(0);gslope=arb(0);individual=arb(0)
        B=arb(0);slope=arb(0);repair=arb(0)
        for i,r in enumerate(self.R[1:]):
            slope+=src[i];B+=slope*self.h[i];loss=arb(0)
            if separate and i<self.physical:gslope+=separate[i]*self.w[i]
            G+=gslope*self.h[i];zero_loss=arb(0)
            for j in range(193 if self.has_pos else 97):
                target=self.cos[1][j].max(0) if i<self.physical else arb(0)
                y=B
                for m in self.modes:
                    value=V[m][i+1]*self.cos[m][j];y+=value.min(self.fac[m]*value)
                loss=loss.max(target-(y+G)/r)
                if self.scalar_mix:zero_loss=zero_loss.max(-y/r)
            curvature=1+sum(m*m*abs(V[m][i+1])/r for m in self.modes)
            repair=repair.max(loss+arc*curvature)
            if self.scalar_mix:individual=individual.max(zero_loss+arc*(curvature-1))
        # Add the scalar repair to this same determinant to ensure nonnegativity
        # on its extra zeros as well as reward domination for the zeta zeros.
        if self.scalar_mix:
            individual=individual.upper()
            separate=[(v+(repair-individual).max(0)).upper() for v in separate]
        else:individual=repair
        for i,w in enumerate(self.w):src[i]=(src[i]+individual*w).upper()
        M=(sum(src,arb(0))+deriv).upper()
        inflated=[b*(1+2*len(self.modes)*arb('1e-6')) for b in src]
        if self.rotating:self.jump_data[id(inflated)]=(inflated,src,jump)
        return inflated,M,separate

    def saving(self,U,scalar,sources,families,caps):
        actual=[w*v for w,v in zip(self.w,scalar[self.cut:],strict=True)];total=sum(actual,arb(0))
        fields=[(sources[ids[0]][3],[caps(self.cut+j,f,1) for j in range(self.n+1)]) for f,ids in families.items()]
        k=int((2*U).mid().floor().unique_fmpz())
        if k not in self.plans:
            estimate=np.min(np.array([[[float(v) for v in row] for row in tab] for _,tab in fields]),axis=(0,2))
            self.plans[k]=self.train(estimate,total,actual,k)
        best=arb(0);proposal=None
        for j in (k,k-1):
            plan=self.plans.get(j)
            if not plan:continue
            bs,M,separate=plan
            scalar_cost=sum((a*b for a,b in zip(separate,actual)),arb(0))
            for family,(edge,tab) in zip(families,fields,strict=True):
                prices=None
                for b,row in zip(bs,tab,strict=True):prices=[M*edge+b*v for v in row] if prices is None else [y+b*v for y,v in zip(prices,row,strict=True)]
                for poly,p in enumerate(prices):
                    best=best.max(total-p-scalar_cost)
                    if self.sharing or self.rotating:
                        score=float(p+scalar_cost)
                        if proposal is None or score<proposal[0]:proposal=(score,family,poly,bs,M*edge,scalar_cost)
        if proposal is not None:
            from shared_radial import compiled_charge,proposal_matrix
            _,family,poly,bs,edgecost,scalar_cost=proposal
            other=edgecost+scalar_cost
            # Rank common auxiliary lines for this fixed detector; the final
            # selected price uses only interval arithmetic.
            chosen=None
            for idx in families[family]:
                delta,left,right,edge,*opts=sources[idx]
                ell=opts[0] if opts else arb(1)/2
                r=1+float(delta/U);l=float(ell)
                ll=float((left*U.exp()*U**2).log());lr=float((right*U).log())
                v=0.
                for a,b in zip(self.x,bs,strict=True):
                    t=(r-float(a))/(r-l);nu=4/(2+t)
                    v+=float(b)*np.exp(nu*(3*t*ll/4+(1-t)*lr/2))
                if chosen is None or v<chosen[0]:chosen=(v,delta,left,right,ell)
            _,delta,left,right,ell=chosen
            if self.rotating:
                from rotating_harmonics import plan_price,plan_rows
                _,means,jumps=self.jump_data[id(bs)]
                cost=plan_price(U,ell,delta,left,right,self.x,self.f,self.modes,means,jumps)
                best=best.max(total-9*edgecost/8-scalar_cost-cost)
                if self.optimize_rotation and k not in self.rotate_plans:
                    bins=plan_rows(U,ell,delta,left,right,self.x,self.f,self.modes)
                    estimate=np.min(np.array([[[float(v) for v in row] for row in tab] for _,tab in fields]),axis=(0,2))
                    fresh=self.train(estimate,total,actual,k,rotate_grid=bins)
                    self.rotate_plans[k]=(fresh,family,ell)
            if self.sharing:
                joint=compiled_charge(U,ell,delta,left,right,self.x,bs,poly)
                best=best.max(total-other-joint)
            if self.reopt and k not in self.jointplans:
                matrix=proposal_matrix(U,ell,delta,left,right,self.x,poly)
                estimate=np.min(np.array([[[float(v) for v in row] for row in tab] for _,tab in fields]),axis=(0,2))
                fresh=self.train(estimate,total,actual,k,matrix)
                self.jointplans[k]=(fresh,family,poly,ell)
        for j in (k,k-1):
            if j in self.rotate_plans:
                plan,family,line=self.rotate_plans[j]
                if plan is not None and family in families:
                    bs,M,separate=plan
                    _,means,jumps=self.jump_data[id(bs)]
                    for idx in families[family]:
                        delta,left,right,edge,*opts=sources[idx]
                        ell=opts[0] if opts else arb(1)/2
                        if ell.repr()!=line.repr():continue
                        cost=plan_price(U,ell,delta,left,right,self.x,self.f,self.modes,means,jumps)
                        extra=sum((a*b for a,b in zip(separate,actual)),arb(0))
                        best=best.max(total-cost-9*M*edge/8-extra)
            if j not in self.jointplans:continue
            plan,family,poly,line=self.jointplans[j]
            if not plan or family not in families:continue
            bs,M,separate=plan
            for idx in families[family]:
                delta,left,right,edge,*opts=sources[idx]
                ell=opts[0] if opts else arb(1)/2
                if ell!=line:continue
                joint=compiled_charge(U,ell,delta,left,right,self.x,bs,poly)
                extra=sum((a*b for a,b in zip(separate,actual)),arb(0))
                best=best.max(total-joint-M*edge-extra)
        return best


class HingeBands:
    """Partition each physical coefficient exactly; every test remains nonnegative."""
    def __init__(self,nodes,weight,frequency,step,positive,extend,tight,source_floor,more,scalar_mix,reuse_fit,cuts):
        ends=[arb(v) for v in cuts.split(',')]
        assert len(ends)<32
        assert all(arb(source_floor)<end<arb(7)/8 for end in ends)
        assert all(a<b for a,b in zip(ends,ends[1:]))
        parts=[[] for _ in range(len(ends)+1)]
        for a,w in zip(nodes,weight):
            band=sum(a>=b for b in ends)
            for j,part in enumerate(parts):
                part.append(w*(32-len(ends) if j==band else 1)/32)
        self.groups=[FreeGreen(nodes,part,frequency,step,positive,extend,tight,source_floor,more,scalar_mix,reuse_fit) for part in parts]
        for j,group in enumerate(self.groups):group.layout+=(cuts,j)

    def saving(self,*args):
        return sum((s.saving(*args) for s in self.groups),arb(0))
