"""Joint pricing of nonnegative Green tests with two, three, four, six or nine sources."""
import numpy as np
from scipy.optimize import linprog
from flint import arb


class MultiRaw:
    def __init__(self,nodes,weight,frequency,step,keep_parts=False):
        self.cut=next(i for i,s in enumerate(nodes) if s>=arb('.795'));self.w=weight[self.cut:]
        self.n=n=len(self.w);self.plans={}
        ticks=[1300+(i+self.cut)*step for i in range(n)]+[1750]
        self.ordinary=[[w*arb(max(0,t-a))/2000 for t in ticks[1:]] for w,a in zip(self.w,ticks[:-1],strict=True)]
        self.target=[sum(col,arb(0)) for col in zip(*self.ordinary,strict=True)]
        cols=self.ordinary.copy();self.groups=[];self.keys=[]
        z=frequency*step/2000;alpha=z/z.sinh();self.fac=alpha;self.parts=[]
        for stride in ((1,2,4,6) if keep_parts else (1,2,3,4,6,8)):
          ticks_step=stride*step;h=arb(ticks_step)/2000
          sh=(frequency*h).sinh();ch=(frequency*h).cosh()
          for periods in (1,2,3,5,8):
            starts=np.array([i for i in range(n) if ticks[i]+periods*ticks_step<=1750 and ticks[i+periods*stride]==ticks[i]+periods*ticks_step],dtype=int)
            if not len(starts):continue
            for slope in (('0',) if periods==1 else (('0','1') if keep_parts else ('0','.65','1','1.3'))):
              for terminal in (('1',) if periods==1 or keep_parts else ('.65','1')):
                x=arb(141)*h*arb(slope)
                v=[h*i if x.is_zero() else h*(x*i).expm1()/x.expm1() for i in range(periods+1)]
                v[-1]*=arb(terminal)
                # The two one-sided derivatives of the imposed hyperbolic spline.
                right=[frequency*(b-a*ch)/sh for a,b in zip(v,v[1:])]+[-frequency*v[-1]]
                left=[arb(0)]+[frequency*(b*ch-a)/sh for a,b in zip(v,v[1:])]
                y=arb(0);dy=arb(0);nodes_b=[];der=arb(0)
                for amp in v:der=der.max(frequency*amp)
                for j,(l,r) in enumerate(zip(left,right,strict=True)):
                    der=der.max(abs(l)).max(abs(r));need=abs(r-l)
                    if j<periods:need=need.max((v[j+1]-y)/h-dy)
                    b=need.upper();nodes_b.append(b);dy+=b;y+=h*dy
                M=(sum(nodes_b,arb(0))+der).upper()
                def profile(t):
                    if t<=0:return arb(0),arb(0)
                    u=arb(t)/2000;idx=t//ticks_step
                    if t>=periods*ticks_step:V=v[-1]*(-frequency*(u-periods*h)).exp()
                    elif t%ticks_step==0:V=v[idx]
                    else:
                        tau=arb(t%ticks_step)/2000
                        V=(v[idx]*(frequency*(h-tau)).sinh()+v[idx+1]*(frequency*tau).sinh())/sh
                    B=sum((b*(u-j*h).max(0) for j,b in enumerate(nodes_b)),arb(0))
                    return B,V
                values={d:profile(d) for d in {t-ticks[a] for a in starts for t in ticks[1:]}}
                gid=len(self.groups)
                self.groups.append((starts,stride,nodes_b,M))
                for a in starts:
                    coords=[values[t-ticks[a]] for t in ticks[1:]]
                    cols.append([self.w[a]*(p+alpha*q) for p,q in coords])
                    if keep_parts:self.parts.append(([self.w[a]*p for p,_ in coords],[self.w[a]*q for _,q in coords]))
                    self.keys.append((gid,int(a)))
        self.cols=cols
        self.A=np.array([[float(v/t) for v,t in zip(col,self.target,strict=True)] for col in cols]).T
        self.wf=np.array([float(x) for x in self.w])

    def estimated(self,fields):
        prices=[]
        data=[(float(edge),np.array([[float(z) for z in row] for row in cols])) for edge,cols in fields]
        for starts,stride,nodes_b,M in self.groups:
            best=None
            for edge,tab in data:
                cost=sum((float(b)*tab[starts+j*stride] for j,b in enumerate(nodes_b)),float(M)*edge)
                v=cost.min(axis=1);best=v if best is None else np.minimum(best,v)
            prices.extend(best*self.wf[starts])
        return np.array(prices)

    def charge(self,j,fields):
        gid,a=self.keys[j];_,stride,bs,M=self.groups[gid];charged=None
        for edge,tab in fields:
            vals=None
            for i,b in enumerate(bs):
                x=tab[a+i*stride]
                vals=[M*edge+b*z for z in x] if vals is None else [v+b*z for v,z in zip(vals,x,strict=True)]
            for v in vals:charged=v if charged is None else charged.min(v)
        return charged*self.w[a]

    def train(self,scalar,fields):
        ordinary=sum(scalar,arb(0));prices=[float(x) for x in scalar]+list(self.estimated(fields))
        fit=linprog(np.array(prices)/float(ordinary),A_ub=-self.A,b_ub=-np.ones(self.n),bounds=(0,None),method='highs')
        if not fit.success:return None
        used=[(k,arb(float(x))) for k,x in enumerate(fit.x) if x>0]
        cover=[arb(0) for _ in scalar]
        for k,q in used:
            for i,v in enumerate(self.cols[k]):cover[i]+=q*v
        if any(not t>0 for t in cover):return None
        factor=arb(1)
        for a,b in zip(self.target,cover,strict=True):factor=factor.max(a/b)
        return used,factor

    def saving(self,U,scalar,sources,families,caps):
        baseline=[w*v for w,v in zip(self.w,scalar[self.cut:],strict=True)];total=sum(baseline,arb(0))
        fields=[(sources[ids[0]][3],[caps(self.cut+j,f,1) for j in range(self.n+1)]) for f,ids in families.items()]
        bucket=int((U*4).mid().floor().unique_fmpz())
        if bucket not in self.plans:self.plans[bucket]=self.train(baseline,fields)
        answer=arb(0)
        for k in (bucket,bucket-1):
            plan=self.plans.get(k)
            if plan is None:continue
            used,repair=plan;cost=arb(0)
            for j,q in used:
                if j<self.n:charged=baseline[j]
                else:charged=self.charge(j-self.n,fields)
                cost+=q*charged
            answer=answer.max(total-repair*cost)
        return answer
