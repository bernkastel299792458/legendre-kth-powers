"""Combine unscaled positive two-source Green weights from different detectors."""
import numpy as np
from flint import arb
from scipy.optimize import linprog
from weighted_green import amplitude


class RawCone:
    def __init__(self,nodes,weight,frequency,step,absolute=False,keep_parts=False,gaps=(1,2,3,4,6,8,12,18,26,40),strengths=('.52','.97')):
        self.cut=next(i for i,s in enumerate(nodes) if s>=arb('.795'));self.plans={}
        self.x=nodes[self.cut:];self.w=weight[self.cut:]
        n=len(self.w);self.n=n
        # At every cell, V is at least this fraction of its linear interpolation.
        z=frequency*(arb(step)/2000);fac=z/z.sinh();self.fac=fac;self.absolute=absolute
        coef=[];self.cols=[];self.key=[];self.parts=[]
        for i in range(n):
            self.cols.append([self.w[i]*(x-self.x[i]).max(0) for x in self.x[1:]])
        for i in range(n):
            for g in gaps:
                j=i+g
                if j>n:continue
                a,b=self.x[i],self.x[j];gap=b-a
                lo=frequency.lower()*gap
                for strength in strengths:
                    C=arb(strength)*2*lo/(-(-2*lo).expm1())
                    eps=C*(-frequency*gap).exp();M=1+C+C*(1+(-2*lo).exp())/2
                    assert eps>0 and eps<1 and C*(-(-2*lo).expm1())/(2*lo)<1
                    out=[];Bs=[];Vs=[]
                    for x in self.x[1:]:
                        u=(x-a).max(0);v=(x-b).max(0)
                        B=u+C*v
                        V=amplitude(C,frequency,gap,u.min(gap),v)
                        out.append(self.w[i]*(B+fac*V))
                        if absolute or keep_parts:Bs.append(self.w[i]*B);Vs.append(self.w[i]*V)
                    self.cols.append(out);self.key.append((i,j,C,M));coef.append((i,j,float(C),float(M)))
                    if absolute or keep_parts:self.parts.append((Bs,Vs))
        target=[sum(z,arb(0)) for z in zip(*self.cols[:n],strict=True)]
        self.target=target
        self.A=np.array([[float(v/t) for v,t in zip(col,target,strict=True)] for col in self.cols]).T
        if absolute:
            B=np.array([[float(v/t) for v,t in zip(b,target,strict=True)] for b,_ in self.parts]).T
            V=np.array([[float(v/t) for v,t in zip(vs,target,strict=True)] for _,vs in self.parts]).T
            self.test=(.44,.58,.68,.73,.80,.88,.94,1.)
            self.Ang=np.vstack([np.hstack((self.A[:,:n], B+(2*u*u-1)*(float(fac) if u*u>.5 else 1)*V)) for u in self.test])
        f=np.array(coef);self.a,self.b=f[:,0].astype(int),f[:,1].astype(int)
        self.C,self.M=f[:,2],f[:,3];self.wf=np.array([float(v) for v in self.w])

    def reprice(self,plan,actual,sources,families,caps):
        terms,factor=plan;cost=arb(0)
        for k,q in terms:
            if k<self.n:charged=actual[k]
            else:
                i,j,C,M=self.key[k-self.n];charged=None
                for family,ids in families.items():
                    edge=M*sources[ids[0]][3]
                    a=caps(self.cut+i,family,1);b=caps(self.cut+j,family,1)
                    for v,z in zip(a,b,strict=True):
                        t=self.w[i]*(v+C*z+edge)
                        charged=t if charged is None else charged.min(t)
            cost+=q*charged
        return (sum(actual,arb(0))-factor*cost).max(arb(0))

    def saving(self,scalar,sources,families,caps,packed=None,bucket=None):
        actual=[w*v for w,v in zip(self.w,scalar[self.cut:],strict=True)]
        if packed:bucket=None
        if bucket is not None and bucket in self.plans:
            out=self.reprice(self.plans[bucket],actual,sources,families,caps)
            if bucket-1 in self.plans:out=out.max(self.reprice(self.plans[bucket-1],actual,sources,families,caps))
            return out
        original=sum(actual,arb(0));raw=None
        fields=[]
        for fam,js in families.items():
            edge=sources[js[0]][3]
            tab=[caps(self.cut+i,fam,1) for i in range(self.n+1)]
            fields.append((edge,tab));T=np.array([[float(x) for x in row] for row in tab])
            z=np.min(T[self.a]+self.C[:,None]*T[self.b]+self.M[:,None]*float(edge),axis=1)
            raw=z if raw is None else np.minimum(raw,z)
        costs=[float(v) for v in actual]+list(raw*self.wf[self.a])
        extra=[];extra_cost=[];A=self.Ang if self.absolute else self.A
        objective=np.concatenate([np.full(self.n,u) for u in self.test]) if self.absolute else np.ones(self.n)
        if packed:
            P=np.zeros((self.n,len(packed)))
            for j,(use,gain) in enumerate(packed.items()):
                entries=[(i-self.cut,v) for i,v in use]
                cost=sum((v*actual[i] for i,v in entries),arb(0))/10**6-gain
                assert cost>0
                for i,v in entries:P[i,j]=(v-1)/10**6
                extra.append(entries);extra_cost.append(cost);costs.append(float(cost))
            if self.absolute:side=np.vstack([u*(self.A[:,:self.n]@P) for u in self.test])
            else:side=A[:,:self.n]@P
            A=np.hstack((A,side))
        price=np.array(costs)/float(original)
        fit=linprog(price,A_ub=-A,b_ub=-objective,bounds=(0,None),method='highs')
        if not fit.success:return arb(0)
        cost=arb(0);cover=[arb(0) for _ in self.w];amp=cover.copy();linear=cover.copy()
        for k,amount in enumerate(fit.x):
            if amount<=0:continue
            q=arb(float(amount))
            if k<self.n:charged=actual[k]
            elif k<len(self.cols):
                i,j,C,M=self.key[k-self.n];charged=None
                for edge,tab in fields:
                    for a,b in zip(tab[i],tab[j],strict=True):
                        val=self.w[i]*(a+C*b+M*edge)
                        charged=val if charged is None else charged.min(val)
            else:
                j=k-len(self.cols)
                cost+=q*extra_cost[j]
                for ix,v in extra[j]:
                    a=q*(v-1)/10**6
                    destination=linear if self.absolute else cover
                    for i,base in enumerate(self.cols[ix]):destination[i]+=a*base
                continue
            cost+=q*charged
            if self.absolute and k>=self.n:
                B,V=self.parts[k-self.n]
                for i in range(self.n):cover[i]+=q*B[i];amp[i]+=q*V[i]
            else:
                for i,v in enumerate(self.cols[k]):cover[i]+=q*v
        if self.absolute:
            split=1/arb(2).sqrt()
            for i,(b,v,g) in enumerate(zip(cover,amp,linear,strict=True)):
                caps=[]
                for a,end,vv in ((arb(0),split,v),(split,arb(1),self.fac*v)):
                    c=b-vv
                    if vv.is_zero():caps.append(c/end+g);continue
                    if not (c>0 and vv>0):return arb(0)
                    at=(c/(2*vv)).sqrt().max(a).min(end)
                    caps.append(c/at+2*vv*at+g)
                cover[i]=caps[0].min(caps[1])
        if any(not v>0 for v in cover):return arb(0)
        factor=arb(1)
        for v,t in zip(cover,self.target,strict=True):factor=factor.max(t/v)
        if bucket is not None:
            self.plans[bucket]=([(i,arb(float(z))) for i,z in enumerate(fit.x) if z>0],factor)
        return (original-factor*cost).max(arb(0))
