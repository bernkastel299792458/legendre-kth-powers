"""Joint heights and abscissae with several independent signed Green harmonics."""
import numpy as np
from scipy.optimize import linprog
from flint import arb
from raw_cone import RawCone


class TrigCone:
    def __init__(self,nodes,w,frequency,step,positive,many=False):
        self.modes=(1,2,3,4) if positive else (2,4)
        self.many=many
        if many:
            from multi_raw import MultiRaw
            self.basis={m:MultiRaw(nodes,w,m*frequency,step,True) for m in self.modes}
        else:self.basis={m:RawCone(nodes,w,m*frequency,step,keep_parts=True,gaps=(1,2,3,5,8,12,18),strengths=('.97',)) for m in self.modes}
        b=self.basis[self.modes[0]];self.n=b.n;self.cut=b.cut;self.w=b.w;self.target=b.target
        self.records=[(0,j,0) for j in range(self.n)]
        arrays={}
        for m in self.modes:
            src=self.basis[m]
            B=np.array([[float(v/t) for v,t in zip(z,b.target,strict=True)] for z,_ in src.parts]).T
            V=np.array([[float(v/t) for v,t in zip(z,b.target,strict=True)] for _,z in src.parts]).T
            arrays[m]=B,V,float(src.fac)
            self.records.extend((m,j,sign) for sign in (1,-1) for j in range(len(src.parts)))
        self.fitC=[];self.fitR=[]
        for i in range(13):
            t=i*np.pi/24
            rows=[b.A[:,:b.n]]
            for m,(B,V,f) in arrays.items():
                cos=np.cos(m*t)
                for sign in (1,-1):
                    s=sign*cos;rows.append(B+min(s,f*s)*V)
            self.fitC.append(np.hstack(rows));self.fitR.extend([np.cos(t)]*self.n)
        self.fitC=-np.vstack(self.fitC);self.fitR=-np.array(self.fitR);self.proposals={}
        self.ng=96
        self.cos={m:[(arb.pi()*i*m/(2*self.ng)).cos() for i in range(self.ng+1)] for m in set(self.modes)|{1}}
        assert all(self.ng%m==0 for m in self.modes)

    def propose(self,fields,scalar):
        base=self.basis[self.modes[0]]
        original=sum(scalar,arb(0));price=[float(v/original) for v in scalar]
        for src in self.basis.values():
            if self.many:
                val=list(src.estimated(fields)/float(original));price+=val+val
                continue
            raw=None
            for edge,tab in fields:
                T=np.array([[float(v) for v in row] for row in tab]);z=np.min(T[src.a]+src.C[:,None]*T[src.b]+src.M[:,None]*float(edge),axis=1)
                raw=z if raw is None else np.minimum(raw,z)
            val=list(raw*src.wf[src.a]/float(original));price+=val+val
        fit=linprog(price,A_ub=self.fitC,b_ub=self.fitR,bounds=(0,None),method='highs')
        if not fit.success:return None
        used=[];B=[arb(0) for _ in scalar]
        pos={m:B.copy() for m in self.modes};neg={m:B.copy() for m in self.modes}
        for k,val in enumerate(fit.x):
            if val<=0:continue
            q=arb(float(val));m,j,sign=self.records[k];used.append((m,j,q))
            if m==0:
                for i,v in enumerate(base.cols[j]):B[i]+=q*v
            else:
                bb,vv=self.basis[m].parts[j];amp=(pos if sign>0 else neg)[m]
                for i in range(len(B)):B[i]+=q*bb[i];amp[i]+=q*vv[i]
        repair=arb(0);rem=(arb.pi()/(2*self.ng))**2/8
        for j,rhs in enumerate(self.target):
            loss=arb(0)
            for i,tar in enumerate(self.cos[1]):
                val=B[j]
                for m in self.modes:
                    t=self.cos[m][i];f=self.basis[m].fac
                    val+=pos[m][j]*t.min(f*t)+neg[m][j]*(-t).min(-f*t)
                loss=loss.max(tar-val/rhs)
            curvature=1+sum((m*m*(pos[m][j]+neg[m][j])/rhs for m in self.modes),arb(0))
            repair=repair.max(loss+rem*curvature)
        return used,repair

    def saving(self,U,scalar,sources,families,caps):
        budget=[a*b for a,b in zip(self.w,scalar[self.cut:],strict=True)];total=sum(budget,arb(0))
        fields=[(sources[ids[0]][3],[caps(self.cut+j,fam,1) for j in range(self.n+1)]) for fam,ids in families.items()]
        bucket=int((2*U).mid().floor().unique_fmpz())
        if bucket not in self.proposals:self.proposals[bucket]=self.propose(fields,budget)
        best=arb(0)
        for h in (bucket,bucket-1):
            plan=self.proposals.get(h)
            if plan is None:continue
            used,repair=plan;cost=repair*total
            for m,j,q in used:
                if m==0:charged=budget[j]
                elif self.many:charged=self.basis[m].charge(j,fields)
                else:
                    a,b,C,M=self.basis[m].key[j];charged=None
                    for edge,tab in fields:
                        for p,r in zip(tab[a],tab[b],strict=True):
                            v=self.w[a]*(p+C*r+M*edge)
                            charged=v if charged is None else charged.min(v)
                cost+=q*charged
            best=best.max(total-cost)
        return best
