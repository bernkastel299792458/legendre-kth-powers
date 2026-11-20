"""Several source lines and several signed harmonics within each individual determinant."""
import numpy as np
from scipy.optimize import linprog
from flint import arb
from multi_raw import MultiRaw


class CoupledCone:
    def __init__(self,nodes,weight,frequency,step,positive):
        self.cut=next(i for i,s in enumerate(nodes) if s>=arb('.795'));self.w=weight[self.cut:]
        self.n=n=len(self.w);self.wf=np.array([float(v) for v in self.w]);self.plans={};self.precision_grid=96
        self.modes=(1,2,4) if positive else (2,4,6)
        recipes=(('1','0','0'),('1','.25','-.05'),('1','.425','-.085'),('1','.60','-.13')) if positive else (('1','0','0'),('1','-.20','.085'),('1','-.33','.12'))
        ticks=[1300+(i+self.cut)*step for i in range(n)]+[1750]
        ordinary=[[w*arb(max(0,t-a))/2000 for t in ticks[1:]] for w,a in zip(self.w,ticks[:-1],strict=True)]
        self.ordinary=ordinary;self.target=[sum(v,arb(0)) for v in zip(*ordinary,strict=True)]
        allm=set(self.modes)|{1}
        self.cos={m:[(arb.pi()*j*m/192).cos() for j in range(193)] for m in allm}
        assert all(96%m==0 for m in self.modes)
        self.fac={m:(m*frequency*step/2000)/(m*frequency*step/2000).sinh() for m in self.modes}
        self.groups=[];self.keys=[];self.parts=[]
        for stride in (1,2,3,5,8):
          tickstep=stride*step;h=arb(tickstep)/2000
          for periods in (2,4,7):
            starts=np.array([i for i in range(n) if ticks[i]+periods*tickstep<=1750 and ticks[i+periods*stride]==ticks[i]+periods*tickstep],dtype=int)
            if not len(starts):continue
            for slope in ('0','.9','1.3'):
              x=arb(141)*h*arb(slope)
              v=[h*i if x.is_zero() else h*(i*x).expm1()/x.expm1() for i in range(periods+1)]
              data={}
              for m in self.modes:
                nu=m*frequency;sh=(nu*h).sinh();ch=(nu*h).cosh()
                left=[arb(0)]+[nu*(b*ch-a)/sh for a,b in zip(v,v[1:])]
                right=[nu*(b-a*ch)/sh for a,b in zip(v,v[1:])]+[-nu*v[-1]]
                deriv=arb(0)
                for l,r,val in zip(left,right,v,strict=True):deriv=deriv.max(abs(l)).max(abs(r)).max(nu*val)
                jumps=[r-l for l,r in zip(left,right,strict=True)]
                def profile(d):
                    if d<=0:return arb(0)
                    y=arb(d)/2000;idx=d//tickstep
                    if d>=periods*tickstep:return v[-1]*(-nu*(y-periods*h)).exp()
                    if d%tickstep==0:return v[idx]
                    w=arb(d%tickstep)/2000
                    return (v[idx]*(nu*(h-w)).sinh()+v[idx+1]*(nu*w).sinh())/sh
                amplitudes={d:profile(d) for d in {t-ticks[a] for a in starts for t in ticks[1:]}}
                data[m]=(jumps,deriv,nu*h/sh,amplitudes)
              for words in recipes:
                cs={m:arb(w) for m,w in zip(self.modes,words,strict=True) if arb(w)!=0}
                # All cos(m*t) sign changes are vertices of the 192-cell grid.
                ang=arb(0);arc=arb.pi()**2/(8*192**2)
                for j in range(193):
                    s=arb(0)
                    for m,c in cs.items():
                        y=c*self.cos[m][j];s+=y.min(data[m][2]*y)
                    ang=ang.max(-s)
                ang+=arc*sum(m*m*abs(c) for m,c in cs.items())
                bs=[];B=arb(0);grad=arb(0)
                for i in range(periods+1):
                    ds={m:c*data[m][0][i] for m,c in cs.items()}
                    cap=arb(0)
                    for j in range(193):cap=cap.max(-sum((d*self.cos[m][j] for m,d in ds.items()),arb(0)))
                    cap+=arc*sum(m*m*abs(d) for m,d in ds.items())
                    if i<periods:cap=cap.max((ang*v[i+1]-B)/h-grad)
                    b=cap.upper();bs.append(b);grad+=b;B+=grad*h
                M=(sum(bs,arb(0))+sum(abs(c)*data[m][1] for m,c in cs.items())).upper()
                gid=len(self.groups)
                # Positivity gives |d_m|<=2 b; at most three modes, all q<10^-6.
                self.groups.append((starts,stride,[b*(1+arb('6e-6')) for b in bs],M))
                offsets={t-ticks[a] for a in starts for t in ticks[1:]}
                Bvals={d:sum((b*arb(max(0,d-i*tickstep))/2000 for i,b in enumerate(bs)),arb(0)) for d in offsets}
                for a in starts:
                    amp={m:[self.w[a]*c*data[m][3][t-ticks[a]] for t in ticks[1:]] for m,c in cs.items()}
                    self.parts.append(([self.w[a]*Bvals[t-ticks[a]] for t in ticks[1:]],amp));self.keys.append((gid,int(a)))
        rows=[];targets=[]
        C0=np.array([[float(v/t) for v,t in zip(z,self.target,strict=True)] for z in self.ordinary]).T
        B=np.array([[float(v/t) for v,t in zip(z,self.target,strict=True)] for z,_ in self.parts]).T
        V={m:np.array([[float(v/t) for v,t in zip(cs.get(m,[0]*n),self.target,strict=True)] for _,cs in self.parts]).T for m in self.modes}
        for k in range(13):
            t=k*np.pi/24;mat=B.copy()
            for m in self.modes:
                y=V[m]*np.cos(m*t);mat+=np.minimum(y,float(self.fac[m])*y)
            rows.append(np.hstack((C0,mat)));targets.extend([np.cos(t)]*n)
        self.A=-np.vstack(rows);self.rhs=-np.array(targets)

    def train(self,actual,fields):
        total=sum(actual,arb(0));prices=np.concatenate(([float(v) for v in actual],MultiRaw.estimated(self,fields)))/float(total)
        fit=linprog(prices,A_ub=self.A,b_ub=self.rhs,bounds=(0,None),method='highs')
        if not fit.success:return None
        used=[];B=[arb(0) for _ in self.w];pos={m:B.copy() for m in self.modes};neg={m:B.copy() for m in self.modes}
        for k,z in enumerate(fit.x):
            if z<=0:continue
            q=arb(float(z));used.append((k,q))
            if k<self.n:base=self.ordinary[k];parts={}
            else:base,parts=self.parts[k-self.n]
            for i,v in enumerate(base):B[i]+=q*v
            for m,vals in parts.items():
                for i,v in enumerate(vals):pos[m][i]+=q*v.max(0);neg[m][i]+=q*(-v).max(0)
        repair=arb(0);arc=arb.pi()**2/(8*192**2)
        for i,r in enumerate(self.target):
            loss=arb(0)
            for j in range(97):
                v=B[i]
                for m in self.modes:
                    c=self.cos[m][j];f=self.fac[m];v+=pos[m][i]*c.min(f*c)+neg[m][i]*(-c).min(-f*c)
                loss=loss.max(self.cos[1][j]-v/r)
            repair=repair.max(loss+arc*(1+sum(m*m*(pos[m][i]+neg[m][i])/r for m in self.modes)))
        return used,repair

    def saving(self,U,scalar,sources,families,caps):
        actual=[w*v for w,v in zip(self.w,scalar[self.cut:],strict=True)];total=sum(actual,arb(0))
        fields=[(sources[ids[0]][3],[caps(self.cut+j,f,1) for j in range(self.n+1)]) for f,ids in families.items()]
        bucket=int((2*U).mid().floor().unique_fmpz());best=arb(0)
        if bucket not in self.plans:self.plans[bucket]=self.train(actual,fields)
        for i in (bucket,bucket-1):
            plan=self.plans.get(i)
            if not plan:continue
            used,repair=plan;cost=repair*total
            for k,q in used:cost+=q*(actual[k] if k<self.n else MultiRaw.charge(self,k-self.n,fields))
            best=best.max(total-cost)
        return best
