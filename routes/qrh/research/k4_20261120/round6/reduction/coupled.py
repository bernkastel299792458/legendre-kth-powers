"""Certify the joint real-part and height dual using nonnegative Arb coefficients."""
import argparse
from functools import lru_cache
import sys
import numpy as np
from flint import arb,arb_mat,ctx
from scipy import sparse
from scipy.optimize import linprog
from irregular import call_rows,parse_grid
from tables import A,H,LOW,get_data,validate_slabs,conditions
from grid_target import cap_table,dot,weights

SIX=[(6,851),(7,865),(9,826),(12,842),(19,863),(31,856)]

def check_necessary():
    with ctx.workprec(200):
        u=arb(H).log()
        counts=[1089900,420071,10495930,3630069,1158145,5070970]
        for (k,m),limit in zip(SIX,counts,strict=True):
            y=conditions(u+arb(k)/4,arb(m)/1000)
            assert limit-1<y<limit
        t=arb(H)*(arb(31)/4).exp()
        assert 6965124291625026<t<6965124291625027
        print("least failing count",min(counts),"strict common ordinate ceiling",6965124291625027,flush=True)

@lru_cache(maxsize=2)
def height_data(nheight,strong,moving,sharp,precision):
    assert precision==ctx.prec
    hs,counts,real,calls,far,final=get_data(nheight,phased=True,fine=True,moving=moving)
    if strong or sharp:
        from strong_rows import improve
        calls=[improve(u,real,row,sharp=sharp) for u,row in zip(hs[1:],calls,strict=True)]
    return hs,counts,real,calls,far,final

class Coupled:
    def __init__(self,marks,first,nheight,span,spacing,conditions_fn=conditions,strong=False,moving=False,
                 sharp=False,increments=False):
        self.hs,self.counts,allreal,calls,self.far,self.final=height_data(nheight,strong,moving,sharp,ctx.prec)
        self.length=3+nheight*span
        self.allreal=allreal
        self.height=[u.exp() for u in self.hs]
        self.cap=cap_table((4*(-first/4).exp()).log1p())
        self.old=arb_mat(call_rows(marks,self.hs,calls,allreal,nheight,conditions_fn=conditions_fn)).transpose()
        self.nodes=sorted(set(range(650,876,spacing))|{875}|{m for _,m in marks})
        self.real=[arb(j)/1000 for j in self.nodes]
        self.size=len(self.nodes)
        self.rhs=[[n]+[r[j-650] for j in self.nodes[:-1]]
                  for n,r in zip(self.counts[:self.length],calls[:self.length],strict=True)]
        self.boxes=[(min(self.length,3+k*(nheight//4))-1,m,
                     arb(conditions_fn(self.hs[0]+arb(k)/4,arb(m)/1000))) for k,m in marks]
        assert all(c>0 for _,_,c in self.boxes)
        self.windows=[]
        if increments:
            from local_calls import hinges as local_hinges
            nodes=[i for i,b in enumerate(self.nodes[:-1]) if b>=770 and i%2==0]
            for start_index in sorted({0}|{k*nheight//4 for k,_ in marks}):
                for steps in (1,2,4):
                    last=start_index+steps
                    if last>span*nheight:continue
                    bound=local_hinges(start_index,last,nheight,[self.real[j] for j in nodes],shrink=True)
                    self.windows.append((start_index+2 if start_index else -1,last+2,nodes,bound))
        self.atomcap=[]
        for i,row in enumerate(self.rhs):
            caps=[]
            for j,(b,v) in enumerate(zip(self.nodes,self.real)):
                z=row[0]
                for t in range(j):
                    z=z.min(row[t+1]/(v-self.real[t]))
                for height,m,count in self.boxes:
                    if i<=height and m<b:z=z.min(count)
                caps.append(z)
            self.atomcap.append(caps)
        real=np.array(self.nodes)/1000
        self.scales=np.minimum(np.exp((1-real)*122),1.e11)
        positive=np.maximum(real[None,:]-real[:,None],0)
        local=sparse.csr_matrix(np.vstack([self.scales,positive[:-1]*self.scales[None,:]]))
        bank=sparse.kron(sparse.eye(self.length,format="csr"),local,format="csr")
        rhs=np.asarray(self.rhs,dtype=float).ravel()
        assert np.min(rhs)>1
        bank=sparse.diags(1/rhs)@bank
        eye=sparse.eye(self.length,format="csr")
        transition=sparse.kron(eye[:-1]-eye[1:],sparse.eye(self.size,format="csr"))
        extra=[sparse.csr_matrix(np.outer(np.arange(self.length)==i,
                   self.scales*(real>m/1000)/float(c)).reshape(1,-1)) for i,m,c in self.boxes]
        window_rows=[]
        for a,b,nodes,bounds in self.windows:
            direction=np.zeros(self.length)
            direction[b]=1
            if a>=0:direction[a]=-1
            kernel=positive[nodes]*self.scales[None,:]/np.asarray(bounds,dtype=float)[:,None]
            window_rows.append(sparse.kron(sparse.csr_matrix(direction[None,:]),sparse.csr_matrix(kernel)))
        self.matrix=sparse.vstack([bank,transition]+extra+window_rows,format="csr")
        self.target=np.r_[np.ones(len(rhs)),np.zeros(transition.shape[0]),np.ones(len(extra)+
                           sum(len(nodes) for _,_,nodes,_ in self.windows))]
        self.box_offset=len(rhs)+transition.shape[0]

    def dual(self,depth,pay,E):
        l,n=self.length,self.size
        charge=np.asarray(depth[:l],dtype=float)[:,None]*(np.asarray(pay,dtype=float)*self.scales)[None,:]
        res=linprog(-charge.ravel(),A_ub=self.matrix,b_ub=self.target,bounds=(0,None),
                    method="highs-ipm",options={"dual_feasibility_tolerance":1.e-9})
        if not res.success:raise ArithmeticError(res.message)
        # Every selected dual multiplier below is a nonnegative binary rational.
        raw=np.maximum(-res.ineqlin.marginals,0.)
        if not np.isfinite(raw).all():raise ArithmeticError("nonfinite dual candidate")
        mu=raw[:l*n].reshape(l,n)
        factors={}
        total=arb(0)
        cursor=self.box_offset+len(self.boxes)
        for (i,m,c),v in zip(self.boxes,raw[self.box_offset:cursor],strict=True):
            a=arb(float(v))
            total+=a
            factors.setdefault(i,[]).append((m,a/c))
        changes={}
        for start,end,nodes,bounds in self.windows:
            for j,c,y in zip(nodes,bounds,raw[cursor:cursor+len(nodes)],strict=True):
                if y<=0:continue
                a=arb(float(y))
                total+=a
                changes.setdefault(end,[]).append((j+1,a/c))
                if start>=0:changes.setdefault(start,[]).append((j+1,-a/c))
            cursor+=len(nodes)
        cover=[arb(0)]*n
        error=arb(0)
        for i in range(l-1,-1,-1):
            u=[arb(float(v)) for v in mu[i]]
            total+=sum(u,arb(0))
            mult=[a/r for a,r in zip(u,self.rhs[i],strict=True)]
            for j,z in changes.get(i,()):mult[j]+=z
            level=mult[0]
            slope=arb(0)
            gap=(E[i]-E[l]).max(arb(0))
            for j,b in enumerate(self.nodes):
                if j:
                    slope+=mult[j]
                    level+=slope*(self.real[j]-self.real[j-1])
                cover[j]+=level
                for m,y in factors.get(i,()):
                    if b>m:cover[j]+=y
                missing=(gap*pay[j]-cover[j]).max(arb(0))
                if not missing.is_zero():error+=missing*self.atomcap[i][j]
        return total+error,error

    def evaluate(self,a,b):
        d=(4*(-b/4).exp()).log1p()
        E=[self.cap(d*t) for t in self.height]
        diff=[(z-y).max(arb(0)) for z,y in zip(E,E[1:])]
        w=weights([self.allreal],a)
        hinges=arb_mat([w[1:]])*self.old
        terms=[v*(hinges[0,i]+w[0]*self.counts[i]) for i,v in enumerate(diff)]
        remote=E[-1]*dot(weights(self.far,a),self.final)
        eps=4*(-a/4).exp()
        fixed=2*(remote+(-a/2).exp()*arb(H)*arb(H).log())
        fixed+=(1+eps)**A("1.5")*(b+eps.log1p())**2*(-a/4).exp()/(6*arb(2).log())
        fixed+=(-3*a).exp()/(1-(-2*a).exp())
        old=2*sum(terms,arb(0))+fixed
        if old<arb(".998"):return old,arb(0),False
        pay=[((s-1)*a).exp() for s in self.real]
        joint,error=self.dual(diff,pay,E)
        return old.min(2*(joint+sum(terms[self.length:],arb(0)))+fixed),error,True

def check_band(args):
    assert args.stride==1 or args.diagnose
    assert not (args.no_boxes and args.grid)
    marks=[] if args.no_boxes else parse_grid(args.grid) if args.grid else SIX
    a0,a1,dx=map(A,(args.first,args.last,args.cell))
    assert 115<=a0<a1<=163 and dx>0 and args.nh>0 and args.nh%4==0 and 1<=args.span<=24 and 1<=args.ds<=15
    assert (4*(-a1/4).exp()).log1p()*arb(55).exp()>192
    model=Coupled(marks,a0,args.nh,args.span,args.ds,strong=args.strong,moving=args.moving,
                  sharp=args.sharp,increments=args.increments)
    n=int(((a1-a0)/dx).upper().ceil().unique_fmpz())
    high=maxerror=arb(0);worst=-1;solves=0
    for i in range(0,n,args.stride):
        a=a0+i*dx
        v,e,use=model.evaluate(a,(a+dx).min(a1))
        solves+=use
        maxerror=maxerror.max(e)
        if v>high:worst=i
        high=high.max(v)
        if args.diagnose or i%32==0 or not v<1:
            print(i,a.str(10),v.str(11),e.str(6),flush=True)
    print("rectangle count",len(marks),"interval",args.first,args.last,"cost",high.str(17),
          "worst lower endpoint",(a0+worst*dx).str(14),"dual correction",maxerror.str(8),
          "linear programs",solves,flush=True)
    if not args.diagnose:
        assert high<1
        if marks==SIX:check_necessary()
    return high

if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--first",default=LOW);cli.add_argument("--last",default="147.2")
    cli.add_argument("--nh",type=int,default=12);cli.add_argument("--span",type=int,default=4)
    cli.add_argument("--ds",type=int,default=3);cli.add_argument("--cell",default="1/16")
    cli.add_argument("--stride",type=int,default=1);cli.add_argument("--grid")
    cli.add_argument("--no-boxes",action="store_true")
    cli.add_argument("--diagnose",action="store_true")
    cli.add_argument("--strong",action="store_true");cli.add_argument("--moving",action="store_true")
    cli.add_argument("--sharp",action="store_true")
    cli.add_argument("--increments",action="store_true")
    args=cli.parse_args();ctx.prec=160
    validate_slabs(phased=True)
    if len(sys.argv)==1:
        args.strong,args.moving,args.nh,args.span,args.cell=True,True,16,8,"1/24"
        for args.first,args.last in ((LOW,"124"),("124","147.2")):
            assert check_band(args)<arb(".997914")
    else:
        check_band(args)
