"""Certified fractional allocation of scalar chord coefficients to signed Green tests."""
from flint import arb

SCALE=10**6


def patterns(shape,groups,weights):
    pairs={}
    for ia,(ib,C,*_) in shape.items():
        u=int((SCALE*C*weights[ia]/weights[ib]).upper().ceil().unique_fmpz())
        assert 0<u<=SCALE+1
        pairs[ia]=((ia,SCALE),(ib,u))
    together={tuple(kk):tuple(sorted(v for i in kk for v in pairs[i])) for kk,_,_ in groups}
    return pairs,together


def saving(candidates,mode):
    if not candidates:return arb(0)
    import numpy as np
    keys=list(candidates);val=[candidates[k] for k in keys]
    score=np.array([float(z.lower()) for z in val]);active=np.flatnonzero(score>0)
    if not len(active):return arb(0)
    peak=max(score);nodes=sorted({i for key in keys for i,c in key});ix={s:i for i,s in enumerate(nodes)}
    def check(order,alloc):
        rem=[SCALE]*len(nodes);result=arb(0)
        for j in order:
            n=min(alloc(j),*(rem[ix[i]]*SCALE//v for i,v in keys[j]))
            if n<=0:continue
            for i,v in keys[j]:rem[ix[i]]-=(n*v+SCALE-1)//SCALE
            result+=n*val[j]
        assert min(rem)>=0
        return result/SCALE
    out=arb(0)
    for pow0 in (0,1):
        order=sorted(active,key=lambda i:score[i]/len(keys[i])**pow0,reverse=True)
        out=out.max(check(order,lambda i:SCALE))
    if mode=='linear':
        from scipy.optimize import linprog
        from scipy.sparse import csc_matrix
        rows=[];cols=[];data=[]
        for col,j in enumerate(active):
            for n,v in keys[j]:rows.append(ix[n]);cols.append(col);data.append(v/SCALE)
        A=csc_matrix((data,(rows,cols)),shape=(len(nodes),len(active)))
        fit=linprog(-score[active]/peak,A_ub=A,b_ub=np.ones(len(nodes)),bounds=(0,1),method='highs')
        if fit.success:
            allocation={j:int(SCALE*max(0,min(1,t))) for j,t in zip(active,fit.x,strict=True) if t>0}
            out=out.max(check(sorted(allocation,key=lambda i:score[i],reverse=True),allocation.__getitem__))
    return out


def cone(candidates,weight,nodes,scalar):
    """Majorize the full piecewise-linear hinge profile; verify every knot in Arb."""
    if not candidates:return arb(0)
    import numpy as np
    from scipy.optimize import linprog
    cut=min(i for key in candidates for i,_ in key)
    n=len(weight)-cut
    x=nodes[cut:];w=weight[cut:];r=scalar[cut:]
    p=[v*t for v,t in zip(w,r,strict=True)]
    original=sum(p,arb(0))
    keys=list(candidates)
    rows=[[(i-cut,v) for i,v in key] for key in keys]
    cols=np.zeros((n,n+len(keys)))
    cols[:,:n]=np.eye(n)
    prices=p.copy()
    for j,(key,usage) in enumerate(zip(keys,rows,strict=True)):
        # The stored key is an upper ceiling. One less unit always underestimates coverage.
        for i,v in usage:cols[i,j+n]=(v-1)/SCALE
        cost=sum((v*p[i] for i,v in usage),arb(0))/SCALE-candidates[key]
        assert cost>0
        prices.append(cost)
    xf=np.array([float(v) for v in x]);wf=np.array([float(v) for v in w]);pf=np.array([float(v/original) for v in prices])
    H=np.maximum(0,xf[1:,None]-xf[None,:-1])*wf[None,:];H/=np.sum(H,axis=1)[:,None]
    # Fixed-precision dot products here only propose nonnegative coefficients.
    proposal=linprog(pf,A_ub=-(H@cols),b_ub=-np.ones(n),bounds=(0,None),method='highs')
    if not proposal.success:return arb(0)
    assigned=[arb(0) for _ in w];cost=arb(0)
    for j,z in enumerate(proposal.x):
        if z<=0:continue
        a=arb(float(z));cost+=a*prices[j]
        if j<n:assigned[j]+=a
        else:
            for i,v in rows[j-n]:assigned[i]+=a*(v-1)/SCALE
    upper=arb(0);target=arb(0);m1=arb(0);m0=arb(0);factor=arb(1)
    for j in range(n):
        m1+=assigned[j]*w[j];m0+=w[j]
        h=x[j+1]-x[j];upper+=h*m1;target+=h*m0
        if not upper>0:return arb(0)
        factor=factor.max(target/upper)
    return (original-factor*cost).max(arb(0))
