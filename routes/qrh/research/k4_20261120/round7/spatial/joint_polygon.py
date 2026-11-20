"""Propose a spatial probability polygon and certify its complete signed height cost."""
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import coo_matrix
from flint import arb
from signed_profile import local_caps
from weighted_green import H


def jumps(h):
    n=len(h)-1
    return [2*(h[1]-h[0])]+[2*(h[j-1]-2*h[j]+(h[j+1] if j<n else 0))
                             for j in range(1,n+1)]


def propose(T,dlo,dhi,caps,tail_price,n,verified_start=False,signed_limit=0,seed=None):
    assert 4<=n<=64
    m=len(T)-1
    # Payments and suffix sums for positive cosine, negative cosine, and
    # absolute cosine, followed by the polygon, its absolute slope jumps
    # and the upper envelope at the terminal height.
    P=5*m;J=P+n;last=J+n+1;dim=last+1+int(seed is not None)
    rows=[];cols=[];data=[]
    limits=[]
    def add(items,limit=0):
        i=len(limits);limits.append(limit)
        for j,x in items:
            if x:
                rows.append(i);cols.append(j);data.append(float(x))
    indices=np.arange(n)
    mult=np.ones(n)*2;mult[0]=1
    left=float(dlo.mid());right=float(dhi.mid());heights=np.array([float(t.mid()) for t in T])
    end=left*heights[-1];cut=192.
    for i in range(m):
        for col,offset in ((i,3*m),(m+i,4*m)):
            terms=[(offset+i,1),(col,-1),(2*m+i,-1)]
            if i+1<m:terms.append((offset+i+1,-1))
            add(terms)
        a=(left*H if verified_start else 0) if i==0 else left*heights[i]
        b=right*heights[i+1]
        if a<cut:
            z=min(cut,b)
            points=np.linspace(a,z,1+max(3,int(np.ceil((z-a)/.28))))
            for y in points:
                basis=np.cos(indices*y/(2*n))*mult*np.sinc(y/(4*n*np.pi))**2
                extra=[] if seed is None else [(last+1,seed[0](y/((left+right)/2)))]
                for sign,offset in ((1,3*m),(-1,4*m)):
                    add([(P+j,sign*v) for j,v in enumerate(basis)]+[(k,sign*v) for k,v in extra]+[(offset+i,-1),(last,-1)])
        if b>=cut:
            coeff=(end/max(a,cut))**2-1
            for offset in (3*m,4*m):add([(last,coeff),(offset+i,-1)])
    D=np.transpose([jumps([int(i==k) for i in range(n)]+[0]) for k in range(n)])
    for k,row in enumerate(D):
        for sign in (1,-1):
            add([(P+j,sign*z) for j,z in enumerate(row)]+[(J+k,-1)])
    add([(J+k,(2*n/end)**2) for k in range(n+1)]+[(last,-1)])
    extra=[] if seed is None else [(last+1,1)]
    add([(P+j,v) for j,v in enumerate(mult)]+extra,1)
    add([(P+j,-v) for j,v in enumerate(mult)]+[(k,-v) for k,v in extra],-1)
    A=coo_matrix((data,(rows,cols)),shape=(len(limits),dim)).tocsc()
    obj=np.zeros(dim)
    obj[:3*m]=[float(x.mid()) for values in (caps[0],caps[0],caps[1]) for x in values]
    obj[last]=float(tail_price.mid())
    if seed is not None:obj[last+1]=seed[1]/2
    bounds=[(0,None)]*dim
    assert 0<=signed_limit<=1e5
    for j in range(n):bounds[P+j]=(-signed_limit/(2*n),max(2.5,signed_limit)/(2*n))
    fit=linprog(obj,A_ub=A,b_ub=limits,bounds=bounds,method='highs')
    assert fit.success,fit.message
    heights=tuple(int(round(1e9*z)) for z in fit.x[P:P+n])+(0,)
    if seed is not None:return heights,int(round(1e9*fit.x[last+1]))
    return heights


def validate(h,T,dlo,dhi,caps,constant,tail_price,power_unit,allocate,verified_start=False):
    assert h[-1]==0 and len(h)>=3
    n=len(h)-1
    total=2*sum(h)-h[0]
    assert total>0
    mass=arb(2*sum(map(abs,h))-abs(h[0]))/total
    peak=arb(2*n*max(map(abs,h)))/total
    V=arb((2*n)**2*sum(map(abs,jumps(h))))/total
    end=V/(dlo*T[-1])**2
    target=[]
    for i,t in enumerate(T[1:]):
        lo=(dlo*H if verified_start else arb(0)) if i==0 else dlo*T[i]
        p,q=local_caps(lo,dhi*t,heights=h)
        target.append(((p-end.lower()).upper().max(0),(q-end.lower()).upper().max(0)))
    return mass*constant+peak*power_unit+2*(end*tail_price+allocate(target,*caps))
