"""Fit a spatial density to the detector's cumulative height costs (proposal only)."""
from functools import partial
from types import FunctionType
import argparse

import numpy as np
from scipy import sparse
from scipy.optimize import linprog
from flint import arb,ctx
import height_profile as profile


def fit(rows,L,n,step,top,amp):
    heights,counts,beta,hinges,far,final=rows
    a=arb(L)
    d=(4*(-a/4).exp()).log1p()
    y=np.array([float(t*d) for t in heights])
    w=profile.exact.weights([beta],a)
    cumulative=np.array([float(w[0]*v+profile.exact.dot(w[1:],r))
                         for v,r in zip(counts,hinges,strict=True)])
    prices=np.diff(np.r_[0,cumulative,float(profile.exact.dot(profile.exact.weights(far,a),final))])
    # The printed polygon is tested subsequently on independently recomputed interval data.
    grid=np.arange(top*step+1)/step
    m=len(grid)
    cost=np.zeros(m)
    bend_cost=0.
    for t,v in zip(y,prices,strict=True):
        if t>=top:
            bend_cost+=v/t**2
        else:
            j=int(t*step)
            f=t*step-j
            cost[j]+=(1-f)*v
            cost[j+1]+=f*v
    t=np.arange(n)/(2*n)
    four=np.cos(np.outer(grid,t))*np.sinc(grid[:,None]/(4*n*np.pi))**2
    eye=sparse.eye(m)
    nodal=np.pad(np.diag(np.r_[1,np.full(n-1,.5)]),((0,2),(0,0)))
    curv=np.zeros((n+1,n))
    curv[0]=2*(nodal[1]-nodal[0])
    for j in range(1,n+1):
        curv[j]=2*(nodal[j-1]-2*nodal[j]+nodal[j+1])
    curv*=(2*n)**2
    mono=sparse.diags([-np.ones(m-1),np.ones(m-1)],[0,1],shape=(m-1,m))
    end=sparse.csr_matrix(([-1.],([0],[m-1])),shape=(1,m))
    matrix=sparse.bmat([[four,-eye,None],[-four,-eye,None],[None,mono,None],
        [curv,None,-sparse.eye(n+1)],[-curv,None,-sparse.eye(n+1)],
        [None,end,np.ones((1,n+1))/top**2]],format="csr")
    obj=np.r_[np.zeros(n),cost,np.full(n+1,bend_cost)]
    norm=np.zeros(len(obj));norm[:n]=1
    sol=linprog(obj,A_ub=matrix,b_ub=np.zeros(matrix.shape[0]),A_eq=norm[None,:],b_eq=[1],
                bounds=[(0,amp/(2*n))]+[(0,amp/n)]*(n-1)+[(0,None)]*(m+n+1),method="highs")
    assert sol.success,sol.message
    out=np.rint(1000000*2*n*sol.x[:n]/np.r_[1,np.full(n-1,2)]).astype(int)
    print("proposal objective",sol.fun,"heights",list(map(int,out))+[0],flush=True)


if __name__=="__main__":
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument("--anchor",default="146.23")
    cli.add_argument("--n",type=int,default=32)
    cli.add_argument("--step",type=int,default=8)
    cli.add_argument("--top",type=int,default=192)
    cli.add_argument("--height",type=float,default=1.495)
    a=cli.parse_args()
    ctx.prec=160
    base=profile.exact.test
    provider=partial(profile.mellin_bridge.finite_row,causal="real")
    run=FunctionType(base.__code__,dict(base.__globals__,cap_table=lambda d:None,
                     finite_row=provider),base.__name__,base.__defaults__,base.__closure__)
    args=(a.anchor,str(float(a.anchor)+.01),profile.mellin_bridge.PARAM,20,64,3,96,
          2**20,"1",2,210,"centered",2310)
    data=run(*args,hi=46,interpolate=True,spectrum_data=lambda *args:args,tight_rows=True)
    fit(data,a.anchor,a.n,a.step,a.top,a.height)
