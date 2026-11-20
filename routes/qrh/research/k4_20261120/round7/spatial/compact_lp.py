"""Search signed compact densities with a monotone frequency majorant."""
import argparse
import numpy as np
from scipy import sparse
from scipy.optimize import linprog


def optimize(n=32,step=8,top=160,p=.4,floor=.0,signed=True,amplitude=8,extension=1,free_prefix=False):
    # m0=midpoint mass, mj=combined mass at the two symmetric translates.
    # The underlying triangle has radius 1/(2n) and unit mass.
    y=np.arange(0,top*step+1)/step
    inner=n
    n=inner*extension
    t=np.arange(n)/(2*inner)
    four=np.cos(np.outer(y,t))*np.sinc(y[:,None]/(4*inner*np.pi))**2
    m=len(y)
    variables=n+m+n+1
    ident=sparse.eye(m)
    curvature=np.zeros((n+1,n))
    heights=np.diag(np.r_[1,np.full(n-1,.5)])
    heights=np.pad(heights,((0,2),(0,0)))
    curvature[0]=2*(heights[1]-heights[0])
    for j in range(1,n+1):curvature[j]=2*(heights[j-1]-2*heights[j]+heights[j+1])
    curvature*=(2*inner)**2
    chain=sparse.diags([-np.ones(m-1),np.ones(m-1)],[0,1],shape=(m-1,m))
    end=sparse.csr_matrix(([-1.],([0],[m-1])),shape=(1,m))
    mat=sparse.bmat([[four,-ident,None],[-four,-ident,None],[None,chain,None],
                     [curvature,None,-sparse.eye(n+1)],[-curvature,None,-sparse.eye(n+1)],
                     [None,end,np.ones((1,n+1))/top**2]],format="csr")
    levels=np.maximum(floor,y)**p
    cost=np.r_[np.zeros(n),np.diff(np.r_[0.,levels]),np.full(n+1,p/(2-p)*top**(p-2))]
    if free_prefix:
        cost[n]=0
        cost[n+int(floor*step)]+=floor**p
    eq=np.zeros(variables); eq[:n]=1
    lim=amplitude/(2*inner)
    bounds=[(-lim if signed else 0,lim)]+[(-2*lim if signed else 0,2*lim)]*(n-1)
    for j in range(inner,n): bounds[j]=(-2*lim,0)
    sol=linprog(cost,A_ub=mat,b_ub=np.zeros(mat.shape[0]),A_eq=eq[None,:],b_eq=[1],
                bounds=bounds+[(0,None)]*(m+n+1),method="highs")
    if not sol.success:raise ValueError(sol.message)
    mass=sol.x[:n]
    h=np.rint(1000000*2*inner*mass/np.r_[1,np.full(n-1,2)]).astype(int)
    print("signed",signed,"bound",sol.fun,"negative mass",-np.minimum(mass,0).sum(),
          "height max",abs(h).max()/1000000,"curvature",sum(abs(curvature@mass)),flush=True)
    print("heights",*h,0,flush=True)
    return h


if __name__=="__main__":
    arg=argparse.ArgumentParser(description=__doc__)
    arg.add_argument("--n",type=int,default=32)
    arg.add_argument("--floor",type=float,default=0)
    arg.add_argument("--p",type=float,default=.4)
    arg.add_argument("--top",type=int,default=160)
    arg.add_argument("--positive",action="store_true")
    arg.add_argument("--extension",type=int,default=1)
    arg.add_argument("--free-prefix",action="store_true")
    arg.add_argument("--amplitude",type=float,default=8)
    a=arg.parse_args()
    optimize(n=a.n,p=a.p,floor=a.floor,top=a.top,signed=not a.positive,amplitude=a.amplitude,
             extension=a.extension,free_prefix=a.free_prefix)
