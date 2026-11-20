"""Choose the signed vertical-line sources of a physical angular majorant (design only)."""
import argparse
import numpy as np
from scipy.optimize import linprog
from scipy import sparse


def problem(knots,theta,modes,positive,nangles=44,sub=4,elasticity=None):
    """Dimensionless coordinate x=omega*(sigma-a0), fixed ordinary exponential chord."""
    angles=np.arange(nangles+1)*np.pi/nangles
    fourier=np.cos(np.outer(angles,modes))
    target=np.maximum(0,np.cos(angles)) if positive else abs(np.cos(angles))
    count=len(knots)
    size=len(modes)
    ratio=np.exp(knots)
    # Variables are a common multiple of the ordinary source, then each
    # source's cosine coefficients divided by its unscaled ordinary weight.
    flexible=elasticity is not None
    nbase=count if flexible else 1
    cons=[]
    rhs=[]
    for k in range(count):
        line=np.zeros((len(angles),nbase+count*size))
        line[:,k if flexible else 0]=1
        line[:,nbase+k*size:nbase+(k+1)*size]=fourier
        cons.append(line);rhs.append(np.zeros(len(angles)))
    # Zero to the left of the first knot; use the right fundamental solution
    # of the half-line Dirichlet problem, whose value is already zero at x=0.
    eq=np.zeros((size,nbase+count*size))
    for j,m in enumerate(modes):
        eq[j,nbase+j::size]=ratio*np.exp(-m*knots)
    places=np.unique(np.r_[np.linspace(0,theta,sub*(count+1)+1)[1:], knots[1:], theta,
                           theta+np.arange(1,25)*.08])
    for x in places:
        B=ratio@np.maximum(0,x-knots)
        # One image at -k enforces the zero left boundary. At k=0 the
        # source variation is carried entirely by the derivative condition.
        G=np.empty((count,size))
        for j,m in enumerate(modes):
            G[:,j]=-ratio*np.exp(-m*abs(x-knots))*(-np.expm1(-2*m*np.minimum(x,knots)))/(2*m*B)
        line=np.zeros((len(angles),nbase+count*size))
        line[:,:nbase]=ratio*np.maximum(0,x-knots)/B if flexible else 1
        line[:,nbase:]=(fourier[:,None,:]*G).reshape(len(angles),-1)
        cons.append(line)
        rhs.append(target if x<=theta else np.zeros(len(angles)))
    A=sparse.csr_matrix(np.concatenate(cons))
    c=np.zeros(A.shape[1])
    c[:nbase]=np.exp((1-elasticity)*knots) if flexible else 1
    c/=sum(c)
    lp=linprog(c,A_ub=-A,b_ub=-np.concatenate(rhs),A_eq=eq,b_eq=np.zeros(len(eq)),
               bounds=[(0,None)]*nbase+[(None,None)]*(len(c)-nbase),method="highs")
    assert lp.success,lp.message
    return c@lp.x,lp.x[nbase:].reshape(count,size)


if __name__=="__main__":
    cli=argparse.ArgumentParser()
    cli.add_argument("--count",type=int,default=14)
    cli.add_argument("--step",type=float,default=.45)
    cli.add_argument("--positive",action="store_true")
    cli.add_argument("--degree",type=int,default=4)
    cli.add_argument("--elasticity",type=float)
    args=cli.parse_args()
    modes=np.arange(1 if args.positive else 2,args.degree+1,1 if args.positive else 2)
    knots=args.step*np.arange(args.count)
    k,weights=problem(knots,knots[-1]+args.step,modes,args.positive,elasticity=args.elasticity)
    print("mesh proposal",k,"modes",modes.tolist(),"first and last source",weights[0],weights[-1])
