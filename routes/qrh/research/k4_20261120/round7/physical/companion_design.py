"""Propose individual positive zero displacements, then price the resulting exact test."""
import argparse
from pathlib import Path
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix,eye,hstack,vstack
from flint import arb,ctx
from companion_cover import H,verify,reference_charge
import json


def design(lo,hi,size,count,mesh,fee,table,negative=0.):
    K=H+size;pi=np.pi
    a=(1-1e-12)*K*np.log1p(4*np.exp(-float(hi)/4))/2
    mass=pi*np.sin(a)/a
    labels=[(j,s) for j in range(1,count+1) for s in (-1,1)]
    b=np.array([2*pi*j+s*a for j,s in labels]);p=a*np.array([s for j,s in labels])/b
    g=lambda u,b:.5*np.sinc((u+b)/(2*pi))*np.sinc((u-b)/(2*pi))
    J=max(64,2*count)
    knots=np.array([a]+[2*pi*j+s*a for j in range(1,J+1) for s in (-1,1)]+[2*pi*(J+1)-a])
    l,r=knots[:-1],knots[1:]
    X,W=np.polynomial.legendre.leggauss(mesh)
    u=((l+r)[:,None]+(r-l)[:,None]*X).ravel()/2
    area=((r-l)[:,None]*W).ravel()/2
    old=g(u,a);change=old[:,None]*p-g(u[:,None],b)
    # Variables are the nonnegative displacement masses e, positive spatial
    # values on the quadrature mesh, and an upper bound on the band-edge ratio.
    m,n=change.shape
    top=hstack((csc_matrix(change),-eye(m),csc_matrix((m,1))))
    t=np.linspace(0,size/K,81)
    band=p-np.sinc(b*t[:,None]/pi)/np.sinc(a*t/pi)[:,None]
    bot=hstack((csc_matrix(band),csc_matrix((len(t),m)),-np.ones((len(t),1))))
    # Restrict to shapes for which the complete real-edge spectrum is monotone
    # and the physical multiplier stays away from its degenerate limiting case.
    safety=np.vstack((1-p,1-p*np.cos(a*size/K)))
    A=vstack((top,bot,hstack((safety,csc_matrix((2,m+1))))),format='csc')
    rhs=np.r_[-old,-np.ones(len(t)),.98,.999*np.cos(a*size/K)]
    if negative:
        nonnegative=hstack((-csc_matrix(band),csc_matrix((len(t),m+1))))
        A=vstack((A,nonnegative),format='csc')
        rhs=np.r_[rhs,np.ones(len(t))]
    slope=4.61/mass
    tail=(2*(pi-a)*np.cos(a)+2*np.sin(a))/(4*pi*pi*J)
    objective_e=slope*tail*(p-1)+fee*g(a,a)*p
    high_price=0. if table else float(reference_charge(lo,hi,size).mid())
    obj=np.r_[objective_e,slope*area,high_price]
    if table:
        data=json.loads(Path(table).read_text(encoding='utf8'))
        assert data['size']==size
        t=np.maximum(0,(size-(size+1280000)*np.arange(data['panels'])/data['panels'])/K)
        row=np.array(data.get('signed_rows',data['rows']))/data['scale']
        spectrum=(p*np.sin(a*t[:,None])-a*np.sin(t[:,None]*b)/b)/np.sin(a)
        obj[:n]+=2*np.diff(np.r_[0,row])@spectrum
        obj[-1]=0
    assert 0<=negative<=.2
    bounds=[(-negative,1)]*n+[(0,None)]*(m+1)
    fit=linprog(obj,A_ub=A,b_ub=rhs,bounds=bounds,method='highs')
    assert fit.success,fit.message
    coeff=[(j,s,round(float(z),6)) for (j,s),z in zip(labels,fit.x[:n],strict=True) if abs(z)>.00001]
    assert coeff
    return ','.join(f"{j}{'+' if s>0 else '-'}/{z:.6f}" for j,s,z in coeff)


if __name__=='__main__':
    ctx.prec=192
    p=argparse.ArgumentParser()
    p.add_argument('--lo',default='115.408');p.add_argument('--hi',default='115.42')
    p.add_argument('--size',type=int,required=True);p.add_argument('--count',type=int,default=24)
    p.add_argument('--mesh',type=int,default=16);p.add_argument('--fee',type=float,default=.025)
    p.add_argument('--height-table');p.add_argument('--sieve-table')
    p.add_argument('--negative',type=float,default=0.)
    p.add_argument('--check',action='store_true')
    v=p.parse_args()
    weights=design(v.lo,v.hi,v.size,v.count,v.mesh,v.fee,v.height_table,v.negative)
    print('prescribed companion weights',weights,flush=True)
    total=verify(v.lo,v.hi,v.size,1,'.3',1,64,'145','146','.0016',0,80,
                 height_table=v.height_table,sieve_table=v.sieve_table,weights=weights)
    if v.check:assert total<1
