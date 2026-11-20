"""Dual lower certificate for independently charged prime shells on the full height interval."""
from math import factorial
from functools import lru_cache

import numpy as np
from scipy.optimize import minimize
from flint import arb

from strip_boundary import H,T,bmax,THETA
from strip_positive import kernel


epsilon=arb('4.2')/(T-H)


def costs(max_degree,budget):
    rows=[(1/(2*budget**2),epsilon)]
    for d in range(2,max_degree+1):
        e=epsilon**(arb(1)/d)
        t=arb(2)**(-1+arb(1)/d)
        scale=(arb(factorial(d))**(arb(1)/d))*t*(budget**(-arb(2)/d)-1/(t*(1+e)))
        assert scale>0
        rows.append((scale,e))
    # All higher degrees, including arbitrary nonnegative translations.
    scale=((-2*budget.log()+epsilon.log()/2)/(2*arb(1).exp()))
    assert 0<scale
    rows.append((scale,epsilon**(arb(1)/(max_degree+1))))
    return rows


@lru_cache(maxsize=1)
def primes():
    limit=9_000_000
    sieve=np.ones(limit+1,dtype=np.bool_)
    sieve[:2]=False
    for p in range(2,3001):
        if sieve[p]:sieve[p*p::p]=False
    return np.flatnonzero(sieve)


@lru_cache(maxsize=10000)
def prime_bin(i,mesh):
    l=arb(i)/mesh;r=arb(i+1)/mesh
    if r<=16:
        lo=int(l.exp().floor().unique_fmpz())
        hi=int(r.exp().floor().unique_fmpz())
        return arb(int(np.searchsorted(primes(),hi,side='right')-np.searchsorted(primes(),lo,side='right')))
    # Dusart, arXiv:1002.0442, Theorem 5.2.
    assert l.exp()>3594641
    return ((r.exp()*(1-arb('.2')/r**2)-l.exp()*(1+arb('.2')/l**2))/r).max(0)


def cells(A,free_until,stop,mesh=32):
    bins=[]
    for i in range(free_until*mesh,stop*mesh-1):
        l=arb(i)/mesh;r=arb(i+1)/mesh
        if r>=A:break
        lo=l*(-THETA*r).exp()*(1-r/A)/(1+(-arb('.75')*l).exp())
        hi=r*(-THETA*l).exp()*(1-l/A)
        B=prime_bin(i,mesh)*lo*lo
        if B>0:bins.append((l,l.exp(),B,B/hi))
    return bins


def witness(A0,A1,free_until,stop=60,verbose=False,exact=False):
    A=arb(A0);Aend=arb(A1)
    bins=cells(A,free_until,stop)
    cap=kernel(arb('.01'),arb(0),Aend)+arb('.04')-bmax
    dx=1/(bmax*512)
    integral=arb(0)
    for i in range(512):
        y=dx*(i+arb('.5'))
        q=kernel(arb('.01'),y,A)+arb('.04')+(Aend-A)/2+A**2*dx/12-bmax
        integral+=(q.max(0)/cap)**2*2*dx
    budget=(420070*integral/(T-H)).sqrt()
    tilt=None
    if exact:
        # Exact real second/fourth torus diagonals; all higher degrees follow
        # from the same two-branch probability tilt and Renyi monotonicity.
        t=1/arb(2).sqrt();e=epsilon.sqrt()
        real_c=(arb(3)/8).sqrt()
        fourth=real_c*t*(1/budget-1/(t*(1+e)))
        rows=[(1/(2*budget**2),epsilon),(fourth,e)]
        S=arb('2.5');u=arb('.03');q=arb(6)/5
        w=arb('.10')
        while True:
            trial=w+arb('.001')
            excess=(1-trial)**q+epsilon**(1-q)*trial**q*(q*(q-1)*S/(1-2*u)).exp()
            if not excess<budget**(-2*(q-1)):break
            w=trial
        assert (1-w)**q+epsilon**(1-q)*w**q*(q*(q-1)*S/(1-2*u)).exp()<budget**(-2*(q-1))
        tilt=(w,S,u)
    else:
        rows=costs(32,budget)
    q=[[s*(1+e*x)*B for _,x,B,_ in bins] for s,e in rows]
    if tilt:
        w,S,u=tilt
        q.append([w*w*S*x*B for _,x,B,_ in bins])
    # Floating point only proposes a nonnegative rational vector.
    inv=1/np.array([[float(a) for a in line] for line in q])
    qinf=np.array([float(b[3]) for b in bins])
    if tilt:
        mixing,_,u=tilt
        qinf=np.minimum(qinf,[float(arb('.999')*mixing*u*x.sqrt()*cap) for _,x,_,cap in bins])
    n=len(q)
    def val(l):return np.sum(1/(l@inv))
    def jac(l):
        w=1/(l@inv)
        return -inv@(w*w)
    res=minimize(val,np.ones(n)/n,jac=jac,bounds=[(0,1)]*n,
                 constraints=[dict(type='eq',fun=lambda l:sum(l)-1,jac=lambda l:np.ones(n))],
                 method='SLSQP',options={'ftol':1e-7,'maxiter':250})
    w=1/(np.maximum(res.x,0)@inv)
    w=w/np.sqrt(np.max(inv@(w*w)))
    w=np.minimum(w,qinf)
    w=[arb(max(0,int(t*10**8)))/10**8 for t in w]
    # Certify every shell choice by an Arb ellipsoid bound.
    norm=max(sum((g*g/z for g,z in zip(w,line)),arb(0)).upper() for line in q)
    norm=norm.max(1).sqrt()*arb('1.0000000001')
    w=[g/norm for g in w]
    assert all(g<=cap for g,(_,_,_,cap) in zip(w,bins))
    assert all(sum((g*g/z for g,z in zip(w,line)),arb(0))<1 for line in q)
    if tilt:
        mixing,_,u=tilt
        assert all(g/(mixing*x.sqrt()*cap)<u for g,(_,x,_,cap) in zip(w,bins))
    total=sum(w,arb(0))
    if verbose:
        for i in range(free_until//5*5,stop,5):
            group=sum((g for g,(l,_,_,_) in zip(w,bins) if i<=l<i+5),arb(0))
            if group>0:print('  log prime interval',i,i+5,group.str(7))
    print('exact' if exact else 'factorial','bandwidth',A0,A1,'free through log p',free_until,'dual budget',total.str(10),
          'available',cap.str(10),'excess',(total-cap).str(10),flush=True)
    return total-cap


if __name__=='__main__':
    for i in range(20,60,2):
        assert witness(i,i+2,8)>0
    gaps=[witness(i/2,(i+1)/2,8,exact=True) for i in range(40,80)]
    gaps += [witness(i,i+2,8,exact=True) for i in range(40,60,2)]
    assert min(gaps)>arb('.01')
    print('exact method minimum gap on all cells',min(gaps).str(10))
    assert witness(40,40,18)>arb('.032')
    assert witness(40,40,10,verbose=True,exact=True)>arb('.21')
    assert witness(40,40,10,verbose=True)>arb('4.29')
    assert witness(50,50,10,verbose=True)>0
