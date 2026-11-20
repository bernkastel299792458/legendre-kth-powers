"""Common tilted means for all positive mixtures of the strip bandwidths."""
import numpy as np
from scipy.optimize import minimize
from flint import arb

from shell_obstruction import H,T,bmax,epsilon,kernel,prime_bin


def check():
    budget=arb('.000055')
    slope=arb('.01')
    mesh=32
    bins=[]
    for i in range(8*mesh,60*mesh):
        n=int(prime_bin(i,mesh).lower().floor().unique_fmpz())
        if n>=1:bins.append((arb(i)/mesh,arb(i+1)/mesh,n))
    S=arb('2.5');u=arb('.03');q=arb(6)/5
    mixing=arb('.124')
    def cost(w):
        return (1-w)**q+epsilon**(1-q)*w**q*(q*(q-1)*S/(1-2*u)).exp()
    assert cost(mixing)<budget**(-2*(q-1))
    e=epsilon.sqrt();t=1/arb(2).sqrt()
    fourth=(arb(3)/8).sqrt()*t*(1/budget-1/(t*(1+e)))
    N=[arb(n).sqrt() for _,_,n in bins]
    caps=[n*(arb(1).min(mixing*u*(l/2).exp())) for n,(l,r,_) in zip(N,bins)]
    rows=[[(1+epsilon*l.exp())/(2*budget**2) for l,r,n in bins],
          [fourth*(1+e*l.exp()) for l,r,n in bins],
          [mixing**2*S*l.exp() for l,r,n in bins]]
    rates=[n*l*(-arb('.875')*r).exp()/(1+(-arb('.75')*l).exp())
           for n,(l,r,_) in zip(N,bins)]

    # A finite numerical optimization suggests one common vector. Only the
    # subsequent rational vector and its ball certificates enter the proof.
    re=np.array([float(r) for l,r,n in bins])
    a=np.arange(20,60.01,.5)[:,None]
    heads=100+np.expm1(-.01*a)/(.0001*a)+.04-float(bmax)
    mat=np.array([float(v) for v in rates])*np.maximum(1-re/a,0)/heads
    inv=1/np.array([[float(z) for z in row] for row in rows])
    k=len(a);L=len(rows)
    def obj(x):
        h=x[:k]@mat
        z=h/(x[k:]@inv)
        return np.sum(h*z),np.concatenate([2*mat@z,-inv@(z*z)])
    cons=[dict(type='eq',fun=lambda x:sum(x[:k])-1,jac=lambda x:np.r_[np.ones(k),np.zeros(L)]),
          dict(type='eq',fun=lambda x:sum(x[k:])-1,jac=lambda x:np.r_[np.zeros(k),np.ones(L)])]
    start=np.r_[np.ones(k)/k,np.ones(L)/L]
    opt=minimize(lambda x:obj(x)[0],start,jac=lambda x:obj(x)[1],bounds=[(0,1)]*(k+L),
                 constraints=cons,method='SLSQP',options={'maxiter':300,'ftol':1e-11})
    xs=np.maximum(opt.x,0)
    z=(xs[:k]@mat)/(xs[k:]@inv)
    z/=np.sqrt(np.max(inv@(z*z)))
    z=np.minimum(z,np.array([float(v) for v in caps])*.999)
    z=[arb(max(0,int(a*10**9)))/10**9 for a in z]
    scale=max(sum((a*a/d for a,d in zip(z,row)),arb(0)).upper() for row in rows).max(1).sqrt()*arb('1.000000001')
    z=[a/scale for a in z]
    assert all(a<cap for a,cap in zip(z,caps))
    assert all(sum((a*a/d for a,d in zip(z,row)),arb(0))<1 for row in rows)

    # Independent certificates for the area and all individual gains relative
    # to their own peak. Both are preserved under positive normalized mixing.
    dx=1/(bmax*512);j=0;gain=arb(0);linear=arb(0);lowest=arb(2);max_area=arb(0)
    for i in range(320,960):
        a=arb(i)/16;right=arb(i+1)/16
        Q=kernel(slope,arb(0),a)+arb('.04')-bmax
        upper=kernel(slope,arb(0),right)+arb('.04')-bmax
        while j<len(bins) and bins[j][1]<=a:
            v=z[j]*rates[j]
            gain+=v;linear+=v*bins[j][1]
            j+=1
        lowest=lowest.min((gain-linear/a)/upper)
        area=arb(0)
        for n in range(512):
            y=dx*(n+arb('.5'))
            peak=kernel(slope,y,a)+arb('.04')+arb(1)/32+a*a*dx/12-bmax
            area+=2*dx*(peak.max(0)/Q)**2
        max_area=max_area.max((420070*area/(T-H)).sqrt())
    print("all positive mixtures, common square-root allowance",max_area.str(13),
          "certified minimum ratio",lowest.str(13))
    assert max_area<budget and lowest>arb('1.005')


if __name__=='__main__':
    check()
