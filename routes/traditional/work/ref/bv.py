import numpy as np, math, sys
def mobius_upto(n):
    mu=np.ones(n+1,dtype=np.int8); isp=np.ones(n+1,dtype=bool); isp[:2]=False
    for p in range(2,n+1):
        if isp[p]:
            isp[2*p::p]=False
            mu[p::p]*=-1
            mu[p*p::p*p]=0
    mu[0]=0; return mu
def run(lu,tau,mult=1.0):
    U=10**lu; V=U**tau; N=int(U*V*mult)
    Vi=int(V); Ui=int(U)
    mu=mobius_upto(Vi)
    Psi=np.zeros(N+1)
    lVU=math.log(V/U)
    for d in range(1,Vi+1):
        m=mu[d]
        if m==0: continue
        if d<=U: wgt=float(m)
        else: wgt=m*math.log(V/d)/lVU
        Psi[d::d]+=wgt
    n=np.arange(1,N+1)
    S=np.cumsum(Psi[1:]**2/n)
    for frac in (1/ (U*V/U), 1/U**0.5, 1.0, mult):
        k=int(min(N, U*V*frac)); 
    out=[]
    for M in (int(V), int(U*V)):
        if M<=N: out.append((M, S[M-1]))
    lnN=math.log(U*V)
    f=(1.084*(tau+1)+1.301*(1+tau*tau)-0.116)/(tau-1)
    rza=3.09*lnN/lVU*f
    print(f"U=10^{lu}, tau={tau}: sum_(n<=V)={out[0][1]:.3f}, sum_(n<=UV)={out[1][1]:.3f};  logN/log(V/U)={lnN/lVU:.3f};  RZA bound={rza:.1f}; ratio RZA/actual={rza/out[1][1]:.1f}")
for lu,tau in ((2.5,1.8),(2.2,2.0),(2.0,2.5),(2.5,1.6)):
    run(lu,tau)
