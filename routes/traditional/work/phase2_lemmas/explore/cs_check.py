# float exploration: check Q(eps) <= (1/Delta^2) sum_n n^-s H(n)^2  at small scale
import numpy as np, math
from mpmath import zeta
def mobius(N):
    mu=np.ones(N+1,dtype=np.int64); isp=np.ones(N+1,dtype=bool); isp[:2]=False
    for p in range(2,N+1):
        if isp[p]:
            isp[2*p::p]=False; mu[p::p]*=-1; mu[p*p::p*p]=0
    mu[0]=0; return mu
U=100.0; V=U**2.2; eps=0.05; s=1+eps
Vi=int(V); mu=mobius(Vi)
D=math.log(V/U)
g=lambda d: min(1.0, max(0.0, math.log(V/d))/D)
lam=np.array([0.0]+[mu[d]*g(d) for d in range(1,Vi+1)])
# Q directly via sum over n up to big N of Psi^2/n^s / zeta(s)? use diagonal form exactly:
# Q = sum_delta phi_s(delta)/delta^{2s} y_delta^2 , y_delta = sum_{delta|d} lam_d d^-s
ds=np.arange(1,Vi+1,dtype=float)
w=lam[1:]*ds**(-s)
y=np.zeros(Vi+1)
for dl in range(1,Vi+1):
    if mu[dl]==0: continue
    y[dl]=w[dl-1::dl].sum()
# phi_s
phis=ds**s
for p in range(2,Vi+1):
    if mu[p]==-1 and all(p%q for q in range(2,int(p**0.5)+1)):
        phis[p-1::p]*=(1-p**(-s))
Q=sum(phis[dl-1]*y[dl]**2 for dl in range(1,Vi+1) if mu[dl]!=0)
# M1(y)
mus=mu[1:].astype(float)
def M1(yy):
    if yy<1: return 0.0
    m=int(yy); k=np.arange(1,m+1,dtype=float)
    return float(np.sum(mus[:m]*k**(-s)*np.log(yy/k)))
Hs=np.array([M1(V/n)-M1(U/n) for n in range(1,Vi+1)])
bound=np.sum(ds**(-s)*Hs**2)/D**2
z=float(zeta(s))
print("Q=",Q," bound=",bound," zetaQ=",z*Q," zeta*bound=",z*bound)
# direct check of zeta Q = sum Psi^2/n^s via truncation N large
N=2000000
Psi=np.zeros(N+1)
for d in range(1,Vi+1):
    if lam[d]!=0: Psi[d::d]+=lam[d]
n=np.arange(1,N+1,dtype=float)
print("partial sum Psi^2/n^s up to N:",np.sum(Psi[1:]**2*n**(-s)), " tail est ~", (N**(-eps))/eps/D)
