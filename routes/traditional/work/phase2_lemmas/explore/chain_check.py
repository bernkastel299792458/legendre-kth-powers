# float sanity check of the full inequality chain of Lemma A at small scale
import numpy as np, math
from mpmath import zeta
import sys
sys.path.insert(0,'..')
from lemmaA_d4 import mobius_sieve
U=50.0; V=U**2.2; X=(U*V)**1.07; eps_list=[0.02,0.05,0.08,0.12]
D=math.log(V/U); Vi=int(V)
N=int(25*X)
mu=mobius_sieve(N).astype(np.int64)
g=lambda d: min(1.0, max(0.0, math.log(V/d))/D)
Psi=np.zeros(N+1)
for d in range(1,Vi+1):
    if mu[d]!=0: Psi[d::d]+=mu[d]*g(d)
n=np.arange(1,N+1,dtype=float)
L=math.log(X)  # pretend L^2/U part negligible; use weight e^{-n/X} only (upper bound of w)
S_true=np.sum(Psi[1:]**2/n*np.exp(-n/X))
print("U,V,X =",U,V,X,"  S_true (with e^{-n/X}) =",S_true, "  minus n=1:",S_true-math.exp(-1/X))
mus=mu[1:Vi+1].astype(float)
def M1(y,s):
    if y<1: return 0.0
    m=int(y); k=np.arange(1,m+1,dtype=float)
    return float(np.sum(mus[:m]*k**(-s)*np.log(y/k)))
for eps in eps_list:
    s=1+eps
    H=np.array([M1(V/k,s)-M1(U/k,s) for k in range(1,Vi+1)])
    k=np.arange(1,Vi+1,dtype=float)
    zQb=float(zeta(s))*np.sum(k**(-s)*H**2)/D**2
    zQ=np.sum(Psi[1:]**2*n**(-s))  # truncated (lower bound of zeta Q)
    rank=(eps*X/math.e)**eps
    print(f"eps={eps}: zetaQ(trunc)={zQ:.4f}  CS-bound={zQb:.4f}  bound on S-1: {rank*(zQb-1):.4f}")
