"""explore_W_slope.py -- EXPLORATION (floats): slope of G(X)=sum mu^2 phi/l^2 in log X equals W=0.428250 (paper: 0.40282)."""
# quick float sanity check (exploration only): slope of G(X)=sum_{l<=X} mu^2(l)phi(l)/l^2 in log X
import numpy as np
N=10**7
mu=np.ones(N+1,dtype=np.int8); phi=np.arange(N+1,dtype=np.float64); sq=np.ones(N+1,bool)
s=np.ones(N+1,bool); s[:2]=False
for i in range(2,int(N**0.5)+1):
    if s[i]: s[i*i::i]=False
ps=np.nonzero(s)[0]
for p in ps:
    mu[p::p]*=-1; phi[p::p]*=(1-1/p)
    if p*p<=N: sq[p*p::p*p]=False
w=np.where(sq, phi/np.maximum(np.arange(N+1),1)**2, 0.0); w[0]=0
G=np.cumsum(w)
for a,b in [(10**5,10**6),(10**6,10**7)]:
    print(a,b,"(G(b)-G(a))/log10 =",(G[b]-G[a])/np.log(10))
print("6/pi^2*0.7044422009991 =",6/np.pi**2*0.7044422009991)
