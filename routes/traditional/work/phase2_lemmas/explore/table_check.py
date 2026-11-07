import sys, math, numpy as np
sys.path.insert(0,'..')
from lemmaA_d4 import M1Data, f_up, f_down
from flint import arb
import mpmath as mp
mp.mp.dps=30
D=M1Data("0.00979")
mu=None
from lemmaA_d4 import get_mu
mu=get_mu(D.Y0)
s=mp.mpf("1.00979")
def M1(y):
    return mp.fsum(int(mu[k])*mp.mpf(k)**(-s)*mp.log(mp.mpf(y)/k) for k in range(1,int(y)+1) if mu[k]!=0)
for m in (1,2,3,10,100,1000,12345):
    print(m, D.vlo[m], D.vhi[m], M1(m))
A=float(D.A.mid()); B=float(D.B.mid())
print("A=",D.A," B=",D.B)
# R at large table points vs rbar
for y in (16, 100, 1000, 10**4, 10**5, 10**6, 2*10**6):
    R=max(abs(D.vlo[y]-A-B*math.log(y)),abs(D.vhi[y]-A-B*math.log(y)))
    print(y, "R=",R, " rbar=", f_up(D.rbar(arb(y).log())))
# max |R| over [Y0/2, Y0] from table
ys=np.arange(D.Y0//2, D.Y0+1)
R=np.maximum(np.abs(D.vlo[ys]-A-B*np.log(ys)),np.abs(D.vhi[ys]-A-B*np.log(ys)))
print("max|R| on [Y0/2,Y0] =",R.max()," rbar(Y0/2)=",f_up(D.rbar(arb(D.Y0//2).log())))
print(D.range_log(arb(0),arb(0.5)), D.range_log(arb(14),arb(15)), D.range_log(arb(-1),arb(0.1)))
