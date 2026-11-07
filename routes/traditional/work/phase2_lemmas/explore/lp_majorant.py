# float exploration: best positive combination of n^{-eps} majorising e^{-n/X} on n >= U
import numpy as np, math
from scipy.optimize import linprog
def run(L,u,v,x, K=40):
    Lu=u*L; Lv=v*L; D=Lv-Lu; lX=x*L
    Phi=lambda e: math.exp(-e*Lu)*(1-math.exp(-e*D))/(e*e*D*D)   # model of zeta Q(eps) - 1
    eps=np.exp(np.linspace(math.log(0.2/lX), math.log(30/lX), K))
    ys=np.linspace(Lu, lX+8, 4000)
    A=-np.exp(-np.outer(ys,eps)); b=-np.exp(-np.exp(ys-lX))
    c=np.array([Phi(e) for e in eps])
    res=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*K,method='highs')
    # single Rankin
    best1=min((e*math.exp(lX*e-1) if False else (e*math.exp(lX)/math.e)**e*Phi(e), e) for e in eps)
    # true (model)
    ys2=np.linspace(Lu,lX+10,200001); rho=np.minimum(ys2-Lu,D)/D**2
    true=np.trapezoid(rho*np.exp(-np.exp(ys2-lX)),ys2)
    used=[(eps[i]*lX, res.x[i]) for i in range(K) if res.x[i]>1e-9]
    print(f"L={L} u={u} v={v} x={x}: true(model)={true:.3f}  Rankin1={best1[0]:.3f} (a={best1[1]*lX:.2f})  LP={res.fun:.3f}  terms(a,c)={[(round(a,2),round(cc,4)) for a,cc in used]}")
run(29,2.1781287,4.4744028,7.0798370)
run(50,1.3227366,2.3928627,3.9675279)
run(80,0.9414561,1.5092573,2.6078943)
run(110,0.7956163,1.2246505,2.1317435)
