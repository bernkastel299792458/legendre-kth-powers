import numpy as np
from scipy.optimize import linprog
th=np.linspace(0,np.pi,4001)
for Z in (5.43,4.896):
  for K in (2,3,4,6,8,12):
    # vars a0, a2..aK ; a1=1 ; minimize 2Z a0 + sqrt2*(0.5+sum a_k)  [b2'=2a0, b1'=sqrt2(0.5+sum)]
    n=K
    c=np.r_[2*Z, np.sqrt(2)*np.ones(K-1)]
    A=-np.column_stack([np.ones_like(th)]+[np.cos(k*th) for k in range(2,K+1)])
    b=np.cos(th)
    res=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*n,method='highs')
    a0=res.x[0]; s=res.x[1:].sum()
    cf=np.sqrt(2)*(0.5+s)+2*a0*Z
    print(f"Z={Z} K={K}: a0/a1={a0:.4f} sum_k>=2 a_k/a1={s:.4f}  -> b1'={np.sqrt(2)*(0.5+s):.3f} b2'={2*a0:.3f}  b1'+b2'Z={cf:.2f}  (Bellotti ~{0.714+2.167*Z:.2f})")
