"""Discover rational trigonometric majorants for the parity projection."""
import numpy as np
from scipy.optimize import linprog
from math import exp,log1p,pi,sin
from numpy.polynomial.legendre import leggauss
from pathlib import Path
import json
H=3000175332800;L=116
a=(1-1e-12)*H*log1p(4*exp(-L/4))/2
I=pi*sin(a)/a
def curve(deg):
    js=np.arange(deg+1)
    def matrix(t):
        return np.cos(t[:,None]*js[None,:])
    u,w=leggauss(180)
    t=(u+1)*a/2
    v=(u+1)*(pi-a)/2+a
    g=.5*np.sinc((a+t)/(2*pi))*np.sinc((a-t)/(2*pi))
    objective=(matrix(t).T@(w*a*(2*g/I-1/(2*pi)))+
               matrix(v).T@(w*(pi-a)/(2*pi)))
    lo=np.linspace(0,a,1500)
    hi=np.linspace(a,pi,1500)
    con=-np.concatenate((matrix(lo),matrix(hi)))
    rhs=-np.r_[np.zeros(len(lo)),np.ones(len(hi))]
    sol=linprog(objective,A_ub=con,b_ub=rhs,bounds=[(None,None)]*(deg+1),method='highs')
    assert sol.success
    return sol.fun,[f"{v:.14f}" for v in sol.x]
if __name__=="__main__":
    result={}
    for J in (1,2,3,4,5,6,7,8,10,12,15,20,24,30,36,48):
        cost,r=curve(J);result[J]=r
        print(J,cost,flush=True)
    Path(__file__).with_name("majorants.json").write_text(json.dumps(result,indent=1)+"\n",encoding="utf-8")
