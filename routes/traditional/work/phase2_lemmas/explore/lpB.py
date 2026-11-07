# float exploration for Lemma B: choose rho and trig polynomial to minimise the box-count constant cf
import numpy as np, math
from scipy.optimize import linprog
def BTZ(r,logT):
    return (logT+4.709774)/(4+8*r)+(4/math.pi-1)*math.log(1+1/r)/(1+2*r)+2.6908+1e-24
def cf_eval(rho,a0,ak,Z,L,hfac=1.0,delta_over_nu=1.0):
    nu=1/(Z*L); d=nu*delta_over_nu; r=rho*d; h=hfac*d
    f=lambda X: X/(X*X+h*h/4)
    cmin=min(f(r+nu),f(r+d))-4*(r+d)/(1+2*r)**2
    num=a0*(1/r-1/(2*(1+r)**2))+sum(a*BTZ(r,L+math.log(k)) for k,a in ak.items())+BTZ(r,L)
    return num/(cmin*d*L)
def lp(rho,Z,L,K,hfac=1.0):
    nu=1/(Z*L); r=rho*nu; d=nu; h=hfac*d
    f=lambda X: X/(X*X+h*h/4)
    cmin=min(f(r+nu),f(r+d))-4*(r+d)/(1+2*r)**2
    den=cmin*d*L
    c=np.array([(1/r-1/(2*(1+r)**2))/den]+[BTZ(r,L+math.log(k))/den for k in range(2,K+1)])
    th=np.linspace(0,math.pi,3001)
    A=-np.column_stack([np.ones_like(th)]+[np.cos(k*th) for k in range(2,K+1)])
    b=np.cos(th)
    res=linprog(c,A_ub=A,b_ub=b,bounds=[(0,None)]*K,method='highs')
    val=res.fun+BTZ(r,L)/den
    return val,res.x
for (Z,L,label) in ((5.558691,28.73,'row29 classical Z=5.5587'),(4.896,28.73,'Z1=4.896 @29'),(5.43,50,'Ford@50'),(4.948,70,'Ford@70'),(4.788,80,'Ford@80'),(4.6,110,'Ford@110')):
    out=[]
    for K in (1,2,3,4,6,8):
        best=None
        for rho in np.linspace(0.5,8,76):
            if K==1:
                v=cf_eval(rho,1.0,{},Z,L); x=[1.0]
            else:
                v,x=lp(rho,Z,L,K)
            if best is None or v<best[0]: best=(v,rho,x)
        out.append((K,round(best[0],3),round(best[1],2),np.round(best[2],4)))
    print(label, "   Bellotti cf =", round(0.711+2.113*Z,3) if L<46 else '')
    for o in out: print("   K=%d cf=%.3f rho=%.2f a=%s"%o)
