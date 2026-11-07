import math, sys, warnings
warnings.filterwarnings('ignore')
sys.path.insert(0,'.')
from belmodel import *
from scipy.optimize import differential_evolution
def nu_bty(L): return max(1/(4.896*L), nu2(L))
def obj_factory(R, mode, Bmax=None, Z1=4.9, **kw):
    L0,L1,s=R[0],R[1],R[2]
    def f(p):
        u,x,v,w=p
        if not (w<u<v and x>=u+v): return 1e9
        try: o=model(L0,L1,s,u,x,v,w,**kw)
        except (OverflowError, ValueError, ZeroDivisionError): return 1e9
        if not (o['c1']>0 and o['C']>0 and math.isfinite(o['C'])): return 1e9
        if mode=='fixB':
            pen = 0 if 2*x<=Bmax else 1e3*(2*x-Bmax)
            return math.log(o['C'])+pen
        return math.log(o['C'])+2*x/Z1
    return f
bounds=[(0.2,4),(0.8,12),(0.4,8),(0.005,1.2)]
sel=[rows[1],rows[3],rows[4],rows[5],rows[6],rows[7]]
for R in sel:
    base=model(*R[:7]); fom0=base['C']*math.exp(base['B']/4.9)
    res=differential_evolution(obj_factory(R,'fixB',Bmax=R[8]),bounds,seed=1,tol=1e-10,maxiter=3000,popsize=40,polish=True)
    o=model(R[0],R[1],R[2],*res.x)
    res2=differential_evolution(obj_factory(R,'fom'),bounds,seed=2,tol=1e-10,maxiter=3000,popsize=40,polish=True)
    o2=model(R[0],R[1],R[2],*res2.x)
    res3=differential_evolution(obj_factory(R,'fom',nu_fn=nu_bty),bounds,seed=3,tol=1e-10,maxiter=3000,popsize=40,polish=True)
    o3=model(R[0],R[1],R[2],*res3.x,nu_fn=nu_bty)
    print(f"{R[0]:5.1f}-{R[1]:5.1f} table C={R[7]:9.0f} B={R[8]:.3f} FOM=C*e^(B/4.9)={fom0:9.3g}")
    print(f"   min C at B<=Btab: C={o['C']:9.0f} B={o['B']:.3f} params={[round(t,4) for t in res.x]}")
    print(f"   min FOM:          C={o2['C']:9.0f} B={o2['B']:.3f} FOM={o2['C']*math.exp(o2['B']/4.9):9.3g} ratio={o2['C']*math.exp(o2['B']/4.9)/fom0:.3f} params={[round(t,4) for t in res2.x]}")
    print(f"   min FOM, Z=4.896: C={o3['C']:9.0f} B={o3['B']:.3f} FOM={o3['C']*math.exp(o3['B']/4.9):9.3g} ratio={o3['C']*math.exp(o3['B']/4.9)/fom0:.3f}")
