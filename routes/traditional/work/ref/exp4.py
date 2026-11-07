import math, sys, warnings
warnings.filterwarnings('ignore')
sys.path.insert(0,'.')
from belmodel import model, nu2
from scipy.optimize import differential_evolution
def opt(L0,L1,s,Bmax=None,Z1=4.9):
    def f(p):
        u,x,v,w=p
        if not (w<u<v and x>=u+v): return 1e9
        try: o=model(L0,L1,s,u,x,v,w)
        except (OverflowError,ValueError,ZeroDivisionError): return 1e9
        if not (o['c1']>0 and o['C']>0 and math.isfinite(o['C'])): return 1e9
        if Bmax is not None: return math.log(o['C'])+(0 if 2*x<=Bmax else 1e3*(2*x-Bmax))
        return math.log(o['C'])+2*x/Z1
    r=differential_evolution(f,[(0.2,4),(0.8,12),(0.4,8),(0.005,1.2)],seed=11,tol=1e-10,maxiter=2000,popsize=30,polish=True)
    return model(L0,L1,s,*r.x)
for L0 in (50,55,58):
    o=opt(L0,60,0.9892,Bmax=7.936); o2=opt(L0,60,0.9892)
    print(f"row [e^{L0},e^60], a0=0.9892: min C at B<=7.936: C={o['C']:.0f};  min C*e^(B/4.9): C={o2['C']:.0f} B={o2['B']:.2f} FOM={o2['C']*math.exp(o2['B']/4.9):.3g}")
# alpha0 sensitivity
for a0 in (0.9892,0.992,0.995):
    o=opt(50,60,a0,Bmax=7.936); print(f"row [e^50,e^60], a0={a0}: min C at B<=7.936: C={o['C']:.0f}")
