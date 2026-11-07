import math, sys, warnings
warnings.filterwarnings('ignore')
sys.path.insert(0,'.')
from belmodel import *
from opt1 import obj_factory, bounds, nu_bty
from scipy.optimize import differential_evolution
def best(R, mode='fom', Bmax=None, **kw):
    res=differential_evolution(obj_factory(R,mode,Bmax=Bmax,**kw),bounds,seed=5,tol=1e-10,maxiter=3000,popsize=40,polish=True)
    o=model(R[0],R[1],R[2],*res.x,**kw); return o, res.x
# narrower rows, Bellotti params
R=rows[5]
for L1 in (51,55,60):
    o=model(50,L1,*R[2:7]); print(f"row [e^50,e^{L1}] with Table-4 params: C={o['C']:.0f}")
R=rows[6]
for L1 in (61,70):
    o=model(60,L1,*R[2:7]); print(f"row [e^60,e^{L1}] with Table-4 params: C={o['C']:.0f}")
print()
for R in (rows[1], rows[5], rows[6]):
    o0,_=best(R,'fixB',Bmax=R[8])
    print(f"Row {R[0]}-{R[1]}, a0={R[2]}: baseline (re-opt, B<=Btab={R[8]}): C={o0['C']:.0f}")
    variants={
     'Z=4.896':dict(nu_fn=nu_bty),
     'b2: 2->1 (+O(r))':dict(b2override=lambda r: r*2*4.7908/4+2*r*math.log(1+1/r)*(4/PI-1)/(1+2*r)+2*r*2.6908+1+64*r*r/(1+2*r)**2),
     'd4/10':dict(d4scale=0.1),
     'parity x2 (rigour fix?)':dict(parity=2.0),
     'all: Z,b2->1,d4/10':dict(nu_fn=nu_bty,d4scale=0.1,b2override=lambda r: r*2*4.7908/4+2*r*math.log(1+1/r)*(4/PI-1)/(1+2*r)+2*r*2.6908+1+64*r*r/(1+2*r)**2),
    }
    for name,kw in variants.items():
        o,p=best(R,'fixB',Bmax=R[8],**kw)
        print(f"   {name:28s} C={o['C']:9.0f}  ratio={o['C']/o0['C']:.3f}")
