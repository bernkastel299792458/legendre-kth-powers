import math, sys, warnings
warnings.filterwarnings('ignore')
sys.path.insert(0,'.')
import belmodel as bm
from belmodel import model, rows, nu2
from scipy.optimize import differential_evolution
def nu_bty(L): return max(1/(4.896*L), nu2(L))
def variant(L0,L1,s,u,x,v,w, fix=False, Zc=None, trig=False, d4scale=1.0):
    nu_fn = (lambda L: max(1/(Zc*L), nu2(L))) if Zc else ((lambda L: bm.nu1(L)) if L0<46.2 else (lambda L: nu2(L)))
    o=model(L0,L1,s,u,x,v,w,nu_fn=nu_fn,d4scale=d4scale)
    if not math.isfinite(o['C']): return o
    den=o['c1']**2-o['c5']
    c2,c3,c4=o['c2'],o['c3'],o['c4']
    b1,b2,Z=o['b1'],o['b2'],o['Z']
    if trig:   # best trig-poly local zero count (LP above): b2 -> 1.22 + (b2-2), b1 -> 1.69/0.707*b1
        b2=b2-2+1.22; b1=b1*1.69/0.7071
    cf=b1+b2*Z
    if fix:
        L=L0
        rho=math.exp(-2*((x-u)*L+2*math.log(L))*nu_fn(L0))
        numb=math.log(1/nu_fn(L1))
        c2=(1+rho)/2*c2
        c3=c3/(2*1.12*numb)*(1+rho)*(numb+1.96)
        c4=(1+rho)*c4
        C=2*(c2+c3+c4)*cf/den
    else:
        C=(c2+c3+c4)*cf/den
    o=dict(o); o['C']=C; return o
def fom_opt(R, Z1=4.9, **kw):
    def f(p):
        u,x,v,w=p
        if not (w<u<v and x>=u+v): return 1e9
        try: o=variant(R[0],R[1],R[2],u,x,v,w,**kw)
        except (OverflowError,ValueError,ZeroDivisionError): return 1e9
        if not (o['c1']>0 and o['C']>0 and math.isfinite(o['C'])): return 1e9
        return math.log(o['C'])+2*x/Z1
    res=differential_evolution(f,[(0.2,4),(0.8,12),(0.4,8),(0.005,1.2)],seed=7,tol=1e-10,maxiter=2000,popsize=30,polish=True)
    o=variant(R[0],R[1],R[2],*res.x,**kw); return o
for R in (rows[1],rows[3],rows[5],rows[6],rows[7]):
    fom_tab=R[7]*math.exp(R[8]/4.9)
    fixonly=variant(*R[:7],fix=True)
    print(f"row {R[0]:.1f}-{R[1]:.1f}: table FOM {fom_tab:.3g}; counting-fix at table params: C x{fixonly['C']/R[7]:.2f}")
    for name,kw in [('re-opt FOM only',{}),('+counting fix',dict(fix=True)),('+fix+Z4.896',dict(fix=True,Zc=4.896)),('+fix+Z+trig',dict(fix=True,Zc=4.896,trig=True)),('+fix+Z+trig+d4/3',dict(fix=True,Zc=4.896,trig=True,d4scale=1/3)),('+fix+Z+trig+d4/10',dict(fix=True,Zc=4.896,trig=True,d4scale=0.1))]:
        o=fom_opt(R,**kw); fom=o['C']*math.exp(o['B']/4.9)
        print(f"    {name:22s} C={o['C']:9.0f} B={o['B']:6.3f} FOM={fom:9.3g} FOM/table={fom/fom_tab:.3f}  (Delta k ~ {4.9*math.log(fom_tab/fom):+.1f})")
