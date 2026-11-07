import sys, math
sys.path.insert(0,'.')
from lemmaB_count import cf_upper, nu_of, f_up, f_down
from flint import arb
def cf_disc(Z,L,lam,dfac=1.0):
    nu=1/(Z*L); d=nu*dfac; r=d*math.sqrt(1+lam*lam/4)
    E=(L+4.7098)/(4+8*r)+(4/math.pi-1)*math.log(1+1/r)/(1+2*r)+2.6908+8*r/(1+2*r)**2*(r*(2*L-1)+4)
    return 2*r*(E+1/r)/(d*L)
for (a0,L0,L1,nm) in ((0.9927,math.log(3e12),29,'classical'),(0.985,80,90,'ford')):
    Z0=1/f_down(nu_of(nm,arb(L0))*arb(L0))
    for lam in (1,2,4,8,10,13):
        cf,det=cf_upper(a0,nm,L0,L1,hfac=lam)
        print(f"{nm:9s} [{L0:.1f},{L1}] lambda={lam:3d}: Lemma B cf<={f_up(cf):7.3f}   TZ-disc cf(delta=nu)={cf_disc(Z0,L1,lam):7.3f}  ratio={f_up(cf)/cf_disc(Z0,L1,lam):.3f}  rho={det['rho']} a0={det['a0']}")
