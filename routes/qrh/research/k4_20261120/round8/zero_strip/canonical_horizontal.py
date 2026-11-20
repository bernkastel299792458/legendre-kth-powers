"""Fixed-height integral of the exponential-detector argument on a bounded Green edge."""
import json
from pathlib import Path
from flint import arb,ctx
from weighted_green import H


def bound(a,u,ell,d,left,right,W,lh,Q):
    T=u.exp();X=(u+W+lh).exp();R=1+d/u;pi=arb.pi()
    c=arb('.98');e=arb('1.05');assert ell<a<c<R and Q>0 and H>3*10**12
    ta=(R-a)/(R-ell);tc=(R-c)/(R-ell)
    PL=1/(pi*tc*(a-ell));PR=1/(pi*(1-ta)*(R-c))
    ll=(PL*2*left*T*u**2).log()*3/4;lr=(PR*2*right*u).log()/2
    la=ta*ll+(1-ta)*lr;lc=tc*ll+(1-tc)*lr
    N=(1+arb('1e-6'))**2/(1-1/arb(3*10**12))
    strip=N*(c-a)*(la.exp()-lc.exp())/(la-lc)
    # Direct Euler summation at N=ceil(T+2), uniformly for |Im s|<=T+1.
    z=(T+4)**(1-c)*(2+(T+4).log()+2/c)+1
    poly=(1+(Q*X).log())*(Q*X)**(1-c)
    narrow=(e-c)*(1+z*poly)
    far=2*(2-e)-2*(e-1).log()+1/(e-1)-1
    fedge=strip+narrow+far
    zsup=(T+4).sqrt()*(6+(T+4).log())+1
    nz=(zsup/(2-arb(2).zeta())).log()/(arb(15)/14).log()
    zarg=(2-a)*pi*(nz+arb(3)/2)
    return fedge,zarg+fedge


if __name__=='__main__':
    ctx.prec=160;data=json.loads((Path(__file__).with_name('phase_shift_extra.json')).read_text(encoding='utf8'))
    u=arb(36);r=data['rows'][str(36*data['sub'])];k=data['steps'].index('.012');d,w,lh=map(arb,data['triples'][0])
    left=arb(r['left_shifts'][0][k])/data['scale'];right=arb(r['moments'][0][1])/data['scale']
    for s in ('.82','.85','.87'):
        f,full=bound(arb(s),u,arb('.488'),d,left,right,w,lh,2310)
        print(s,'integral |f|',f.upper().str(12),'integral |arg D0|',full.upper().str(12),flush=True)
