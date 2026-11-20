"""Translate a t-band mean of a true, weighted unit row into a physical cost."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import H,constants
from odd_sieve import denominator

def run(band=None,spectral=False):
    Q=210;eta=arb(48)/Q;K=arb(H);z,c,r,I,A,S,u=constants(1732099)
    G=denominator(z,Q);X=(c+2*r).exp();x=arb(116).exp();d=arb(".0002")*x/K
    area=X/K*A+2*d*S;pref=u*K*(-c).exp()
    t0,t1=(K/8,K/4) if band is None else map(arb,band)
    assert 0<t0<t1
    dis=arb(0);count=0
    for m in range(Q):
        if m and gcd(m,Q)==1:count+=1
        dis=dis.max(abs(count-eta*m)).max(abs(count-eta*(m+1)))
    N=int((t1*dis/eta).upper().ceil().unique_fmpz())
    shift=sum(arb(p).log()/(p-1) for p in (2,3,5,7))
    harmonic=eta*(arb(N).log()+arb.const_euler()+shift)+arb(16)/N
    sup=harmonic+eta/t0+dis*(1+(1+t1**2).sqrt())/N
    if spectral:
        from pathlib import Path
        import sys
        sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round7"/"mobius"))
        from unit_zeta import upper
        bounds=[]
        for start,end in ((t0,t1.min(arb(128))),(t0.max(arb(128)),t1.min(arb(10**6))),
                          (t0.max(arb(10**6)),t1)):
            if start>=end:continue
            cap=run((start,end))[0] if start<100 else upper(start,end,60,6)
            bounds.append(cap)
        if bounds:
            envelope=bounds[0]
            for cap in bounds[1:]:envelope=envelope.max(cap)
            sup=sup.min(envelope)
    cost=pref*area*sup/(arb.pi()*G**2)
    return sup,cost,arb(".00236860")/cost,arb(".00145")*cost
if __name__=="__main__":
    ctx.prec=160
    print("unit zeta supremum, cost per true row energy, full allowance for one row, cost if .00145",*(v.str(15) for v in run()))
