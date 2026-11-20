"""Every three-prime modulus in one multiplier annulus, including true resonances."""
from math import gcd
from flint import arb,ctx,fmpz
from actual_split import constants,H
from odd_sieve import denominator
from ramanujan_prefix import signed_maxima

def run(start=2500,end=11000,n_a=80,n_b=120,slabs=8):
    Q=223092870;z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();C=c.exp()
    eta=arb(int(fmpz(Q).euler_phi()))/Q;den=denominator(z,Q)
    assert 2500<=start<end<=1000000 and C/end>z and z*z<C
    pmin=C/(end*z);cmin=pmin.sqrt()
    gs=[arb(0)];g=arb(0)
    for n in range(1,end+3):
        if gcd(n,Q)==1 and fmpz(n).moebius_mu():g+=1/arb(int(fmpz(n).euler_phi()))
        gs.append(g)
    def G(v):return gs[int(v.upper().floor().unique_fmpz())]
    def harm(l,h,logcap=None):
        if h<l:return arb(0)
        assert 5000<l and h<arb("2.169e25")
        e=h.sqrt()*h.log()*(h.log()-2)/(8*arb.pi())
        span=(h/l).log()
        if logcap is not None:span=span.min(logcap)
        return (span+2*e/l)/l.log()+1/l
    # Coarse small-prime bins are counted exactly, aside from outward-expanded endpoints.
    aedges=[z*(pmin/z)**(arb(j)/n_a) for j in range(n_a+1)]
    arows=[(l,h,harm(l,h)*G(z/l)*l/(l-1)) for l,h in zip(aedges[1:],aedges[:-1])]
    bedges=[arb(29)*(z.sqrt()/29)**(arb(j)/n_b) for j in range(n_b+1)]
    brows=[]
    for l,h in zip(bedges,bedges[1:]):
        if h<100000:
            lo=max(29,int(l.lower().floor().unique_fmpz()))
            hi=int(h.upper().ceil().unique_fmpz())
            hh=sum((1/arb(p-1) for p in range(lo,hi+1) if fmpz(p).is_prime()),arb(0))
        else:hh=harm(l,h)*l/(l-1)
        brows.append((l,h,hh))
    we=[arb(start)*(arb(end)/start)**(arb(j)/slabs) for j in range(slabs+1)]
    peaks=signed_maxima(Q,[int((2*Q/w).upper().floor().unique_fmpz()) for w in we[:-1]])
    kap=arb("2.5e17");s=2*arb.pi()*arb(".0002")*(116-c-2*r).exp()*kap/(64*H)
    R=(s.sin()/s).max(arb(1)/4);tau=2**len(fmpz(Q).factor())
    M1=S*H*(2*r).exp()/(arb.pi()*kap)
    M=u*((2*r).exp()*A+2*arb(".0002")*(116-c).exp()*S)
    result=arb(0)
    for w0,w1 in zip(we,we[1:]):
        freq=int((2*Q/w0).upper().floor().unique_fmpz())
        high=min((2*u*M1*eta*tau*R**(64-n)*s**(-n)*(kap/((n-1)*w0)+1)
                  for n in range(2,65)),key=lambda x:float(x.upper()))
        factor=M*(eta+18*arb(peaks[freq][0])/Q)+high
        mass=arb(0)
        for al,ah,hw in arows:
            if ah*z<C/w1:continue
            row=arb(0)
            for bl,bh,bw in brows:
                lo=cmin.max(bl).max(C/(w1*ah*bh))
                hi=(z/bl).min(C/(w0*al*bl))
                if hi<lo:continue
                row+=bw*harm(lo,hi,(w1/w0).log())*lo/(lo-1)
            mass+=hw*row*G(z*w1*ah/C)
        result+=2*factor*mass/den**2
    return result

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--start",type=int,default=2500);ap.add_argument("--end",type=int,default=11000)
    ap.add_argument("--outer",type=int,default=80);ap.add_argument("--inner",type=int,default=120)
    ap.add_argument("--slabs",type=int,default=8);ap.add_argument("--upper");a=ap.parse_args()
    ctx.prec=144
    v=run(a.start,a.end,a.outer,a.inner,a.slabs)
    print("all three-prime actual signed middle upper",v.str(15))
    if a.upper:assert v<arb(a.upper)
