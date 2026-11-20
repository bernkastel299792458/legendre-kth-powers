"""Uniform weighted reciprocal Mobius tails for the true rational AFE rows."""
import numpy as np
from flint import arb
from quarter_diagonal import primes,zq
from quarter_integer_ratios import factors
from quarter_long_row import mobius,prefix

# Recompute the closed dyadic intervals via quarter_mertens_finite.py.
NANOS=(3258868,1897266,1213758,657944,445503,250714,140383,97076,46707,30668,17384,13088)


def weighted(s,capbits=16):
    q=2310;P=q*s;u=arb(3)/2
    bdr=10**14;rhohalf=arb(1);rhoone=arb(1)
    for p in primes(q):
        rhohalf/=1-1/arb(p).sqrt();rhoone/=1-1/arb(p)
    def upper(v):
        top=(2*arb(1)).sqrt()*rhohalf/arb(max(bdr,v)).sqrt()+arb('.010032')*rhoone/arb(bdr).log()
        if v<=bdr:
            top=top.max((2*arb(1)).sqrt()*rhohalf/arb(v).sqrt())
        return top
    pfx,den=prefix(mobius(q,2**18))
    vals=[]
    cutoff=2**18
    for j in range(18):
        m=int(np.max(abs(pfx[2**j-1:2**(j+1)])))
        vals.append(arb(m+cutoff)/den)
    vals.extend(arb(x)/10**9 for x in NANOS)
    vals.extend(upper(2**j) for j in range(30,76))
    for k in range(74,-1,-1):vals[k]=vals[k].max(vals[k+1])
    cap=2**capbits;f=factors(cap);coeff=[arb(1)]*cap
    W=zq(u,P)/zq(2*u,P);M=arb(1);c=1000
    if s>1:M/=1-1/arb(s)
    for p in range(2,c+1):
        if p==f[p] and P%p:M*=1+1/((1+arb(p)**u)*(p-1))
    M*=(arb(c)**(-u)/(u*(1-1/arb(c)))).exp()
    # Isolate h=1; the other bins each have h<2^(j+1).
    groups=[arb(0)]*capbits;head=arb(1)
    for h in range(2,cap):
        p=f[h];k=h//p
        if q%p==0:coeff[h]=arb(0)
        else:
            coeff[h]=coeff[k]
            if s%p and k%p:coeff[h]/=1+arb(p)**u
        v=coeff[h]/h;head+=v;groups[h.bit_length()-1]+=v
    tail=(M-head)*vals[0]
    out=[]
    for j in range(75):
        total=vals[j]+tail
        for i,m in enumerate(groups):
            total+=m*vals[max(j-i-1,0)]
        out.append(W*total)
    return out


def bound(t,entries):
    # Prefixes at a strict lower endpoint may use the integer before t.
    v=max(1,int((t-1).lower().floor().unique_fmpz()))
    return entries[min(len(entries)-1,v.bit_length()-1)]
