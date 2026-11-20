"""Bound the short-prime exponential in mean using its Euler factors."""
from functools import lru_cache
from flint import arb,ctx,fmpz
from short_spectrum import estimate as spectrum,prime_cost
from finite_inverse import right


@lru_cache(None)
def norms(i,k,kap,prec,panels=192,arcs=128,power=1,modulus=1,right_factors=False,totient=False):
    assert ctx.prec==prec
    assert not (right_factors or totient) or power in (2,4)
    a=arb(i)/100-arb(1)/2
    b=arb(k)/100+arb(1)/2
    vs=[a+(b-a)*j*j/panels**2 for j in range(panels+1)]
    left=[(z-y)/(1-(-kap*y).exp())**2 for y,z in zip(vs,vs[1:])]
    rightw=[(z-y)/(1-(-kap*z).exp())**2 for y,z in zip(vs,vs[1:])]
    M=[arb(1),arb(1)]
    absolute=arb(0)
    factors=[int(p) for p,_ in fmpz(modulus).factor()]
    top=int(arb(kap).exp().upper().ceil().unique_fmpz())
    assert all(p<top for p in factors)
    phase=[arb.pi()*(2*j+1)/(2*arcs)+arb(0,arb.pi()/(2*arcs)) for j in range(arcs)]
    cosines=[[((j+1)*th).cos() for th in phase] for j in range(top.bit_length())]
    for p in range(2,top+1):
        if not fmpz(p).is_prime():continue
        n=p
        coeff=[]
        while n<=top:
            xi=arb(n).log()
            if xi<kap:
                def piece(v):return (-v*xi).exp()-(-v*(2*kap-xi)).exp()
                lo=sum(w*piece(v) for v,w in zip(vs[1:],rightw))
                hi=sum(w*piece(v) for v,w in zip(vs,left))
                val=power*arb(p).log()/arb(n).sqrt()*lo.union(hi)
                coeff.append(val)
                absolute+=val.upper()
            else:assert xi>kap
            n*=p
        if not coeff:continue
        for alpha in (0,1):
            values=[v*(arb(p)**(j+1)).sqrt()**alpha for j,v in enumerate(coeff)]
            angular=[(-sum(v*cosines[j][h] for j,v in enumerate(values))).exp().upper()
                     for h in range(arcs)]
            if right_factors:
                q=arb(p)**(-1-arb(k)/100)
                r=q*arb(p)**(arb(alpha)/2)
                for h in range(arcs):
                    angular[h]*=(1+r*r-2*r*cosines[0][h])**(arb(power)/2)/(1+q)**power
            if p in factors:
                r=arb(p)**(arb(alpha)/2-arb(i)/100)
                for h in range(arcs):
                    den=1+r*r-2*r*cosines[0][h]
                    assert den>0
                    angular[h]*=den**(-arb(power)/2)
            elif totient:
                r=arb(p)**(arb(alpha)/2-arb(i)/100)
                rho=arb(p)/(p-1)
                for h in range(arcs):
                    cs=cosines[0][h]
                    denom=1+r*r-2*r*cs
                    # This ratio is monotone in cos(theta); evaluate endpoints
                    # together to preserve cancellations at high primes.
                    assert denom>0
                    def ratio(c):
                        return (1+(rho*r)**2-2*rho*r*c)/(1+r*r-2*r*c)
                    angular[h]*=ratio(cs.lower()).max(ratio(cs.upper()))**(power//2)
            integral=sum(v.upper() for v in angular)/arcs
            M[alpha]*=integral
        if totient and p not in factors:
            r=arb(p)**(-arb(i)/100)
            absolute+=power*(r/((p-1)*(1-r))).log1p()
    if factors:
        absolute-=power*sum((-arb(p)**(-arb(i)/100)).log1p() for p in factors)
    return M[0],M[1],absolute.exp()


def mean(i,k,kap,lo,hi):
    length=hi-lo
    assert length>0
    m0,m1,l1sq=norms(i,k,kap,ctx.prec)
    cost=spectrum(i,hi,k,kap,96,False,t0=lo)/prime_cost(i,k,kap,96,ctx.prec).exp()
    candidates=[]
    for q in (1,4,16,64):
        R=length/q
        raw=(length+R)*m0+16*((length+R)/R).sqrt()*m1+4*l1sq/(R*arb(2).log()**2)
        candidates.append(cost*raw)
    v=candidates[0]
    for w in candidates[1:]:v=v.min(w)
    return v


if __name__=="__main__":
    ctx.prec=160
    for i in (55,57,59):
        for kap in (4,5,6,7):
            v=norms(i,75,kap,ctx.prec)
            b=arb(16).exp()
            print("mean-data",i,kap,[q.str(7) for q in v],(mean(i,75,kap,b,2*b)/b).str(8),flush=True)
