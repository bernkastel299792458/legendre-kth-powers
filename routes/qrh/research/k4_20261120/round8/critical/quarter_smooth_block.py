"""All direct internal frequencies below a cutoff after log averaging the AFE."""
from math import gcd,lcm
from functools import lru_cache
from flint import arb,ctx
from quarter_low_block import first_gap
from quarter_diagonal import primes


def test(N,alpha=arb(32),w=arb(1)/4,q=2310,U=arb(37)):
    s=arb(3)/4;a=2*s-1
    T=U.exp();Y=(U-3).exp();Dtime=arb("1.01")*T
    K=arb(".75")*3*10**12;ts=arb(".5")*3*10**12;P=128
    ds=int((arb(N)*w.exp()/(alpha*(q*ts/(2*arb.pi())).sqrt())).upper().floor().unique_fmpz())
    assert ds>=1
    eta=arb(sum(gcd(i,q)==1 for i in range(q)))/q
    cnt=0;high=low=arb(0)
    for i in range(q):
        v=cnt-eta*i
        high=high.max(v);low=low.min(v-eta);cnt+=int(gcd(q,i+1)==1)
    disc=high-low+1
    def power(r,L):
        ss=err=arb(0)
        for i in range(1,q+1):
            if gcd(i,q)==1:ss+=arb(i)**(-r)
            err=err.max(ss-eta*arb(i)**(1-r)/(1-r))
        err=err.max(ss-eta*arb(q)**(1-r)/(1-r)+2*disc*arb(q)**(-r))
        return (eta/(1-r)+err/L**(1-r)).min(1/(1-r))
    cut=65536;scale=2**44
    hh=[0];phi=list(range(cut+1))
    for p in range(2,cut+1):
        if phi[p]==p:
            for j in range(p,cut+1,p):phi[j]-=phi[j]//p
    for i in range(1,cut+1):hh.append(hh[-1]+((scale+i-1)//i if gcd(i,q)==1 else 0))
    const=arb.const_euler()+sum(arb(p).log()/(p-1) for p in primes(q))
    @lru_cache(None)
    def H(n):
        if n<=cut:return arb(hh[n])/scale
        return eta*(arb(n).log()+const)+arb(2**len(primes(q)))/n
    L=arb(0)
    for k in range(1,min(cut,ds)+1):
        if gcd(k,q)==1:L+=arb(phi[k])/k**2*H(ds//k)**2
    for m in range(1,ds//(cut+1)+1):
        lo=max(cut,ds//(m+1));hi=ds//m
        if hi<=lo:continue
        L+=(eta*(arb(hi)/lo).log()+2*disc/lo)*H(m)**2
    extras={}
    jn=int((arb(N)/Y).upper().floor().unique_fmpz())
    for j in range(1,jn+1):
        if gcd(j,q)==1:extras[j]=(arb(N)/(Y*j)).log().max(arb(0)).min(arb("9.5"))/arb("9.5")
    for j,v in extras.items():
        assert j<=cut
        L+=2*v/j*sum((arb(phi[b])/b*H(ds//b) for b in range(1,j+1) if j%b==0),arb(0))
        L+=v*sum((z/lcm(j,k) for k,z in extras.items()),arb(0))
    one=power(s,arb(N)/ds)*arb(N)**(1-s)*(H(ds)+sum((v/j for j,v in extras.items()),arb(0)))
    nenergy=power(a,arb(N)/(ds*ds))*arb(N)**(1-a)*L
    vprime=4*P/K+4096/Dtime+3*(4*w).exp()/(2*w*ts)
    rad=vprime*N/2
    # Tail for sum_{j>rad,(r+j,q)=1} 1/j^2 from interval discrepancy.
    head,den=first_gap(q)
    if rad>=q:
        gap=arb(head)/den+eta*(rad/q).log()+2*disc/q
        gap+=eta+2*disc/rad
    else:
        gap=arb(head)/den+rad*(eta/q+2*disc/q**2)
    # The restricted lower edge in the coefficient step has negligible mass.
    mass=ts*(ts/K)**(2*P)/(2*P+1)+2*T*(Dtime/(2*T))**2048/2047
    off=4*((gap+arb(1)/2)*nenergy+vprime*one**2/(4*arb(2).log()**2))+mass*one**2
    return ds,L,rad,off


if __name__=="__main__":
    ctx.prec=144
    for N in (10**14,10**15,3*10**15,5*10**15,10**16,15*10**15):
        d,L,r,O=test(N)
        print(N,"complement cutoff",d,"lcm",L.str(8),"effective gap",r.str(8),"off",O.str(12),flush=True)
