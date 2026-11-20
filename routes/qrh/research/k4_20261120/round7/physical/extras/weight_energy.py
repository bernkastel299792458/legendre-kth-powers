"""Dyadic second moments of the actual Selberg sieve weights on multiples."""
from functools import lru_cache
from fractions import Fraction
from math import gcd,prod,sqrt
from pathlib import Path
import sys
import numpy as np
from numba import njit
from flint import arb,ctx,fmpz
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from bilinear import groups,lambdas,rational,upper,lower

SMALL=(2,3,5,7)
P=prod(SMALL)
R=8
N=2048
QUANT=2**32


@lru_cache(None)
def residue_rows():
    """Densities and all half-open interval discrepancies, exactly."""
    rows=[]
    for m in range(1,P+1):
        if P%m:continue
        period=P*m
        active=[int(gcd(j,P)==m and gcd(j//m if m and j%m==0 else 0,m)==1) for j in range(1,period+1)]
        mass=sum(active)
        ht=lo=count=0
        for n,x in enumerate(active,1):
            lo=min(lo,period*count-n*mass)
            count+=x
            ht=max(ht,period*count-n*mass)
        amp=Fraction(m,prod(k-1 for k in SMALL if m%k==0))**2
        rows.append((m,amp*Fraction(mass,period),amp*Fraction(ht-lo,period)))
    return tuple(rows)


@lru_cache(None)
def quantized():
    return [0]+[(QUANT+int(fmpz(n).euler_phi())-1)//int(fmpz(n).euler_phi())
                if fmpz(n).moebius_mu() else 0 for n in range(1,N+1)]


@lru_cache(maxsize=2048)
def coprime_prefix(k):
    raw=quantized()
    v=np.array([a if gcd(k,n)==1 else 0 for n,a in enumerate(raw)],np.int64)
    return np.cumsum(v)


@lru_cache(None)
def max_ratio(limit):
    n=1
    rs=Fraction(1)
    for p in range(2,300):
        if fmpz(p).is_prime():
            n*=p
            if n>limit:return rs
            rs*=Fraction(p,p-1)
    raise ValueError("insufficient primorial")


def zero_frequency(zlo,zhi,modulus=1):
    """Mean of mu²(n)*sigma(n)/phi(n) via an exact small-prime density."""
    best=None
    for cut in (13,31,53,71,97):
        rho=disc=outer=arb(1)
        for p in range(2,1001):
            if not fmpz(p).is_prime():continue
            if modulus%p==0:
                assert p<=cut
                rho*=1-arb(1)/p
                disc*=2
            elif p<=cut:
                rho*=1+arb(1)/p**2
                disc*=arb(2)*(p+1)/(p-1)
            else:outer*=1+arb(2)/(p*(p-1))
        cand=rho*outer*(arb(2)/1000).exp()+disc*(1+zhi.log())**3/zlo
        best=cand if best is None else best.min(cand)
    return best


def squarefree_groups(trunc):
    gs=groups(trunc)
    m=P**2
    raw=np.ones(m+1,np.int64)
    for p in SMALL:raw[::p**2]=0
    raw[0]=0
    counts=np.cumsum(raw)
    total=int(counts[-1])
    M=m*counts-np.arange(m+1,dtype=np.int64)*total
    D=Fraction(int(max(M)-min(M)),m)
    d=Fraction(total,m)
    for k,(aa,bb,_) in enumerate(gs):
        a,b=int(aa),int(bb)
        if a==b:continue
        old=Fraction(1,a*a)+Fraction(1,a)-Fraction(1,b)
        bound=d*old+D/Fraction(a*a)
        # Intervals appearing after summation by parts have integer endpoints.
        gs[k,2]=upper(rational(min(old,bound)))
    return gs


@lru_cache(None)
def cap(block,piece):
    return ((2**(block+1)*R+R+piece-1)//(R+piece))-1


@lru_cache(None)
def fixed_rows(known,blocks,precision,modulus=1):
    main=[arb(0) for _ in range(blocks)]
    error=[arb(0) for _ in range(blocks)]
    mainw=[arb(0) for _ in range(blocks)]
    errw=[arb(0) for _ in range(blocks)]
    for mask,rho,discrepancy in residue_rows():
        if gcd(mask,known)>1:continue
        prefix=coprime_prefix(mask*known)
        dm=rational(rho)/(2*R)
        de=rational(discrepancy)
        for i in range(blocks):
            for j in range(R):
                a=cap(i,j)
                if a<=N:g=arb(int(prefix[a]))/QUANT
                else:
                    g=arb(a).log()+2+arb('2.44')/arb(a).sqrt()
                    if modulus>1:
                        from odd_sieve import upper_harmonic
                        g=g.min(upper_harmonic(a,modulus,precision))
                main[i]+=dm*g*g
                error[i]+=de*g*g
                weight=(arb(2*R)/(R+j))**2
                mainw[i]+=weight*dm*g*g
                errw[i]+=weight*de*g*g
    return main,error,mainw,errw


def factors(gs,blocks,G,zlo,zhi):
    tail=arb(1)
    for p in range(11,1001):
        if fmpz(p).is_prime():tail*=1+arb(2*p-1)/(p*(p-1)**2)
    tail*=(arb(3)/1000).exp()
    logloss=(1+zhi.log())**3
    lam=lambdas(G,zhi,blocks)
    out=np.empty((len(gs),len(gs),blocks))
    weighted=np.empty_like(out)
    density=np.empty((*out.shape,4))
    for i,(ga,gb,_) in enumerate(gs):
        for j,(ha,hb,_) in enumerate(gs):
            known=(int(ga) if ga==gb else 1)*(int(ha) if ha==hb else 1)
            if not fmpz(known).moebius_mu():
                out[i,j,:]=0.;weighted[i,j,:]=0.;density[i,j,:,:]=0.;continue
            ratio=Fraction(known,int(fmpz(known).euler_phi()))
            unknown=(int(gb) if ga!=gb else 1)*(int(hb) if ha!=hb else 1)
            ratio=min(ratio*max_ratio(unknown),max_ratio(int(gb)*int(hb)))
            norm=(rational(ratio)/G)**2
            main,error,mainw,errw=fixed_rows(known,blocks,ctx.prec)
            for k in range(blocks):
                dim=zlo/(int(gb)*int(hb)*2**k)
                raw=norm*(main[k]*tail+error[k]*logloss/dim)
                trivial=(arb(1)/2+1/dim).min(arb(1))*arb(lam[k])**2
                out[i,j,k]=upper(raw.min(trivial))
                rw=norm*(mainw[k]*tail+errw[k]*logloss/dim)
                weighted[i,j,k]=upper(rw.min(4*trivial))
                density[i,j,k]=(upper(norm*main[k]*tail),upper(norm*error[k]*logloss/dim),
                                upper(norm*mainw[k]*tail),upper(norm*errw[k]*logloss/dim))
    return out,weighted,density


@njit
def paley(K,inv,D,E):
    best=1.06*(1+(K+.25)/D)*max(inv,4/E)
    for b,c in ((.03125,1.001),(.125,1.014),(.5,1.235),(.75,1.627)):
        cand=c*(1+(K+b)/D)*max(inv,1/(b*E))
        best=min(best,cand)
    return best


@njit
def reciprocal_l2(gs,energies,weighted,density,lam,zlo,zhi,tlo,thi,lg,nlo,nhi,coef,group):
    val=0.
    diff=0.
    for a in range(len(gs)):
        ga,gb,gw=gs[a]
        for b in range(len(gs)):
            ha,hb,hw=gs[b]
            for i in range(energies.shape[2]):
                for j in range(i+1):
                    dl=zlo/(gb*hb*2.**j)
                    el=zlo/(gb*hb*2.**i)
                    di=min(1.,.5+1/dl)
                    ei=min(1.,.5+1/el)
                    q=2.**(i+j)
                    kinv=zhi**2/(nlo*tlo*ga*q)
                    ktop=nhi*thi*gb*q/zlo**2
                    spec=paley(ktop,kinv,dl,el)
                    rev=paley(ktop,kinv,el,dl)
                    old=di*(1/el+32*nhi*thi*gb**3*hb**2*q*q/zlo**4*ei)
                    old+=4*lg*(kinv+32*ei/dl)
                    s=min(di*ei,old,spec,rev)
                    v=sqrt(energies[a,b,i]*energies[a,b,j]*s)
                    der=sqrt(weighted[a,b,i]*weighted[a,b,j]*s)*coef*nhi*gb*q
                    vd=min(der,v)
                    if nhi>nlo:
                        gtop=(2*nhi-nlo)*thi*gb*q/zlo**2
                        gi=zhi**2/(tlo*ga*q)
                        sg=paley(gtop,gi,dl,el)
                        sr=paley(gtop,gi,el,dl)
                        ux=energies[a,b,j];uy=energies[a,b,i]
                        wx=weighted[a,b,j];wy=weighted[a,b,i]
                        ai=lam[i]*lam[i];aj=lam[j]*lam[j]
                        ix=density[a,b,j];iy=density[a,b,i]
                        rm=sqrt(min(ux*sg*(uy*group[0]+min(ai*group[1],iy[0]*group[2]+iy[1]*group[3])),
                                    uy*sr*(ux*group[0]+min(aj*group[1],ix[0]*group[2]+ix[1]*group[3]))))
                        ma=sqrt(min(ux*sg*(uy*group[4]+min(ai*group[5],iy[0]*group[6]+iy[1]*group[7])),
                                    uy*sr*(ux*group[4]+min(aj*group[5],ix[0]*group[6]+ix[1]*group[7]))))
                        md=sqrt(min(wx*sg*(wy*group[8]+min(4*ai*group[9],iy[2]*group[10]+iy[3]*group[11])),
                                    wy*sr*(wx*group[8]+min(4*aj*group[9],ix[2]*group[10]+ix[3]*group[11]))))
                        v=min(v,rm)
                        vd=min(vd,ma,md*coef*gb*q*group[12])
                    fac=gw*hw/q*(1 if i==j else 2)
                    val+=fac*v
                    diff+=fac*vd
    return val,diff


@lru_cache(maxsize=8)
def frequency_groups(order,prec):
    result=[]
    tau=np.zeros(order+1,np.int64)
    for r in range(1,order+1):tau[r::r]+=1
    C=np.ones(order+1);D=np.ones(order+1)
    assert order<2**28
    for p in range(2,order+1):
        if tau[p]==2:
            C[p::p]*=1+p/(p-1)
            D[p::p]*=1+p*p/(p-1)
    pad=arb(1)+arb(2)**-40
    n=1
    while n<=order:
        last=min(order,max(n,(5*n)//4))
        sums=[[arb(0) for _ in range(5)] for _ in range(3)]
        for k in range(n,last+1):
            x=arb(k)/(order+1)
            v=arb.pi()*x
            phi=v*(1-x)*v.cot()+x
            mainw=2*phi/(arb.pi()*k)
            rem=arb(2)/(order+1)*(1-x)
            for row,w in zip(sums,(rem,mainw,k*mainw)):
                row[0]+=w;row[1]+=w*w;row[2]+=w*w*int(tau[k])/k
                row[3]+=w*w*arb(float(C[k]))*pad/k
                row[4]+=w*w*arb(float(D[k]))*pad/k
        remainder,main=sums[0][0],sums[1][0]
        assert main>0 and remainder>0
        constants=[upper(y) if y>0 else 0.0 for t,v,z,a,b in sums
                   for y in (v/t**2,(last-n)*z/t**2,(last-n)*a/t**2,(last-n)*b/t**2)]
        constants.append(upper(sums[2][0]/main))
        result.append((n,last,main,remainder,np.array(constants)))
        n=last+1
    return result


def denominator(l,h,ratio,order,blocks=38,location_hi="115.12"):
    c=rational(Fraction(ratio))
    assert c>=1 and order>=32 and 30<=blocks<=40 and 83<=l<h<=89
    trunc=2**32
    zlo=c*(arb(l)/2).exp();zhi=c*(arb(h)/2).exp()
    tlo=arb("114.98").exp();thi=arb(location_hi).exp()
    assert Fraction("115.12")<=Fraction(location_hi)<=116 and zhi<tlo
    shift=arb("1.331")+c.log()
    G=arb(l)/2+shift
    for b,bound in (('.03125','1.001'),('.125','1.014'),('.25','1.06'),('.5','1.235'),('.75','1.627')):
        x=arb(b)*arb.pi()/2
        assert (x/x.sin())**2<arb(bound)
    assert arb("1.33258")-arb("2.44")/zlo.sqrt()>arb("1.331")
    gs=squarefree_groups(trunc)
    assert len(gs)**2*blocks*(blocks+1)//2<2**23
    E,weights,density=factors(gs,blocks,G,zlo,zhi)
    K=zero_frequency(zlo,zhi)
    total=(K/G)**2/(order+1)
    tail=(1+arb(2).zeta())/trunc+2*arb(2).zeta()**2/2**blocks
    lam=lambdas(G,zhi,blocks)
    for n,last,main,remainder,group in frequency_groups(order,ctx.prec):
        raw,diff=reciprocal_l2(gs,E,weights,density,lam,lower(zlo),upper(zhi),lower(tlo),upper(thi),
                               upper(1+zhi.log()),n,last,upper(arb.pi()/c**2),group)
        assert 0<diff<1 and 0<raw<1
        total+=(arb(raw)*(1+arb("1e-7"))+tail)*remainder
        total+=(arb(diff)*(1+arb("1e-7"))+tail)*main
    error=c*c*total
    a=arb(h)/2+shift
    val=2*shift-2*error*a*a/(1+error*a)
    print(l,h,"ratio",ratio,"N",order,"error",error.str(11),"eta",val.str(14),flush=True)
    return val


if __name__=="__main__":
    import argparse
    ctx.prec=160
    cli=argparse.ArgumentParser()
    cli.add_argument('--l',type=int,default=85)
    cli.add_argument('--ratio',default='4')
    cli.add_argument('--order',type=int,default=1024)
    cli.add_argument('--location-hi',default='115.12')
    a=cli.parse_args()
    denominator(a.l,a.l+1,a.ratio,a.order,location_hi=a.location_hi)
