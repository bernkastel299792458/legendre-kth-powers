"""All common scales at a fixed nonintegral primitive denominator of the true AFE."""
from math import gcd,prod

import numpy as np
from flint import arb,ctx,fmpz
from quarter_long_row import result as first,mobius
from quarter_integer_ratios import factors
from quarter_negative import geometry
from quarter_signed_block import harmonic
from quarter_diagonal import zq,primes


def discrepancy(q,s):
    P=q*s;den=2**20
    ps=primes(q)
    tr=[[],[]]
    for v in range(P):
        y=2*arb(v)/P
        for target,z in zip(tr,(y.cos_pi(),y.sin_pi()),strict=True):
            target.append(int((den*z).lower().floor().unique_fmpz()))
    co,si=[np.array(z,dtype=np.int64) for z in tr]
    js=np.arange(1,q+1,dtype=np.int64)
    uu=(np.gcd(js,q)==1).astype(np.int64)
    c=np.array([prod(p-1 if k%p==0 else -1 for p in ps) for k in js],dtype=np.int64)
    assert 4*q**3*den<2**63
    cabs=int(np.sum(abs(c)));sumb=int(np.sum(uu))
    cp=arb(0);so=0
    for i,z in enumerate(c,1):
        so+=abs(int(z));cp=cp.max(arb(so)/i)
    rot=[None]+[(arb(k)/s).cos_pi()/(2*(arb(k)/s).sin_pi()) for k in range(1,s)]
    dJ={};dU={};nums={};whole=0;maxJ=0
    for v in range(P//2+1):
        ii=v*js%P;g=gcd(v,P);weight=1 if v==0 or 2*v==P else 2
        nums[g]=nums.get(g,0)+weight
        def cell(seq,mean,norm,absum):
            x=np.cumsum(seq*co[ii]-mean*den,dtype=np.int64)
            y=np.cumsum(seq*si[ii],dtype=np.int64)
            if v%s:
                # The q-block endpoints lie on a regular polygon around C.
                cot=rot[v%s]
                cx=arb(int(x[-1]))/2-cot*int(y[-1]);cy=arb(int(y[-1]))/2+cot*int(x[-1])
                ix=int(cx.lower().floor().unique_fmpz());iy=int(cy.lower().floor().unique_fmpz())
                assert cx-ix<2 and cy-iy<2
                xx=(x-ix)//16384;yy=(y-iy)//16384
                maxcoord=max(abs(int(xx.min())),abs(int(xx.max())),abs(int(yy.min())),abs(int(yy.max())),abs(ix)//16384+1,abs(iy)//16384+1)
                assert maxcoord<2**30
                sq=max(int(np.max(xx*xx+yy*yy)),(ix//16384)**2+(iy//16384)**2)
                rho=16384*arb(sq).sqrt()+23176+2*absum*(1+1/(2*(arb(v%s)/s).sin_pi()))
                out=2*rho/(den*norm)
            else:
                rr=max(0,int(x.max()))-min(0,int(x.min()))
                jj=max(0,int(y.max()))-min(0,int(y.min()))
                out=(arb(rr*rr+jj*jj).sqrt()+4*absum)/(den*norm)
            return int(out.upper().ceil().unique_fmpz())+1
        if gcd(v,q)==1:
            val=cell(c,1 if v%s==0 else 0,1,cabs)
            dJ[g]=dJ.get(g,0)+weight*val
            whole+=weight*val;maxJ=max(maxJ,val)
        mean=int(c[(v//s-1)%q]) if v%s==0 else 0
        val=cell(q*uu,mean,q,q*sumb)
        dU[g]=dU.get(g,0)+weight*val
    def uppers(data):return {g:(b+nums[g]-1)//nums[g] for g,b in data.items()}
    return uppers(dJ),uppers(dU),arb(whole)/P,maxJ,cp,c


def price(s,d0,base,ctxprec):
    q=2310;P=q*s
    assert (s==1 or (fmpz(s).is_prime() and q%s)) and 100000<=d0 and s*d0<2**23
    sg=arb(3)/4;a=arb(1)/2;u=1+a
    U=arb(37);T=U.exp();alpha=arb(64);w=arb('.75');Y=(U-3).exp()
    lo,hi,tc,_,oldout,yf=geometry(q,str(U),str(alpha),str(w),ctxprec)
    eta=arb(int(fmpz(q).euler_phi()))/q;density=eta if s==1 else eta*(1-1/arb(s))
    dj,du,rawmean,rawmax,cp,cs=discrepancy(q,s)
    # Small ratios use the complete u-period mean of the fixed-r function.
    inner=4*arb.pi()/q*(2*rawmean*yf.sqrt()+2*(rawmax*P*rawmean).sqrt())
    W=zq(u,P)/zq(2*u,P)
    cap=s*d0
    sp=factors(cap);mu=mobius(P,cap)
    # Squarefree multiplicative factor (and a separate tail on the smooth mass).
    scaled=2**34
    mw=np.full(cap+1,scaled,dtype=np.int64)
    for p in range(2,cap+1):
        if sp[p]!=p or P%p==0:continue
        val=1/(1+arb(p)**(-u))
        # Every squarefree n<=cap has at most 23 prime factors. Each division is
        # rounded downward to this grid. Use powers of two to avoid integer overflow.
        v=int((val*2**24).lower().floor().unique_fmpz())
        arow=mw[p::p]
        arow[:]=(arow*v)>>24
    assert cap<2**23 and scaled*2**24<2**63
    errgrid=arb(24)*(arb(2)**(-24)+arb(2)**(-34))
    h=time=lat=arb(0)
    for r in np.flatnonzero(mu[s+1:])+s+1:
        r=int(r);v=arb(r);rr=1/v.sqrt();sgn=int(mu[r])*(1 if s==1 else -1)
        low=W*int(mw[r])/scaled
        top=low+W*errgrid
        loss=(v/Y)**a*(1/a+v/Y)
        h+=sgn*(top if sgn>0 else low-loss)*(1/arb(s).sqrt()-rr)/(s*r)
        time+=top*tc*(v*s)**(-sg)
        lat+=top*rr/s*(inner+oldout*(v/s)**a)
    small=h*(hi if h>0 else lo)+time+lat
    # Majorize true M_{qsg} by adjoining s to the first-row smooth divisor.
    # For s^0, s^1, the old lower cutoff is retained. For higher powers use
    # absolute mass (qg)-restricted prefix majorant, weighted over all g.
    # Use the unconditional bound |M_q|<1.000001 and the remaining Euler mass.
    # Constants below are independently established by integer_ratios.complete().
    beta=arb('.008191074') if s==1 else arb('.008191074')*(1+1/arb(s))+arb('1.16')/(s*(s-1))
    ltime=base[2]*W/arb(s)**a
    # Compute the stationary lattice price after averaging over unit r modulo qs.
    N=q*2*T/(2*arb.pi())*s
    bot=arb(cap);cut=2*P;L=(N/bot).sqrt()
    cnt=int(fmpz(P).euler_phi());disc=cnt+2**len(primes(P))
    def series(B,short):
        mean=arb(B)/P
        return 2*mean/arb(cut).sqrt()+2*B/arb(cut)**(arb(3)/2) if short else 2*mean*L.sqrt()+2*B
    def cost(k,dis,b,c):
        y=N/k**2;threshold=c*N/(dis*k)
        t=threshold.min(y).max(bot)
        v=2*dis*(t.sqrt()-bot.sqrt())+2*c*N/k*(1/t.sqrt()-1/y.sqrt())
        v=v.max(arb(0))
        return b*(density*v+disc*dis/bot.sqrt())/arb(k).sqrt()
    out=arb(0);bs=[0,0]
    for k in range(1,cut+1):
        g=gcd(k,P)
        if gcd(k,q)==1:
            dd=dj[g];out+=cost(k,dd,1,cp+1)
            if k<=P:bs[0]+=dd
        dd=du[g];b=abs(int(cs[(k-1)%q]));out+=cost(k,dd,b,2)
        if k<=P:bs[1]+=dd*b
    for B in bs:
        out+=2*density*N.sqrt()*series(B,True)+disc*series(B,False)/bot.sqrt()
    llat=out*4*arb.pi()/q*W/s
    N2=N/s
    pop=4*beta*harmonic((N2/d0).sqrt()/s,q,eta)*(a/(2*eta))*hi/arb(s)**u
    Kr=prod(1+(p-2)*arb(p)**a for p in primes(q))/(q*a)
    Dz=arb('1.01')*T
    scale=(q/(2*arb.pi()))**(-a)*Dz**(1-a)*(1/(1-a)+1/(2048+a-1))
    pop+=4*beta*(hi/(2*arb(s)**u)+Kr*scale/s)
    return h,small,ltime,llat,pop,small+ltime+llat+pop


if __name__=='__main__':
    import argparse
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--denominator',type=int,nargs='+',default=[1,13,17])
    ap.add_argument('--cut',type=int,default=100000)
    args=ap.parse_args();ctx.prec=144
    base=first(args.cut)
    for s in args.denominator:
        out=price(s,args.cut,base,ctx.prec)
        print('primitive denominator',s,'small signed scalar, true head, tail time, averaged lattice, continuous Mobius, whole except remaining nonstationary',
              *(v.str(12) for v in out),flush=True)
