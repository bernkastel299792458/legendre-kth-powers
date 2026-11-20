"""Strip Poisson averaging after an analytic rotation about each target point."""
from functools import lru_cache
from math import comb
from flint import arb,ctx


@lru_cache(maxsize=16)
def circular_constants(J,precision,signed=False):
    assert 1<=J<=8 and precision==ctx.prec
    if signed=='pad':assert J in (1,2,4,8)
    eps=arb('2e-6');nangle=384
    cos=[(arb.pi()*j/nangle).cos() for j in range(nangle+1)]
    a=[arb(comb(J,k))*(-arb(1)/J)**k for k in range(J+1)]
    coef=[v+w for v,w in zip(a+[arb(0)],[arb(0)]+a,strict=True)]
    assert coef[0]==1 and coef[1].contains(0)
    assert all(abs(v)<=comb(J+1,k) for k,v in enumerate(coef)) and J+1<=9
    right=sum(abs(c)*arb(4)**(2-j) for j,c in enumerate(coef[2:],2))
    assert right/16<arb(1)/2 and right/(1-right/16)<2
    ps=(arb(4)/3,arb(2));step=arb(2).log()/32
    cap=[arb(0),arb(0)]
    for k in range(-128,129):
        r=(k*step).exp();s=r/J
        # log |(1+z)(1-z/J)^J| is concave in x=cos(arg z).
        peak=-(1-arb(1)/J)*r/2
        pad=sum(abs(c)*r**j*((1+eps)**j-1) for j,c in enumerate(coef[2:],2))
        av=arb(0)
        for hi,lo in zip(cos,cos[1:]):
            x=peak.max(lo).min(hi)
            mag=((1+2*r*x+r*r)*(1-2*s*x+s*s)**J).max(0).sqrt()
            av+=(mag+pad).log() if signed else (mag+pad).max(1).log()
        av/=nangle
        if signed=='pad':av-=r.max(1).log()+J*(r/J).max(1).log()
        for i,p in enumerate(ps):cap[i]=cap[i].max(av/r**p)
    r=arb(1)/16
    tail=sum(abs(c)*(1+eps)**j*r**(j-2) for j,c in enumerate(coef[3:],3))
    all2=sum(abs(c)*(1+eps)**j*r**(j-2) for j,c in enumerate(coef[2:],2))
    small=abs(coef[2])*(1/arb.pi()+(1+eps)**2-1)+tail+r*r*all2**2/2
    if signed:
        small=sum(abs(c)*r**(j-2)*((1+eps)**j-1) for j,c in enumerate(coef[2:],2))/(1-r)**2
    large=sum(abs(c)*(16*(1+eps))**j for j,c in enumerate(coef)).log()
    if signed=='pad':
        p16=sum(abs(c)*arb(16)**j*((1+eps)**j-1) for j,c in enumerate(coef[2:],2))
        l16=(p16/(15*(arb(16)/J-1)**J)).log1p()
    for i,p in enumerate(ps):
        assert p*large>J+1
        cap[i]=(cap[i]*(1+(p*step)**2*(p*step).exp()/8)).max(small*r**(2-p)).max((l16 if signed=='pad' else large)/16**p)
    return tuple(cap)


def wrapped(gap,span,mass,rate):
    z=(-gap*rate).exp()
    return 1+2*z/(mass*(1-z)*(1-(-2*span*rate).exp()))


def logprice(ell,r,ll,lr,a,J=8):
    p=arb(4)/3;q=arb(2)
    span=r-ell;A=a-ell;B=r-a;t=B/span
    assert A>0 and B>0
    cp,cq=circular_constants(J,ctx.prec)
    rate=((p*cp/(q*cq)).log()+ll-lr)/(p*A+q*B)
    assert rate>0
    l=t*cp*(ll-p*A*rate).exp()*wrapped(A,span,t,rate)
    v=(1-t)*cq*(lr+q*B*rate).exp()*wrapped(B,span,1-t,rate)
    return (l+v)/(2*arb.pi()),rate


def price(U,ell,delta,left,right,a,J=8):
    return logprice(ell,1+delta/U,(left*U.exp()*U**2).log(),(right*U).log(),a,J)


if __name__=='__main__':
    from complete_green import kernel,radial,radial_table
    from frozen_green import Book
    from pathlib import Path
    ctx.prec=150
    for J in (2,4,8):
        c=circular_constants(J,ctx.prec);print('J',J,'circle',*(v.str(11) for v in c),flush=True)
    book=Book(Path(__file__).with_name('phase_shift_extra.json'),'.012,.016')
    U=arb(35);rows=book.row(560);data=next(v for v in rows if v[5]==5 and v[4].overlaps(arb('.484')))
    d,l,r,e,ell,f=data
    for word in ('.80','.85','.865','.874'):
        a=arb(word);nu,P,base,_,_=kernel(U,l,r,d,a,arb(135),ell)
        old=min(base*radial(line,nu) for line in radial_table(ctx.prec))
        val,rate=price(U,ell,d,l,r,a)
        print('a',word,'old',old.str(12),'angular mean',val.str(12),'ratio',(val/old).str(10),'lambda',rate.str(9),flush=True)
        assert val<old
