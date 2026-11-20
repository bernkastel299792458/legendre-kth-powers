"""Exchange the two finite-interval indicators before averaging the signed logarithm."""
from flint import arb,ctx
from rotating import circular_constants,wrapped


def signed_constants(J):
    cp,cq=circular_constants(J,ctx.prec,True)
    if J==8:
        from jensen_circle import constants
        hp,hq=constants(J,ctx.prec)
        cp=cp.min(hp);cq=cq.min(hq)
    return cp,cq


def signed_logprice(V,ell,r,ll,lr,a,J=8):
    p=arb(4)/3;q=arb(2)
    span=r-ell;A=a-ell;B=r-a;t=B/span
    assert 0<t<1 and V>=25 and ell>=arb('.4') and ell<=arb('.5') and r<arb('1.5')
    cp,cq=signed_constants(J);lp,lq=circular_constants(J,ctx.prec)
    rate=((p*cp/(q*cq)).log()+ll-lr)/(p*A+q*B)
    assert rate>0 and (1+(1+1/(r-1))**2).log()+B*rate<4*V
    dl=wrapped(A,span,t,rate)-1;dr=wrapped(B,span,1-t,rate)-1
    assert dl<1 and dr<1
    l=t*((1-dl)*cp+2*dl*lp)*(ll-p*A*rate).exp()
    v=(1-t)*((1-dr)*cq+2*dr*lq)*(lr+q*B*rate).exp()
    # Q X<=exp(3U), absolute top plus the two half-window widths <=4exp(U).
    # These conditions are checked by callers when using translated windows.
    K=(J+1)*(4*V+2)+20
    x=(-arb.pi()).exp()
    displacement=span*(1+4*x*(arb.pi()+1)/(arb.pi()*(1-x))**2)
    extra=2*K*displacement/(2*arb.pi())
    return (l+v)/(2*arb.pi())+extra,rate,extra


def signed_price(U,ell,delta,left,right,a,J=8,V=None):
    if V is None:V=U
    assert V>=U or V.overlaps(U)
    return signed_logprice(V,ell,1+delta/U,(left*U.exp()*U**2).log(),(right*U).log(),a,J)


if __name__=='__main__':
    from complete_green import kernel,radial,radial_table
    from frozen_green import Book
    from rotating import price
    from pathlib import Path
    ctx.prec=150;U=arb(35)
    d,l,r,e,ell,f=next(v for v in Book(Path(__file__).with_name('phase_shift_extra.json'),'.012,.016').row(560)
                        if v[5]==5 and v[4].overlaps(arb('.484')))
    for s in ('.80','.85','.865','.874'):
        a=arb(s);nu,P,base,_,_=kernel(U,l,r,d,a,arb(135),ell)
        old=min(base*radial(line,nu) for line in radial_table(ctx.prec))
        plus=price(U,ell,d,l,r,a)[0];signed,rate,extra=signed_price(U,ell,d,l,r,a)
        print(s,'signed',signed.str(12),'positive',plus.str(12),'old',old.str(12),
              'ratio',(signed/old).str(9),'displacement',extra.str(8),flush=True)
        assert signed<plus<old
    print('signed circular cap',*(x.str(12) for x in circular_constants(8,ctx.prec,True)),flush=True)
