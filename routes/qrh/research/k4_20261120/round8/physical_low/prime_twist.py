"""Twisted prime row on [H/8,H/4] from the pole and all true zeta zeros."""
from flint import arb,ctx
from actual_split import H

def run(loga,Tlo=None,Thi=None):
    a=arb(loga);A=a.exp();B=2*A;h=arb(H);w=arb("1.1e-11")
    t0=h/8 if Tlo is None else arb(Tlo)
    t1=h/4 if Thi is None else arb(Thi);pi=arb.pi()
    assert 1<t0 and t0<t1 and t1<=h/2 and w<arb(".001")
    # Unit-ordinate count <=12+2 log(|t|+3), by the real log derivative of xi at 2+it.
    C=12+2*(h+5).log()
    zeros=2*C/A.sqrt()*(w*w/8).exp()*(arb(2).log()+2*(1+(2*h+2).log()))
    j0=arb(3000000000000)-t1-2;assert j0>2
    ht=4*(w*w/2-(w*j0)**2/4).exp()*(C*(1+pi.sqrt()/w)+2/h*(2+4/w**2))
    # Vertical line Re(zeta argument)=-1, using the functional equation.
    line=2/A**2*(2*w*w).exp()/(2*pi)*((10+(h+3).log())*(2*pi).sqrt()/w+2/((h+3)*w*w))
    pole=2/t0
    uns=2*(2*(2*B).log()*((w*w/2).exp()*w+2/A) +
         (-(arb(2).log()/w)**2/4).exp()*(2+2*B*pi.sqrt()*w*(w*w).exp()))
    power=B.log()/A*(B.sqrt()+B**(arb(1)/3)*B.log()/arb(2).log())
    mag=(zeros+ht+line+pole+uns+power)/a
    return mag,(t1-t0)*mag**2,zeros/a,uns/a,ht/a

def square_cost():
    from actual_split import constants
    from row_calibration import run as cal
    z=constants(1732099)[0];D=arb(int((z/11).floor().unique_fmpz()))
    _,energy,_,_,_=run(D.log())
    rho=D/(D-1)
    # prime diagonal is absent for squarefree lcms; remove it in absolute value.
    diagonal=arb(H)/8*rho**2/D
    return cal()[1]*(rho**2*energy+diagonal)

if __name__=="__main__":
    import argparse
    ap=argparse.ArgumentParser(description=__doc__);ap.add_argument("--loga",default="55");ap.add_argument("--upper")
    ap.add_argument("--square",action="store_true");a=ap.parse_args();ctx.prec=144;v=run(a.loga)
    print("uniform prime |row|, unnormalized t-band energy, finite zeros, unsmoothing, high zeros",*(q.str(15) for q in v))
    if a.upper:assert v[1]<arb(a.upper)
    if a.square:print("physical normalized ordinary Mellin I, true balanced semiprimes",square_cost().str(15))
