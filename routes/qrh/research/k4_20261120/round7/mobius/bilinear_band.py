"""A two-index reciprocal exponential sum with the actual Selberg signs."""
from math import comb,factorial
from flint import arb,ctx
from selberg_band import band


def derivative_norm(delta,kappa,order):
    # Absolute coefficients after differentiation of w^k exp(-jw) times h.
    terms={(0,0):arb(1)}
    for _ in range(order):
        grow={}
        for (j,k),v in terms.items():
            for a,b,w in ((j,k-1,k*v),(j,k,j*v),(j,k+1,v/(4*delta**2)),(j+1,k,kappa*v)):
                if not w.is_zero():grow[a,b]=grow.get((a,b),arb(0))+w
        terms=grow
    mass=2*arb.pi().sqrt()*delta
    out=arb(0)
    for (j,k),v in terms.items():
        # Shifted even Gaussian moment with variance 2 delta^2.
        moment=sum(comb(2*k,2*r)*factorial(2*r)//factorial(r)*
                   delta**(2*r)*(4*j*delta**2)**(2*k-2*r) for r in range(k+1))
        out+=v*(mass*(4*j*j*delta**2).exp()*moment).sqrt()
    return out


def calculate(logx,logk,logt,i,k,m):
    delta=1/(32*arb(2).sqrt())
    kap=arb(logk).exp()
    T=arb(logt).exp()
    X=arb(logx).exp()
    small=arb(1000)
    assert T>small
    U=band(logx,logt,i,k,m,uniform=True)
    mass=2*arb.pi().sqrt()*delta
    variance=1/(8*delta**2)+kap**2*(1-2*(delta**2).exp()+(4*delta**2).exp())
    fourier=(mass*variance.sqrt()).sqrt()
    order=16
    tail=derivative_norm(delta,kap,order)*(T-small)**(arb(1)/2-order)/(arb.pi()*(2*order-1)).sqrt()
    tail+=fourier*(arb(2).sqrt()*delta*small).erfc()
    width=delta*arb(2).sqrt()
    trivial=(2*arb.pi()).sqrt()*width*(width**2/2).exp()+1/X
    result=fourier*U**2+tail*trivial**2
    return result,U,fourier,tail


if __name__=="__main__":
    ctx.prec=160
    ctx.cap=32
    for a,cap in zip(((43,23,27,63,245,20),(55,15,23,59,215,12),
                      (60,23,27,61,245,20),(70,23,27,59,245,20)),
                     (".000147589","1.424e-10","2.211e-10","6.245e-14"),strict=True):
        out=calculate(*a)
        print("two-index normalized bound",a[:3],*(v.str(10) for v in out),flush=True)
        assert out[0]<arb(cap)
