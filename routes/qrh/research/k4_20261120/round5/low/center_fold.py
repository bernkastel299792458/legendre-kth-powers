"""Folded means with independent time slack and a centered Taylor residual."""
from flint import arb


def folded(mass,energy,min_height,ybar,slope,defect):
    """Bound the half mean from T*sum|a|² (mass) and sum n|a|² (energy)."""
    best=None
    for numerator in (1,2,4,8,16,32,64):
        slack=arb(numerator)/100
        w=(4/(arb.pi()*slack*(1+slack)*min_height**2))**(arb(1)/3)
        loss=4/(arb.pi()*w*slack*min_height)
        assert loss<1
        correction=((1+slack)*min_height*w.expm1()**2/2).exp()/(1-loss)
        val=correction*((1+slack)*slope*ybar*mass+defect*energy)
        best=val if best is None else best.min(val)
    return best
