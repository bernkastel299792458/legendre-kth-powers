"""Bilinear fractional-part sums bounded by two separated reciprocal sequences."""
from math import sqrt
from numba import njit


@njit
def reciprocal_sum(gs,lam,zlo,zhi,tlo,thi,lg,nlo,nhi):
    value=0.
    for ga,gb,gw in gs:
        for ha,hb,hw in gs:
            for i in range(len(lam)):
                for j in range(i+1):
                    dl=zlo/(gb*hb*2.**j)
                    el=zlo/(gb*hb*2.**i)
                    di=min(1.,.5+1/dl)
                    ei=min(1.,.5+1/el)
                    q=2.**(i+j)
                    kinv=zhi**2/(nlo*tlo*ga*q)
                    ktop=nhi*thi*gb*q/zlo**2
                    # Continuous sinc majorant in the frequency variable after
                    # Sobolev sampling. Both orientations are usable.
                    spec=(1+4*ktop/dl)*max(kinv,4*(1+1/dl)/el)
                    reverse=(1+4*ktop/el)*max(kinv,4*(1+1/el)/dl)
                    older=di*(1/el+32*nhi*thi*gb**3*hb**2*q*q/zlo**4*ei)
                    older+=4*lg*(kinv+32*ei/dl)
                    upper=min(di*ei,sqrt(di*ei*min(older,1.06*min(spec,reverse))))
                    value+=gw*hw*lam[i]*lam[j]*upper/q*(1 if i==j else 2)
    return value
