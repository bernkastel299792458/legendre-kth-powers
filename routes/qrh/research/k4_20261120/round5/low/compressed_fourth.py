"""Compressed time window and all-integer Fourier fold in the frozen fourth moment."""
from functools import lru_cache
from flint import arb
from frozen_energy import energy,harmonic_upper
from sieved_fourth import fourth_six
from prefix_fourth import prefix_norm
from center_fold import folded


@lru_cache(maxsize=None)
def coefficient_norms(y):
    d={1:1}
    for p in (2,3,5,7,11,13):
        d.update({p*k:-sg for k,sg in d.items()})
    e=sum(sg*energy(y,k) for k,sg in d.items())
    a,b=harmonic_upper(y)
    assert 0<e and 0<a
    return arb(e),arb(a)/b


def compressed(H,D):
    R=D/2; C=H+R; v=arb("1.01");M=2048
    pi=arb.pi();B=C+v*R;p=1+4/B.log()
    y0=(C/(2*pi)).sqrt(); y=int(y0.floor().unique_fmpz())
    assert 6*y<10**7
    eu,harm=coefficient_norms(y)
    global4=fourth_six(B.log())*B*B.log()**4
    E=(1+1/arb(2).sqrt())*(1+1/arb(3).sqrt())
    best=None
    for val in ("1.003","1.005","1.008","1.012","1.020","1.04","1.10","2"):
        tau=arb(val); J=tau*v*R
        assert C-J>200
        yw=((C-J)/(2*pi)).sqrt();yy=((C+J)/(2*pi)).sqrt()
        er=(1+(y0-yw).max(yy-y0))*J**(arb(1)/4)/yw.sqrt()
        er=er.min(prefix_norm(C,J))
        re=2*E*(er+(J/(C-J))**(arb(1)/4))
        eps=J**(-arb(1)/5)
        assert 4*eps<pi
        cor=((1+eps)*eps*(2*eps**3).exp()).exp()/(1-4*eps/pi)
        norm=cor*((1+eps)*J*harm+pi*eu)
        norm=norm.min(folded(J*harm,eu,J,arb(1),arb(1),pi))
        tail=global4*M/(M-p)*tau**(p-M)
        cost=(2*norm**(arb(1)/4)+re)**4+tail
        best=cost if best is None else best.min(cost)
    return best
