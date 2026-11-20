"""Short-interval fourth-moment replacement above H with an exact finite Gram sum."""
from flint import arb
from frozen_energy import sieved_energy, harmonic_upper
from sieved_fourth import fourth_six


def frozen_fourth(H,D,use_prefix=True):
    R=D/2
    C=H+R
    v=arb("1.01")
    M=2048
    J=2*v*R
    assert C-J>200 and v*R<C
    pi=arb.pi()
    y0=(C/(2*pi)).sqrt()
    y=int(y0.floor().unique_fmpz())
    ylo=((C-J)/(2*pi)).sqrt()
    yhi=((C+J)/(2*pi)).sqrt()
    # At both endpoints the first index which differs is greater than ylo.
    diff=(yhi-y0).max(y0-ylo)+1
    euler=(1+1/arb(2).sqrt())*(1+1/arb(3).sqrt())
    jroot=J**(arb(1)/4)
    change=jroot*diff/ylo.sqrt()
    if use_prefix:
        from prefix_fourth import prefix_norm
        change=change.min(prefix_norm(C,J))
    err=2*euler*(change+jroot*(C-J)**(-arb(1)/4))
    N=arb(6*y)
    harm=arb(1)
    h=N.log()
    for k in range(128):
        a,b=h*k/128,h*(k+1)/128
        harm+=2*(1+b)*(1+h-a)**2*(b-a+(-a).exp())
    # The pair with max(r,s)=1 contributes H_{6y}^2, not one.
    harm+=(1+h)**2
    if 6*y<10**7:
        hnum,hden=harmonic_upper(y)
        harm=harm.min(arb(hnum)/hden)
    eu=sieved_energy(y)
    hilbert=pi*(1+arb(2)/3*(arb(6)/5).sqrt()).sqrt()
    base=(J+hilbert/2)*harm+hilbert*eu
    local=(2*base**(arb(1)/4)+err)**4
    B=C+v*R
    p=1+4/B.log()
    tail=fourth_six(B.log())*B*B.log()**4*M/(M-p)*2**(p-M)
    assert tail<arb("1e-500")
    return local+tail
