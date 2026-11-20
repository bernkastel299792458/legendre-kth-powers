"""A second explicit formula at multiples of the comparison spacing."""
from flint import arb

from strip_boundary import H,T,PI,fail,profile,global_phase


def geometric():
    # For K >= 80, |D_N| <= |D_K|^2 + .37 K/N, for every N.
    a=1-arb('2.8')**2/(6*80**2)
    c=arb('.37')
    assert 1/(arb('2.8')*a)<c and PI*arb('.1')/(6*a)<c
    n=4096
    for j in range(n):
        l=arb('.1')+arb('2.7')*j/n
        u=arb('.1')+arb('2.7')*(j+1)/n
        # sinc decreases on this entire interval in (0,pi).
        r=(u.sin()/u)**2
        assert ((1-r*r).sqrt()-r*r.acos())/(a*l)<c
    return c


def arch_bound():
    # Upper gamma excess for |t| <= Z, for all Z >= 10^8.
    z=arb(10**8);v=z.sqrt()
    near=((1+(v+1)/z).log()+arb('.001'))/4
    tail=((z+3).log()+(1+v).log()+3)/(2*PI*v)
    assert near+tail<arb('.005')
    assert arb(4002).log()+1<((z+v+1)/2).log()


def compare(a,k,r,min_step,c):
    A=arb(a);K=arb(k)
    assert 20<=A<=60 and K>=80
    _,V,D=global_phase(a)
    E=profile(A,arb(0))-D
    h=arb(1)/8;eta=arb(7)/8
    F=(h*A).exp()
    poles=(1+F)/A+2*eta*(F-1)/(A*h)+eta**2*(F-1-h*A)/(A*h**2)
    upper=10**8+2*K*r*(T-H)/fail
    gamma=(upper/(2*PI)).log()/4+arb('.005')
    B=V/K+(1-1/K)*(gamma+E)+PI**2*poles/(3*K*min_step**2)+c*r*K*V/fail
    gap=D-B
    print('all-step comparison',a,k,r,min_step,'prime cap',B.str(12),
          'signed gap',gap.str(12),'minimum mean displacement',(gap/(A*V)).str(12),
          'required replacements',(gap*fail/(2*V)).str(12))
    return gap/(A*V)


if __name__=='__main__':
    c=geometric()
    arch_bound()
    assert compare(44,650,1,20,c)>arb('.00021')
    assert compare(44,300,6,20,c)>arb('.0001')
    assert compare(42,200,20,20,c)>0
    assert compare(43,164,34,20,c)>arb('.00000371')
