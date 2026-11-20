"""Joint signed constraints at nine Gaussian cutoff lengths for the cost of one sample."""
from flint import arb,arb_mat,ctx
from gaussian_detector import D,H,N,Q,THETA,phi,fraction,short_second


def gram(scale_indices):
    b2=2*D**2
    return arb_mat([[(-b2*(i-j)**2/4).exp() for j in scale_indices] for i in scale_indices])


def main():
    ctx.prec=192
    grid=list(range(-4,5))
    G=gram(grid);inv=G.inv()
    error_factor=sum(abs(inv[i,j]) for i in range(len(grid)) for j in range(len(grid))).sqrt()
    assert error_factor<10**5
    b=D*arb(2).sqrt()
    assert phi(b*((128*arb(H)).log()-4))>1-arb("1e-40")
    # Every unnormalized residual entry (tail of I, pole and correction to Phi) is < 1e-39.
    assert (4*D).exp()*error_factor*arb("1e-39")<arb("1e-30")
    print("Gram norm for uniform entry error",error_factor.str(12),flush=True)
    for scale in (128,512):
        worst=arb(0)
        for k in range(229,360):
            U,V=arb(k)/8,arb(k+1)/8
            S=short_second(U,Q,N)
            for j in range(800,875):
                c=arb(2*j)/1000-arb(1)/2
                pair=3*(c-THETA)/(2*(c-arb(1)/2))
                adj=((arb(".5")-arb("1e-40"))/(arb(".35")-arb("1e-30")))**2
                worst=worst.max(fraction(U,V,j,scale,S)*pair*adj)
        print("scale",scale,"full joint exceptional fraction of R7",worst.str(12),flush=True)
    print("simultaneous signed caps for ell=-2,-1,0,1,2 at s=.85",
         [(-1+arb(".35")*(-ell*(D if ell<0 else arb(".35"))).exp()).str(9) for ell in (-2,-1,0,1,2)],flush=True)


if __name__=="__main__":
    main()
