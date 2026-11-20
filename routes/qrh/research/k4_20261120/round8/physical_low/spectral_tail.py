"""A complete additive-frequency tail using the true finite Selberg lcm mass."""
from flint import arb,ctx,fmpz
from actual_split import constants,H
from small_selberg import layers

def high(Q,m,kappa,width=".0002"):
    z,c,r,I,A,S,u=constants(1732099);X=(c+2*r).exp();q0=X/m
    kap=arb(kappa);delta=arb(width)*arb(116).exp()/H
    # Degrees kept fixed at 64 in the actual probability convolution.
    s=2*arb.pi()*delta*kap/(64*X);pi=arb.pi()
    assert 0<s<pi
    # sinc decreases through pi.  Beyond pi, its first negative lobe is at most
    # 1/4 on [4,infinity); on [pi,4] use sin(v-pi)<=v-pi.
    R=(s.sin()/s).max(arb(1)/4)
    assert 1-pi/4<arb(1)/4
    eta=arb(int(fmpz(Q).euler_phi()))/Q
    v=eta*2**len(fmpz(Q).factor());mass=(2*r).exp()*A+2*arb(width)*(116-c).exp()*S
    # The pre-convolution physical dilation still has total variation at most 2S.
    mass=mass.min(S*H*(2*r).exp()/(arb.pi()*kap))
    count=layers(Q,q0.log())*q0;harmonic=(1+q0.log())**3
    values=[2*u*mass*v*R**(64-nu)*s**(-nu)*(kap/X*count/(nu-1)+harmonic)
            for nu in range(2,65)]
    best=min(range(len(values)),key=lambda j:float(values[j].upper()))
    return s,R,best+2,values[best]

if __name__=="__main__":
    import argparse
    p=argparse.ArgumentParser(description=__doc__);p.add_argument("--Q",type=int,default=223092870)
    p.add_argument("--cut",type=int,default=200);p.add_argument("--kappa",default="2.8e17")
    p.add_argument("--upper");a=p.parse_args();ctx.prec=144
    s,R,nu,v=high(a.Q,a.cut,a.kappa)
    print("sinc argument, absolute envelope, residual degree, full upper",s.str(12),R.str(12),nu,v.str(15))
    if a.upper:assert v<arb(a.upper)
