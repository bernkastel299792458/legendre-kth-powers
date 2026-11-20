"""Universal cost floors on just A+B in the first actual finite-density rectangle."""
from flint import arb,ctx


def floor_first(sigma,steps=768):
    H=arb(3000175332800)
    pi=arb.pi()
    W=H*(arb(1)/4).exp()
    delt=W-H
    b=2*sigma-1
    d0=arb("2.8265")*arb("1.9436")*(1+arb(8).log())
    k0=1+(36*W/H).log()
    bottom=None
    for i in range(steps):
        l=b*i/steps
        u=b*(i+1)/steps
        qmax=(b-l)/2
        # D-1 >= (1+u)^-1 X^-u, X<=H/(2pi).
        aa=1/(1+u)
        point=aa*(2*pi/H)**u
        if i:
            j0=(d0*(l/(1+l))**2).min(arb("1.9436")).min(arb("5.5")*l/(1+l))
            bb=j0/u*(2*pi/H)**u*(4*W*k0/(H*delt))
            # V >= (sqrt(aa) X^-u/2 + sqrt(bb) X)^2. Optimize over every X>0.
            p=2/(2+u)
            q=u/(2+u)
            point=point.max(aa**p*bb**q*p**(-2*p)*q**(-2*q))
        val=delt*point.log1p()/(2*pi*qmax)
        bottom=val if bottom is None else bottom.min(val)
    goal=6*W.log()*W**(3*(1-sigma)/(3*sigma-1))
    return bottom,goal


NODES=(800,820,837,850,852,865,874)


def direct_first():
    from finite_points import A,counts,fixed_right
    from critical_mean import critical_mean
    from six_energy import fourth
    from frozen_fourth import frozen_fourth
    H=arb(3000175332800);D=H*(A(".25")).expm1()
    T=H+D;R=D/2;C=H+R;U=R.log()
    # One fixed normalized Jensen rectangle on [H,T].
    B=C+A("1.01")*R
    m=2048;v=A("1.01");p=1+4/B.log()
    ybar=v*m/(m-1)
    assert 4*m/R<1 and ((1+2/R)/v)**m<A(".000001")
    assert 1/(1-(A(".5")+2/R)**m)<1+A(".000001")
    norm=(1+A(".000001"))**2/(1-1/H)
    whole=fourth(B.log())*B*B.log()**4*m/(m-p)*(1+(v*R/C)**(m-p))/2
    fourth_mass=whole.min(frozen_fourth(H,D))
    best={}
    for delta,width,lg,q in [(".55","7","-2.2",210),(".7","7.5","-2.1",210),
                              (".7","8","-2.5",210),(".8","8","-2.5",210),(".7","8.5","-2.9",210),(".8","8.8","-3.1",210),
                              (".9","9","-3.3",210),("1","9","-3.5",210),
                              ("1.1","9","-3.5",210),(".9","9","-3.3",2310)]:
        d,w,h=map(A,(delta,width,lg))
        cm=critical_mean(U,w,h,q=q)
        left=(fourth_mass**A(".25")*(cm*R*U).sqrt()+(ybar*R)**A(".75"))**A("4/3")
        right=fixed_right(U,d,w,h,q)
        Y=R*h.exp()
        a2=2*(Y.log()+2)/Y
        assert (1+a2)**9<arb(3)/2
        edge=D*a2**2/arb.pi()
        outer=11*(q*Y*w.exp()).sqrt()*(T+6)
        for j in NODES:
            sig=A(j)/1000
            n,s,_=counts(sig,U,d,left,right,norm,edge,outer,asymmetric=True)
            if j not in best or n<best[j][0]:best[j]=(n,s,delta,q)
    for j,(n,s,d,q) in best.items():
        sig=A(j)/1000;goal=6*T.log()*T**(3*(1-sig)/(3*sig-1))
        print("direct first box",j,n.str(13),(n/goal).str(12),s.str(6),d,q,flush=True)
    return best

def cumulative_first():
    from finite_points import A,counts,fixed
    H=arb(3000175332800)
    U=H.log()+A(".25")
    best={}
    for delta,w,lg,q in [(".85","8.8","-3.2",210),(".92","9.5","-3.5",210),
                           ("1","9","-3.5",210),("1.1","9","-3.5",210),(".92","9","-3.5",2310)]:
        d=A(delta)
        args=fixed(U,d,w,lg,q,131072)
        for j in NODES:
            sig=A(j)/1000
            n,s,_=counts(sig,U,d,*args)
            if j not in best or n<best[j][0]:best[j]=n,s,delta,q
    return best


if __name__=="__main__":
    ctx.prec=192
    cumulative=cumulative_first()
    local=direct_first()
    for j in NODES:
        n,goal=floor_first(arb(j)/1000)
        both=cumulative[j][0].min(local[j][0])
        print("joint",j,"target",goal.str(12),"cumulative",cumulative[j][0].str(13),
              "centered",local[j][0].str(13),"best ratio",(both/goal).str(10),
              "AFE floor ratio",(n/goal).str(11),flush=True)
