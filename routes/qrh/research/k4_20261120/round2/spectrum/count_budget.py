"""Directly test the existing hinge estimates against the finite-box goals."""
from verify_spectrum import A, arb, ctx, coefficient
from flat_window import moments


def density_test(upper, allowed):
    U,delta,W,logh=A(upper),A(".8"),A("8.5"),A("-4.25")
    left,_,right,l0=moments(U,delta,W,logh,True,True,True)
    jlog=A("15/14").log()
    edge=162*(-logh).exp()/(2*arb.pi())
    edge+=2*(2+(arb(2).log()+9*(11*((logh+W)/2).exp()).log())/jlog)+27*U/jlog
    results=[]
    for j in range(700,800):
        s=arb(j)/1000
        nu=(2+4*delta/U)/(2-s+3*delta/U)
        P=(3*(1-s)+3*delta/U)/(2-s+3*delta/U)
        height=U.exp()
        hinge=coefficient(nu,nu)*l0**nu*(height*left*U**2)**P*(right*U)**(1-P)/(2*arb.pi())
        results.append((hinge+edge)/(A(".8")-s))
    optimum=min(results)
    print("log height",upper,"permitted",allowed,"smallest bound on tested grid",optimum.str(15))
    assert optimum>allowed


def first_weighted_box():
    # The true weighted sum is truncated at exp(37). Extending the
    # nonnegative upper bound to infinity gives a simple reproducible test.
    L,E=A("114.992"),arb(123)
    U,delta,W,logh=A("28.7"),A(".88"),A("8.5"),A("-4.25")
    left,_,right,l0=moments(U,delta,W,logh,True,True,True)
    ratio=left/right
    t=(2/((4*(-E/4).exp()).log1p()*A("3/16").sqrt())).log()
    assert t>U and t>arb(3*10**12).log()
    def power(p,r):
        assert p+r/t<2
        return 2*(p*t+r*t.log()).exp()/(2-p-r/t)
    jlog=A("15/14").log()
    edge=162*(-logh).exp()/(2*arb.pi())
    edge+=2*(2+(arb(2).log()+9*(11*((W+logh)/2).exp()).log())/jlog)
    edge+=27/jlog*power(arb(0),arb(1))
    def hinge(s):
        p=3*(1-s)/(2-s)
        k=3*delta*(2*s-1)/(2-s)**2
        c=3*delta/(2-s)
        assert c+1+c/U<(U*ratio).log()
        nu=2/(2-s)
        cd=coefficient((2+4*delta/U)/(2-s+3*delta/U),nu)
        B=cd*l0**nu*right*ratio**p*(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
        return B*power(p,1+p)+edge
    b=A("7/8")
    knots=[arb(j)/1000 for j in range(800,862)]+[b]
    total=((knots[0]-b)*L).exp()*hinge(A(".78"))/(knots[0]-A(".78"))
    previous=arb(0)
    for s,t1 in zip(knots,knots[1:]):
        slope=((s-b)*L).exp()*((t1-s)*L).expm1()/(t1-s)
        assert slope>previous
        total+=(slope-previous)*hinge(s)
        previous=slope
    print("first box weighted expression",total.str(16),"permitted",40000)
    assert total>40000


if __name__=="__main__":
    ctx.prec=192
    for upper,allowed in [("37",40000),("44",500000),("53",200000000),("57.6",400000000)]:
        density_test(upper,allowed)
    first_weighted_box()
