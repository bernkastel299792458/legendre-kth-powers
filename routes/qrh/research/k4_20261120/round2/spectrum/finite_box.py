"""A finite zero-free rectangle sufficient to finish all fourth-power gaps."""
import contextlib
import io
from fractions import Fraction
from flint import arb, ctx
from verify_spectrum import A, check, coefficient, verify
from flat_window import moments


def high_tail(altitude, endpoint="229", u0="55.5", transition="10.75",
              cutoff="-5", shift=".8"):
    L=A(endpoint)
    u=A(altitude)
    U,delta,W,logh=A(u0),A(shift),A(transition),A(cutoff)
    k1,_,k3,l0=moments(U,delta,W,logh,True,True,True)
    ratio=k1/k3
    d=(4*(-L/4).exp()).log1p()
    dmax=(4*(-A("114.992")/4).exp()).log1p()
    check(u>U and dmax<A(".01"),"tail and monotonicity domains")
    a=A(".2")
    def power(p,r):
        check(2-p-r/u>0,"convergent tail")
        return ((p-2)*u+r*u.log()).exp()/(2-p-r/u)
    knots=[arb(i)/1000 for i in range(650,871)]+[A("7/8")]
    jlog=A("15/14").log()
    outer=(11*((logh+W)/2).exp()).log()
    ec=162*(-logh).exp()/(2*arb.pi())+2*(2+(arb(2).log()+9*outer)/jlog)
    edge=ec*power(arb(0),arb(0))+27/jlog*power(arb(0),arb(1))
    total=((knots[0]-1)*L).exp()*power(arb(1),arb(1))
    previous=arb(0)
    for s,t in zip(knots,knots[1:]):
        p=3*(1-s)/(2-s)
        k=3*delta*(2*s-1)/(2-s)**2
        c=3*delta/(2-s)
        nu=2/(2-s)
        check(c+1+c/U<(U*ratio).log(),"correction decreases")
        cd=coefficient((2+4*delta/U)/(2-s+3*delta/U),nu)
        B=cd*l0**nu*k3*ratio**p*(k*(U+(U*ratio).log())/(U+c)).exp()/(2*arb.pi())
        slope=((s-1)*L).exp()*((t-s)*L).expm1()/(t-s)
        check(slope>previous,"positive chord")
        total+=(slope-previous)*(B*power(p,1+p)+edge)
        previous=slope
    return 16*total/(a*(1-a)*d**2)


def verify_box():
    # Different endpoint sizes require different ordinate ranges. Each
    # allowed zero in the positive half-plane costs at most 2 exp(-L/8).
    bands=[(123,"37",40000,"28.7"),(160,"44",500000,"35"),
           (200,"53",200000000,"47"),(229,"57.6",400000000,"55.5")]
    tails={}
    for end,top,count,u in bands:
        tails[end]=high_tail(top) if end==229 else high_tail(top,str(end),u,"9.5","-4",".75")
        print("band upper endpoint",end,"log height",top,"allowed",count,"tail",tails[end].str(14))
    cells=[(Fraction("114.992"),Fraction(115),True)]
    cells.extend((Fraction(i,4),Fraction(i+1,4),True) for i in range(460,492))
    cells.extend([(Fraction(123),Fraction(160),False),(Fraction(160),Fraction(200),False),
                  (Fraction(200),Fraction(229),False)])
    largest=arb(0)
    for lo,hi,clipped in cells:
        with contextlib.redirect_stdout(io.StringIO()):
            restricted=verify(str(lo),"1/4",128,96,"flat-both","28.7","8.5","-4.25",
                              ".88","0" if clipped else "1",".8",str(hi) if clipped else None,".0149")
        end,top,count,_=next(band for band in bands if hi<=band[0])
        rest=tails[end]*(A(".14")*(A(hi)-end)).exp()
        allowance=2*count*(-A(lo)/8).exp()
        total=restricted+rest+allowance
        print(str(lo),str(hi),"restricted",restricted.str(9),"tail",rest.str(7),
              "finite zeros",allowance.str(7),"total",total.str(12))
        check(total<1,"finite rectangle exception budget")
        largest=largest.max(total)
    print("maximum budget across all bands",largest.str(18))


if __name__=="__main__":
    ctx.prec=192
    verify_box()
