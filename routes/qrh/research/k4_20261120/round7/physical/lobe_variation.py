"""Direct interval bound for the endpoint densities in positive exterior lobes."""
from math import factorial
from flint import arb


def sinc_derivatives(t):
    terms=16
    assert abs(t)<4
    x=t*t
    result=[]
    for k in range(3):
        first=(k+1)//2
        value=arb(0)
        for j in range(terms,first-1,-1):
            value=value*x+arb((-1)**j)/((2*j+1)*factorial(2*j-k))
        if 2*first!=k:value*=t
        j=terms+1
        error=2*arb(4)**(2*j-k)/((2*j+1)*factorial(2*j-k))
        result.append(value+arb(0,error.upper()))
    return result


def derivatives(u,a):
    x=sinc_derivatives((u+a)/2)
    y=sinc_derivatives((u-a)/2)
    return (x[1]*y[0]+x[0]*y[1])/4,(x[2]*y[0]+2*x[1]*y[1]+x[0]*y[2])/8


def first(a,width,K,mass,panels=128):
    step=width/panels
    result=abs(derivatives(a,a)[0])+abs(derivatives(a+width,a)[0])+mass/K
    for j in range(panels):
        u=a+step*(2*j+1)/2
        # From the sine integral, |g'''(u)| <= int v^3(1-v) dv=1/20.
        result+=step*(abs(derivatives(u,a)[1])+step/40)
    return result.upper()


def secondary(a,left,width,panels=64):
    step=width/panels
    result=arb(0)
    for i in range(panels):
        u=(left+step*i).union(left+step*(i+1))
        den=u*u-a*a
        top=a.cos()-u.cos()
        val=u.cos()/den-(4*u*u.sin()+2*top)/den**2+8*u*u*top/den**3
        result+=step*abs(val).upper()
    return result.upper()


def twice_moving(a,K,lobes):
    """Boundary and interior constants after a second integration by parts."""
    b=2*(arb.pi()-a)
    if lobes==0:
        first=abs(derivatives(a,a)[0])+abs(derivatives(a+b,a)[0])
        second=abs(derivatives(a,a)[1])+abs(derivatives(a+b,a)[1])+first/K
        second+=b*(arb(1)/20+arb(1)/(4*K)+arb(1)/(3*K**2))
        return first,second
    first=arb(0);second=arb(0)
    for j in range(1,lobes+1):
        left=2*arb.pi()*j+a
        right=left+b
        boundary=a.sin()*(1/(left**2-a**2)+1/(right**2-a**2))
        first+=boundary
        ends=arb(0)
        for u in (left,right):
            den=u*u-a*a
            ends+=abs(u.cos()/den-4*u*u.sin()/den**2)
        total=arb(0)
        for i in range(32):
            u=(left+b*i/32).union(left+b*(i+1)/32)
            den=u*u-a*a
            h=a.cos()-u.cos()
            inv=1/den
            d1=-2*u/den**2
            d2=8*u*u/den**3-2/den**2
            d3=24*u/den**3-48*u**3/den**4
            gp=u.sin()*inv+h*d1
            gpp=u.cos()*inv+2*u.sin()*d1+h*d2
            gppp=-u.sin()*inv+3*u.cos()*d1+3*u.sin()*d2+h*d3
            total+=b/32*(abs(gppp)+3*abs(gpp)/K+2*abs(gp)/K**2).upper()
        second+=ends+boundary/K+total
    return first/2,second/2
