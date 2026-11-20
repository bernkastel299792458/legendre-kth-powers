"""An explicit remainder for the unrestricted scalar AFE saddle."""
from flint import arb,ctx


def remainder(mesh=32,slices=64):
    slope=curv=arb(0)
    for i in range(mesh):
        x=arb(1)/2+arb(2*i+1,1)/(2*mesh)
        g=[arb(0) for k in range(3)]
        v=[arb(0) for k in range(3)]
        for j in range(slices):
            z=arb(2*j+1,1)/(2*slices)
            den=1+z*(x-1)
            for k,c in enumerate((1,-1,2)):
                term=c*z**k/(slices*den**(k+1))
                g[k]+=term
                v[k]+=2*(1-z)*term
        h=v[0].sqrt()
        dh=v[1]/(2*h)
        ddh=v[2]/(2*h)-dh**2/h
        A=h/g[0]
        dA=(dh-A*g[1])/g[0]
        ddA=(ddh-A*g[2]-2*dA*g[1])/g[0]
        slope=slope.max(abs(A*dA))
        curv=curv.max(abs(A**2*ddA+A*dA**2))
    x0=arb(1)/2;x1=arb(3)/2
    l=(2*(x0*x0.log()-x0+1)).sqrt();r=(2*(x1*x1.log()-x1+1)).sqrt()
    return slope,curv,2*slope+(l+r)*curv/2+2/l+2/r+2/abs(x0.log())+2/x1.log()


if __name__=='__main__':
    ctx.prec=160
    values=remainder()
    print('sup |A_v|, |A_vv|, whole scalar saddle error',*(v.upper().str(12) for v in values))
    assert values[-1]<20
