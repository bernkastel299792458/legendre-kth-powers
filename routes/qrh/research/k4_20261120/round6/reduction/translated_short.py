"""Translated short-polynomial mean with arbitrary positive interval midpoint."""
from flint import arb
from short_block import data,short_second
from flint import ctx

def stats(R,C,q,n):
    M=2048
    v=arb("1.01")
    ybar=v*M/(M-1)
    J=v*arb("1.02")*R
    B=C+J
    y=(B/(2*arb.pi())).sqrt()
    yl=((C-J)/(2*arb.pi())).sqrt()
    a,b,h,G,roots,K,L,h2,_,gmax,_=data(q,n,ctx.prec,1)
    assert C-J>200 and y>1 and yl>0
    diagonal=J*(a*(y.log()+arb.const_euler())+b+G/yl)
    off=2*(1+arb(L).log()+B.log()/2)*(arb(K)**2+gmax*y)+8*roots**2*y
    rs=2*roots*(C-J)**(-arb(1)/4)*J.sqrt()
    main=(2*(diagonal+off).sqrt()+rs)**2
    B0=C+v*R
    p=1+1/B0.log()
    remote=short_second(B0.log(),q,n)*B0*B0.log()*M/(M-p)*arb("1.02")**(p-M)
    err=20*(1+roots)*(C+ybar*R+200).sqrt()+82000*(1+roots)
    err=err.min(160*(1+roots)*(C+ybar*R+4)**(arb(1)/4))
    return h,h2,main+remote,err

def left(R,U,h,cm,mass,rows):
    v=arb("1.01");m=2048;bar=v*m/(m-1)
    best=(mass**(arb(1)/4)*(cm*R*U).sqrt()+(bar*R)**(arb(3)/4))**(arb(4)/3)
    for n,(s,s2,moment,error) in rows:
        assert n<R*h.exp() and 11*n<arb(210)/12*v*arb("1.03")*R/arb.pi()
        for k in range(1,26):
            t=arb(k)/25
            take=(2*t*s-t*t*s2)*arb(12)/11*R*v*(1-arb("1.03")**(1-m))
            rest=cm*R*U-take
            short=t*t*moment+(1-2*t)*bar*R+2*t*error
            assert rest>0 and short>0
            val=(mass**(arb(1)/4)*rest.sqrt()+(bar*R)**(arb(1)/4)*short.sqrt())**(arb(4)/3)
            best=best.min(val)
    return best
