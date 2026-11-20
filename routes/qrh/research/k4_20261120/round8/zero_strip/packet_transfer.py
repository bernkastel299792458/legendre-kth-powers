"""Transfer forced Gaussian cancellation to the old positive strip detector."""
from flint import arb,ctx
from power_packet import run
from strip_boundary import PI,THETA,S,global_phase


def compare(U,v,eta,D,A,lambda0):
    U,v,eta,D,A,lambda0=map(arb,(U,v,eta,D,A,lambda0))
    b=THETA-arb(1)/2
    widths=[arb(i*i)/10000 for i in range(1,49)]
    ny=384
    data=[]
    for n in range(ny):
        l=D*n/ny;r=D*(n+1)/ny
        center=(l+r)/2;radius=(r-l)/2
        row=[]
        for w in widths:
            top=(A*arb(center,radius+w)).cos().upper()
            row.append((1-top).max(0)/(A*(r+w)**2))
        data.append((l,r,row))
    answer=arb(100)
    for j in range(64):
        aj=(THETA-eta)*j/64; bj=(THETA-eta)*(j+1)/64
        mass=[2/PI*((PI*w/(2*b)).sinh()/(PI*bj/(2*b)).sin()).atan() for w in widths]
        increments=[mass[0]]+[mass[i]-mass[i-1] for i in range(1,len(widths))]
        for l,r,row in data:
            boundary=sum(z*w for z,w in zip(row,increments))
            for i in range(8):
                ai=(THETA-S)*i/8; bi=(THETA-S)*(i+1)/8
                philo=(U-(bi+bj)*v*v/2)*l
                phihi=(U-(ai+aj)*v*v/2)*r
                negative=(-arb((philo+phihi)/2,(phihi-philo)/2).cos()).upper()
                if negative<=0:continue
                kprod=(-(ai+aj)*U+v*v*(ai*ai+aj*aj)/2-v*v*l*l/4).exp()
                answer=answer.min(boundary/(kprod*negative))
    return answer*(2-lambda0)/2


if __name__=='__main__':
    ctx.prec=160
    packet=('.75','1','33.66','4.60','2.13',5,'.77')
    gap,cap=run(*packet,'.31967',115886,prime_phases=True)
    ratio=compare('33.66','4.60','.75','1','33.25','.77')
    gain=ratio*gap
    print('extra positive contribution per failing root',gain.str(14),flush=True)
    assert gain>arb('.14401')
    _,V,D=global_phase('33.25')
    print('improved prime-phase deficit and bias',(D+gain).str(14),((D+gain)/V).str(14))
    assert D+gain>arb('7.00219') and (D+gain)/V>arb('.06242')
