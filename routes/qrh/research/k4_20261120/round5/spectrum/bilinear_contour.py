"""An all-composite signed detector from the square of the Gaussian tail."""
from pathlib import Path
import sys
from flint import arb, ctx

sys.path.insert(0, str(Path(__file__).resolve().parents[1]/"left"/"large_values"))
from quadratic_contour import row, H, N, Q, D, mean_square, pole_coefficients
from riesz import compact_fraction, short_second


def real_square_floor(h):
    # Jensen on the real part; the least point is min(h,1/2).
    a = h.min(arb(1)/2)
    return 1-2*a+2*a**2-h**2


def compact(s, j, t, width, target, scale, regular, A):
    v = t+width
    u = v.log()
    y = scale*v
    lam = 2*D
    band = (arb('.9')*H).min(v/200)
    far = 6*lam*431/arb.pi()*y**(-(s-arb(1)/2))*((v+1).sqrt()/band+2/band.sqrt())
    residue = y**(-lam)+Q*N*lam*y**(1-s)/arb(H)**2
    p = 3*(1-s)/(3*s-1)
    r = compact_fraction(u,u,j,scale,short_second(u,Q,N),arb(1)/2,True)
    h = (r*(arb(1)/2-arb('1e-4'))**2*7*u*v**p/target).sqrt()+far+residue
    radius = arb(1)/32
    sec = mean_square(s,y,width)
    sup = (1+2*radius/width)*mean_square(s-radius,y,width+2*radius)/(
        arb.pi()*radius*arb(N).log())
    horizontal = regular*sec/(2*arb(N).log())+2*arb('2.55')*A*((4/radius).log()+1)*sup
    P, Pd = pole_coefficients(ctx.prec)
    d1 = abs(Pd+P*(y.log()+arb.const_euler()-1/lam)-1)+y**(-lam)
    d1 += 6*431*15*arb(2).sqrt()/(2*arb.pi()*y.sqrt())
    edges = (horizontal/(2*arb.pi())+d1**2/2+10/(2*arb.pi()*arb(N).log()))/target
    return real_square_floor(h)-edges


def replay():
    ctx.prec = 192
    overall = arb(1)
    scales = (8,32,128,512)
    compact_floor = [arb(1) for _ in scales]
    for k in (1,4,9,17,30,51):
        bounds = []
        for j in (800,820,837,852,865):
            _, critical, edges, _ = row(j,k)
            residual = critical + arb("1e-28")
            s = arb(j)/1000
            t = arb(H)*(arb(k)/4).exp()
            width = t/100
            target = 6*t.log()*t**(3*(1-s)/(3*s-1))
            A = (2*t).log()/2+3
            regular = 3+(2*(2-s)+arb("2.5"))*A
            nearby = (arb("2.5")*(width+4)/(arb(".9")*width)*8*
                      (arb(4).log()**2+2*arb(4).log()+2)).sqrt()*A
            powers = arb(N)**(1-2*s)/((2*s-1)*(1-arb(N)**(-s))**2)
            extra_edges = powers*((regular*(2-s)+nearby)/(2*arb.pi())+
                                   arb(1)/2+1/(2*arb.pi()*arb(N).log()))/target
            allowance = real_square_floor(residual.sqrt())-edges-powers-extra_edges
            for i,scale in enumerate(scales):
                compact_floor[i] = compact_floor[i].min(compact(
                    s,j,t,width,target,scale,regular,A)-powers-extra_edges)
            bounds.append(allowance.str(8))
            overall = overall.min(allowance)
        print("k",k,"allowance",*bounds)
    print("minimum signed bilinear allowance",overall.str(14))
    print("finite Riesz allowances",*[f.str(12) for f in compact_floor])
    assert overall>arb(".83") and compact_floor[0]>arb(".08")


if __name__ == "__main__":
    replay()
