# Independent re-implementation of Bellotti (arXiv:2405.12545v2) Sec. 3-4 / Appendix A constants,
# written from the paper + reading constants.py (not executing it).
import math
from scipy.integrate import quad
PI=math.pi
def nu1(L,Z=5.558691): return 1/(Z*L)
def J(L): return L/6+math.log(L)+math.log(0.618)
def nu2(L):
    j=J(L); return (0.04962-0.0196/(j+1.15))/(j+0.685+0.155*math.log(L))
def nu3(L): return math.log(L)/(21.233*L)
def nu_best(L, Zc=5.558691, ford=True):
    c=[nu1(L,Zc)]
    if ford: c.append(nu2(L))
    c.append(nu3(L))
    return max(c)
def model(L0,L1,s,u,x,v,w, nu_fn=None, d3fix=False, b2override=None, d4scale=1.0,
          zeta_const=66.7, parity=1.0, verbose=False):
    if nu_fn is None:
        nu_fn = (lambda L: nu1(L)) if L0<46.2 else (lambda L: nu2(L))
    L=L0; T=lambda a: math.exp(a*L)
    r=math.sqrt(2)*(1-s)
    b2=r*2*4.7908/4+2*r*math.log(1+1/r)*(4/PI-1)/(1+2*r)+2*r*2.6908+2+64*r*r/(1+2*r)**2
    if b2override is not None: b2=b2override(r)
    lt=L  # log(t+r) ~ L
    b1=(2*math.sqrt(2)*lt/4+32*r*r/(1+2*r)**2*lt-16*r*r/(1+2*r)**2)/L
    tau=v/u
    rza=3.09*(u+v)*(1.301*(1+tau**2)+1.084*(tau+1)-0.116)/((v-u)*(tau-1))
    d3=4/((v-u)**2*L**2)*(1+1.0061*(u*L+1.333+11/math.sqrt(u*L*math.exp(u*L))))/L
    if d3fix: d3*=L**2
    d4=rza*d4scale + d3/(math.exp(math.exp((u+v-x)*L))*L) + d3/L*(2+(x-(u+v))*L)
    d5=1.0061*(w*L+1.333+3.95/math.exp(w*L/2))/(w*L)
    G1=0.632121+quad(lambda y: y**(2-2*s)*math.exp(-y),1,math.inf)[0]
    c2=d5/w*G1*d4
    numb=math.log(1/nu_fn(L1))
    c3=2*d5/w*G1*d4*numb*1.12
    G2=math.sqrt(2*PI)*quad(lambda y: y**(1.5-2*s)*math.exp(-PI*y/2)*math.exp(1/(6*y)),1,math.inf)[0]
    c4=2*d5/w*G2*d4*2.4
    Zf=1/(nu_fn(L0)*L0)
    cf=b1+b2*Zf
    # c5
    pre=math.sqrt(2*PI)*math.exp(1/(6*(2*s-1.5)))*zeta_const
    iJ1=quad(lambda y:(2*y)**(27/164)*math.exp(-PI*y/2)*y**(1-2*s),3,math.inf)[0]
    iJ3=quad(lambda y:(y/3+1)**(27/164)*math.exp(-PI*y/2)*y**(1-2*s),1,math.inf)[0]
    J1=pre*iJ1; J2=1.461*4.05206; J31=pre*iJ3; J32=zeta_const*1.0486*3.62642
    bint=2*J1+J2+(2*J31+J32)*math.exp(27/164*L)
    fb=d4*d5/(2*PI)*math.exp(w*L)/(w*L)*(math.exp(x*(1.5-2*s)*L)+math.exp((u*L-2*math.log(L))*(1.5-2*s)))
    c5=fb*bint
    # c1
    def d1(lX): return 1/PI**2+0.746/lX+0.825/lX**2+0.462/lX**3+9.73*math.exp(-lX/4)/lX**2+0.73*math.exp(-lX/2)/lX**3
    lVW=(v+w)*L
    d21=d1((w+x)*L)*(1/lVW+0.25)   # code evaluates d1 at T^{w+x} (argument-order slip)
    integ=quad(lambda y:(1+y/(0.447*L))**(27/164)*math.exp(-PI*y/2)*y**(-s),1,math.inf)[0]
    I2I3=2*(122.092+math.exp(1/6)*math.sqrt(2*PI)*zeta_const*integ)
    S1=d21*(u+w)**4*math.sqrt(2*PI)*math.exp(1/(6*L))*L**4*math.exp(x*(1-s)*L)/(math.exp(0.447*PI*L/2)*(0.447*L)**(s-0.5))
    SU=d21*I2I3/(2*PI)*(v+w)**4*math.exp(((v+w)/2+x*(0.5-s)+27/164)*L)*L**4
    c1=math.exp(-L*L/math.exp(u*L))-S1-SU
    den=c1*c1-c5
    C=parity*(c2+c3+c4)*cf/den if den>0 else float('inf')
    out=dict(C=C,B=2*x,b1=b1,b2=b2,d3=d3,d4=d4,d5=d5,c1=c1,c2=c2,c3=c3,c4=c4,c5=c5,Z=Zf,cf=cf,F=(c2+c3+c4)/c2*G1/G1)
    return out
rows=[ # L0,L1,alpha0,u,x,v,w, tableC, tableB
 (math.log(3e12),29,0.9927,2.1781287,7.0798370,4.4744028,0.4808273,37341.72,14.160),
 (29,30,0.9927,2.1653098,7.0418787,4.4543359,0.4781452,37564.18,14.084),
 (40,41,0.9907,1.6037571,4.9754347,3.0601163,0.3005496,76267.80,9.951),
 (45,46.2,0.9900,1.4468014,4.4210629,2.6949834,0.2533034,99227.30,8.843),
 (46.2,50,0.9899,1.4190314,4.3167121,2.6279248,0.2455362,104761.04,8.634),
 (50,60,0.9892,1.3227366,3.9675279,2.3928627,0.2159253,128806.85,7.936),
 (60,70,0.9876,1.1443596,3.3303140,1.9746460,0.1634613,194323.75,6.661),
 (70,80,0.9860,1.0275277,2.9044834,1.6974785,0.1318565,278045.07,5.809),
 (80,90,0.9850,0.9414561,2.6078943,1.5092573,0.1103318,370655.73,5.216),
]
if __name__=='__main__':
    for R in rows:
        o=model(*R[:7])
        print(f"L0={R[0]:6.2f}-{R[1]:5.1f} a0={R[2]} C={o['C']:11.2f} (tab {R[7]:11.2f}, ratio {o['C']/R[7]:.4f}) B={o['B']:.3f} d4={o['d4']:.2f} d5/w={o['d5']/R[6]:.2f} c1={o['c1']:.3f} c5={o['c5']:.3f} b1={o['b1']:.3f} b2={o['b2']:.3f} Z={o['Z']:.3f} cf={o['cf']:.2f} (c2+c3+c4)/c2={(o['c2']+o['c3']+o['c4'])/o['c2']:.2f}")
