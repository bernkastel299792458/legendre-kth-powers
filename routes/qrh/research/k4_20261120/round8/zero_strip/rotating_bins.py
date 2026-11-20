"""Joint radius bounds for the angular mean and the resonant Fourier coefficients."""
from functools import lru_cache
from math import comb,floor
import numpy as np
from flint import arb,ctx
from rotating import circular_constants
from rotating_signed import signed_constants
from rotating_harmonics import attenuation,series

W=2**24
Z=2**28


def up(z,k):
    return int((z*k).upper().ceil().unique_fmpz())


@lru_cache(maxsize=2)
def bases(J,prec):
    assert J==8 and prec==ctx.prec
    ends=[arb(v)/8 for v in (0,4,6,8,9,10,11,12,13,14,16,18,20,24,32,48,64,80,96,128)]
    eps=arb('2e-6');poly=[arb(comb(J,k))*(-arb(1)/J)**k for k in range(J+1)]
    coef=[u+v for u,v in zip(poly+[arb(0)],[arb(0)]+poly,strict=True)]
    err=[abs(c)*((1+eps)**k-1) for k,c in enumerate(coef)]
    output=[]
    for p,pad in zip((arb(4)/3,arb(2)),circular_constants(J,ctx.prec,'pad'),strict=True):
        assert pad<arb('.1')
        rows=[]
        for lo,hi in zip(ends,ends[1:]+[None],strict=True):
            def clip(z):
                z=z.max(lo)
                return z.min(hi) if hi is not None else z
            def primary(z):
                if z.is_zero():return arb(0)
                return (z.max(1).log()+J*(z/J).max(1).log())/z**p
            m0=primary(lo)
            if hi is not None:m0=m0.max(primary(hi))
            # For 1<r<J there is one stationary point of log(r)/r^p;
            # for r>J apply the same derivative to (J+1)log(r)-Jlog J.
            m0=m0.max(primary(clip((1/p).exp()))).max(primary(clip((1/p+J*arb(J).log()/(J+1)).exp())))
            e=pad
            if hi is None:
                lmin=(lo-1)*(lo/J-1)**J
                e=e.min((sum(c*lo**k for k,c in enumerate(err))/lmin).log1p()/lo**p)
            elif not (lo<=1<=hi or lo<=J<=hi):
                away=abs(lo-1).min(abs(hi-1))*abs(1-lo/J).min(abs(1-hi/J))**J
                e=e.min(sum(err[k]*hi**(k-p) for k in range(2,len(err)))/away)
            row=[up(m0+e,W)]
            for j in range(1,129):
                def at(r):
                    if r.is_zero():
                        return abs(arb((-1)**(j-1))-arb(J)**(1-j))/(2*j) if j==2 and p==2 else arb(0)
                    a=r.min(1/r);b=(r/J).min(J/r)
                    return abs((-1)**(j-1)*a**j-J*b**j)/(2*j*r**p)
                v=at(lo)
                if hi is not None:v=v.max(at(hi))
                if j==1:v=v.max(at(clip(((p+1)/(p-1)).sqrt())))
                row.append(up(v+e,W))
            row.append(W);rows.append(row)
        out=np.array(rows,dtype=np.int64)
        assert out.min()>=0 and out.max()<=2*W
        output.append(out)
    return output


def folded(basis,rate,d,span,mass,omega,modes):
    cols=np.zeros((130,len(modes)+1),dtype=np.int64);cols[0,0]=Z
    for j in range(1,5):cols[j,0]=up(2*attenuation(j*rate,d,span,mass),Z)
    cols[-1,0]=up(2*series(5*rate,rate,d,span,mass),Z)
    for i,m in enumerate(modes,1):
        f=m*omega;j0=floor(float(f/rate));lo=max(1,j0-3);hi=max(3,j0+4)
        assert hi<=128
        cols[0,i]=up(attenuation(f,d,span,mass),Z)
        for j in range(lo,hi+1):cols[j,i]=up(attenuation(f-j*rate,d,span,mass),Z)
        tail=series(f+rate,rate,d,span,mass)+series((hi+1)*rate-f,rate,d,span,mass)
        if lo>1:tail+=series(f-(lo-1)*rate,rate,d,span,mass)
        cols[-1,i]=up(tail,Z)
    assert cols.min()>=0 and int(cols.sum(axis=0).max())*int(basis.max())+Z<2**63
    return (basis@cols+Z-1)//Z


def components(V,ell,r,ll,lr,a,omega,modes,J=8,offset=0):
    A=a-ell;B=r-a;span=r-ell;t=B/span;p=arb(4)/3;q=arb(2);pi=arb.pi()
    assert V>=25 and arb('.4')<=ell<=arb('.5') and 1<r<arb('1.5') and 0<t<1
    cp,cq=signed_constants(J)
    rate=((p*cp/(q*cq)).log()+ll-lr)/(p*A+q*B)+offset
    assert rate>0 and (1+(1+1/(r-1))**2).log()+B*rate<4*V
    bl,br=bases(J,ctx.prec)
    vl=folded(bl,rate,A,span,t,omega,modes);vr=folded(br,rate,B,span,1-t,omega,modes)
    e=(-pi).exp()
    extra=((J+1)*(4*V+2)+20)*span/pi*(1+4*e*(pi+1)/(pi*(1-e))**2)
    return vl,vr,t*(ll-p*A*rate).exp()/(2*pi),(1-t)*(lr+q*B*rate).exp()/(2*pi),extra


def cost(prepared,weight):
    l,r,fl,fr,extra=prepared;mass=sum(weight,arb(0)).upper()
    if mass.is_zero():return arb(0)
    v=np.array([up(w/mass,2**28) for w in weight],dtype=np.int64)
    assert min(v)>=0 and int(v.sum())*max(int(l.max()),int(r.max()))<2**63
    return mass*((int((l@v).max())*fl+int((r@v).max())*fr)/(W*2**28)+extra)


def epigraph(A,rhs,price,source_scale,dmat,modes,rows,normal):
    from scipy.sparse import csr_matrix,lil_matrix,hstack,vstack
    N=len(rows);n=N-1;old=A.shape[1];M=len(modes);wide=old+N*(M+2)
    count=sum(2*M+len(vl)+len(vr) for vl,vr,_,_,_ in rows)
    add=lil_matrix((count,wide),dtype=float);out=np.zeros(wide);out[:old]=price
    out[:N]*=.003
    k=0
    for i,(left,right,fl,fr,extra) in enumerate(rows):
        scale=float(source_scale[i]/normal)
        out[i]+=scale*float(extra)
        for m,harm in enumerate(modes):
            ab=old+m*N+i;out[ab]=scale*float(extra)
            derivative=dmat[harm][i]
            used=np.flatnonzero(derivative)
            p=N+2*n*m
            for sign in (1,-1):
                for j in used:
                    add[k,p+j]=sign*derivative[j];add[k,p+n+j]=-sign*derivative[j]
                add[k,ab]=-1;k+=1
        for edge,(caps,factor) in enumerate(((left,fl),(right,fr))):
            mx=old+(M+edge)*N+i;out[mx]=scale*float(factor)
            for line in caps:
                add[k,i]=line[0]/W
                for m in range(M):add[k,old+m*N+i]=line[m+1]/W
                add[k,mx]=-1;k+=1
    assert k==count
    main=hstack((A,csr_matrix((A.shape[0],wide-old))))
    return vstack((main,add),format='csr'),np.concatenate((rhs,np.zeros(count))),out
