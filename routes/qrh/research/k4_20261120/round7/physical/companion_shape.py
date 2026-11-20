"""Validated positive lobes of an integral-preserving combination of Logan kernels."""
from math import factorial
from flint import arb


def cin(x):
    """Entire even integral of (1-cos(t))/t from zero to x."""
    if abs(x)<1:
        value=arb(0)
        for n in range(12,0,-1):
            value=(value+arb((-1)**(n+1))/(2*n*factorial(2*n)))*x*x
        return value+arb(0,(abs(x).upper()**26/factorial(26)).upper())
    v=abs(x)
    assert v>0
    return arb.const_euler()+v.log()-v.ci()


def at_pole(u,b,cosine,sine):
    # The removable numerator divided by u-b is integral_0^1 sin(b+t(u-b))dt.
    z=u-b
    assert abs(z)<2
    ds=(sine,cosine,-sine,-cosine)
    jet=[]
    for k in range(3):
        v=arb(0)
        for j in range(15,-1,-1):
            v=v*z+ds[(k+j)%4]/(factorial(j)*(1+j+k))
        err=abs(z).upper()**16/factorial(16)
        jet.append(v+arb(0,err.upper()))
    inv=1/(u+b)
    v=inv*jet[0]
    d=inv*(jet[1]-v)
    return v,d,inv*(jet[2]-2*d)


class Shape:
    def __init__(self,a,count,weight,first=1,both=False,decay=0,plus_share='.5',weights=None):
        assert 0<a<arb.pi() and count>=1 and first>=1 and decay in (0,1,2,3)
        self.a=a
        tags=[(i,sgn,2*arb.pi()*i+sgn*a) for i in range(first,first+count)
              for sgn in ((-1,1) if both else (-1,))]
        share=arb(plus_share)
        assert 0<share<1
        raw=[arb(first+count-i)**decay*((share if sgn>0 else 1-share) if both else 1) for i,sgn,_ in tags]
        norm=sum(raw,arb(0))
        self.coefficients=[arb(weight)*x/norm for x in raw]
        if weights:
            prescribed=[]
            for term in weights.split(','):
                label,amount=term.split('/')
                j=int(label[:-1]);assert j>=1 and label[-1] in '+-'
                prescribed.append((j,1 if label[-1]=='+' else -1,arb(amount)))
            prescribed.sort(key=lambda row:(row[0],row[1]))
            assert len({(j,s) for j,s,_ in prescribed})==len(prescribed)
            tags=[(j,s,2*arb.pi()*j+s*a) for j,s,e in prescribed]
            self.coefficients=[e for j,s,e in prescribed]
        self.bs=[b for _,_,b in tags]
        assert all(e>0 or e<0 for e in self.coefficients)
        self.signed=any(e<0 for e in self.coefficients)
        self.mass=sum((abs(e) for e in self.coefficients),arb(0))
        self.c=1+a*sum((sgn*e/b for (_,sgn,b),e in zip(tags,self.coefficients,strict=True)),arb(0))
        self.r=self.c-sum(self.coefficients,arb(0))
        assert 0<self.r<1 and self.c>0
        self.co,self.si=a.cos(),a.sin()
        self.terms=[(self.c,a,a*a,self.si)]+[(-e,b,b*b,sgn*self.si)
                    for (_,sgn,b),e in zip(tags,self.coefficients,strict=True)]
        self.moved={}
        residue=sum((abs(e)*(b*b-a*a) for b,e in zip(self.bs,self.coefficients,strict=True)),arb(0))
        if self.signed:
            bounds=[a]+self.bs+[(self.bs[-1]**2+2*residue/self.r).sqrt()]
            roots=[]
            for j,(l,h) in enumerate(zip(bounds,bounds[1:])):
                pad=(h-l)/2**55
                left=l+(pad if j else 0);right=h-(pad if j+2<len(bounds) else 0)
                points=[left+(right-left)*i/32 for i in range(33)]
                vals=[self.ratio(u) for u in points]
                for lo,hi,v,w in zip(points,points[1:],vals,vals[1:]):
                    if not (v*w<0):continue
                    order=1 if v<0 else -1
                    for _ in range(72):
                        mid=(lo+hi)/2;test=order*self.ratio(mid)
                        if test>0:hi=mid
                        elif test<0:lo=mid
                        else:break
                    assert hi-lo<arb('1e-18')
                    roots.append(lo.union(hi))
            # Clearing the distinct simple poles gives a polynomial of exact
            # degree len(tags) in u^2, since r>0. These separated sign
            # brackets must account for every root, including multiplicity.
            assert len(roots)==len(tags) and all(v<w for v,w in zip(roots,roots[1:]))
            self.moved={(j,s):v for (j,s,b),v in zip(tags,roots,strict=True)}
        for index,(j,sgn,b) in enumerate([] if self.signed else tags):
            lo=b
            if index+1<len(tags):
                next_pole=self.bs[index+1]
                hi=next_pole-(next_pole-b)/2**32
            else:
                hi=(b*b+2*residue/self.r).sqrt()
            assert self.ratio(hi)>0
            for _ in range(72):
                mid=(lo+hi)/2
                test=self.ratio(mid)
                if test>0:hi=mid
                elif test<0:lo=mid
                else:break
            assert hi-lo<arb('1e-18')
            self.moved[j,sgn]=lo.union(hi)
        self.zeros=[]

    def set_lobes(self,last):
        roots=[self.moved.get((i,sgn),2*arb.pi()*i+sgn*self.a)
               for i in range(1,last+2) for sgn in (-1,1)
               if i<=last or sgn==-1]
        roots.sort(key=lambda t:float(t.mid()))
        assert all(x<y for x,y in zip([self.a]+roots[:-1],roots,strict=True))
        assert all(j<=last and v<roots[-1] for (j,_),v in self.moved.items())
        self.zeros=roots
        cutoff=roots[-1]
        self.tail_ratio=self.r+sum(((-e)*(b*b-self.a**2)/(cutoff**2-b*b)
                                    for e,b in zip(self.coefficients,self.bs,strict=True) if e<0),arb(0))
        assert self.tail_ratio>0

    def ratio(self,u):
        x=u*u
        return self.c-(x-self.a**2)*sum((e/(x-b*b) for b,e in zip(self.bs,self.coefficients,strict=True)),arb(0))

    def jets(self,u):
        x=u*u; sn=u.sin();cs=u.cos();num=self.co-cs
        t0=t1=t2=arb(0);v=d=d2=arb(0)
        for coef,b,square,sine in self.terms:
            if abs(u-b)<1:
                s,ds,dds=at_pole(u,b,self.co,sine)
                v+=coef*s;d+=coef*ds;d2+=coef*dds
            else:
                den=x-square
                assert not den.contains(0)
                inv=1/den;z=coef*inv
                t0+=z;t1+=z*inv;t2+=z*inv*inv
        return (v+num*t0,d+sn*t0-2*u*num*t1,
                d2+cs*t0-(4*u*sn+2*num)*t1+8*x*num*t2)

    def primitive(self,u):
        out=arb(0)
        for coef,b,_,sine in self.terms:
            x=u-b;y=u+b
            out+=coef*(self.co*(cin(x)-cin(y))+sine*(x.si()+y.si()))/(2*b)
        return out

    def peak(self,left,right):
        lo,hi=left,right
        for _ in range(52):
            m=(lo+hi)/2
            d=self.jets(m)[1]
            if d>0:lo=m
            elif d<0:hi=m
            else:break
        upper=self.jets((lo+hi)/2)[0]+(hi-lo)*(self.c+self.mass)/12
        return upper.upper()

    def lobe(self,j,K,panels):
        a=self.a
        left=self.zeros[2*j-1] if j else a
        right=self.zeros[2*j]
        step=(right-left)/panels
        area=self.primitive(right)-self.primitive(left)
        assert area>0
        osc=arb(0)
        for i in range(panels):
            lo=left+step*i;hi=lo+step
            M=abs(self.jets(lo.union(hi))[2]).upper()
            osc+=step*M
        boundary=abs(self.jets(left)[1])+abs(self.jets(right)[1])
        if j==0:
            cap=self.jets(left)[0]
            return area,cap,boundary+osc+cap/K
        cap=self.peak(left,right)
        return area,cap,(boundary+osc+2*cap/K)/2

    def spectral_ratio(self,xmax,panels=256):
        # sinc() uses sin(t)/t, including its entire continuation at zero.
        high=arb(0)
        for i in range(panels):
            x=(xmax*i/panels).union(xmax*(i+1)/panels)
            ratio=self.c-sum((e*(b*x).sinc() for b,e in zip(self.bs,self.coefficients,strict=True)),arb(0))/(self.a*x).sinc()
            high=high.max(abs(ratio).upper())
        return high
