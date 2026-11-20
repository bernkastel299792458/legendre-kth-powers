"""Uniform Mellin mass of a single log taper, with the removable numerator retained."""
from flint import acb,arb,ctx
from taper_profile import research
from mixed_low import _unit_discrepancy
from variance import smooth_values


def continuous(l,u,W,q,refine=2,detail=False,midpoint=False):
    """Upper integral for every e in [l,u]. Subdivide in both real coordinates."""
    _,primes=smooth_values(q,1)
    eta=arb(1)
    lp=[arb(p).log() for p in primes]
    for p in primes:eta*=1-arb(1)/p
    logs=[arb(i).log() for i in range(1,17)]
    sigma=(l/2).union(u/2)
    sc=(l+u)/4
    diff=(u-l)/4
    cap=arb(1) if not l>0 else -(-W*l/2).expm1()/(W*l/2)
    def regular(z):
        # The Euler--Maclaurin remainder here also allows negative Re(z).
        s=1+z
        re=z.real.lower()
        assert re>-1
        val=(-z*logs[-1]).exp()
        for h in logs[:-1]:val+=z*(-s*h).exp()
        val+=z*(-s*logs[-1]).exp()/2
        err=abs(z*s)*(1+abs(2+z)/(2+re))/(12*arb(16)**(2+re))
        return abs(val).lower()-err.upper()
    def denbox(z):
        den=regular(z)
        if abs(z).lower()>arb(".11"):
            den=den.max(abs(z*(1+z).zeta()).lower())
        for hp in lp:
            den*=abs(1-(-(1+z)*hp).exp()).lower().max(arb(0))
        return den
    def middisk(a,b):
        mid=(a+b)/2
        cen=acb(sc,mid)*W
        amp=abs(-(-cen).expm1()/cen)+W*diff/2
        low=denbox(acb(sigma,mid))
        assert low>0
        d=b-a
        R=arb(".0625");best=None
        for _ in range(5):
            lo=l/2-R;hi=u/2+R
            di=denbox(acb(lo.union(hi),(a-R).union(b+R)))
            if di>0:
                whole=((-W*lo).max(arb(0))).exp()/(di*R)
                best=whole if best is None else best.min(whole)
            R/=2
        if best is None:return box(a,b)
        return d*((amp.min(cap)/low)**2+d*d*best**2/12)
    def box(a,b,depth=0):
        z=acb(sigma,a.union(b))
        s=1+z
        den=arb(1)
        for h in lp:den*=abs(1-(-s*h).exp()).lower().max(arb(0))
        az=((l/2)**2+a*a).sqrt()
        if b<=arb(1)/4:
            rr=(-z*logs[-1]).exp()
            for h in logs[:-1]:rr+=z*(-s*h).exp()
            rr+=z*(-s*logs[-1]).exp()/2
            den*=abs(rr).lower()-abs(z*s)*(1+abs(2+z)/2)/(12*16**2)
        else:den*=az*abs(s.zeta()).lower()
        if not den>0:
            assert depth<12
            mid=(a+b)/2
            return box(a,mid,depth+1)+box(mid,b,depth+1)
        mid=(a+b)/2
        center=acb(sc,mid)*W
        avg=abs(-(-center).expm1()/center)
        lip=(diff*diff+((b-a)/2)**2).sqrt()*W/2
        num=cap.min(avg+lip)
        if az>0:
            # |1-r exp(i t)|^2=(1-r)^2+4r sin²(t/2).
            rhi=(-W*l/2).exp()
            rlo=(-W*u/2).exp()
            sn=abs((W*a.union(b)/2).sin()).upper()
            num=num.min(((1-rlo)**2+4*rhi*sn**2).sqrt()/(W*az))
        return (b-a)*(num/den)**2
    vals=[]
    for start,end,scale in [(0,1,512),(1,4,128),(4,12,32),(12,100,16)]:
        scale*=refine if start<1 else 1
        fun=middisk if midpoint and start<1 else box
        vals.append(sum((fun(arb(i)/scale,arb(i+1)/scale) for i in range(start*scale,end*scale)),arb(0)))
    la=arb(100).log()
    vals.append(4*(arb('4.339')/(W*eta))**2*(la**2/3+2*la/9+arb(2)/27)/100**3)
    assert all(v.is_finite() for v in vals)
    if detail:return [a/arb.pi() for a in vals]
    return sum(vals)/arb.pi()


def discrete(U,delta,W,lh,q):
    _,ps=smooth_values(q,1)
    e0=2*delta/U;ly=U+lh
    assert 0<e0<=arb('.1') and ly>16 and W>0
    xi=1-1/(12*arb(10).log())
    eta=zs=zx=arb(1)
    for p in ps:
        eta*=1-arb(1)/p
        zs/=1-arb(p)**(-arb(1)/2)
        zx/=1-arb(p)**(-xi)
    g0=arb(3).sqrt()*(arb(2).sqrt()-1)/2 if 2 in ps else arb(1)
    g1=arb('1.4378')*(1-arb(2)**(-xi)) if 2 in ps else arb(1)
    A=arb('.0336')*g1*arb(2)**e0*zx
    h0=(arb('4.86')*g0+arb('2.93')+arb('5.17')*e0)*zs*arb(2)**e0
    h1=arb('2.83')*e0*zs*arb(2)**e0
    decay=(-W/2).exp()
    c0=(h0*(1+decay)+h1*W*decay)/W
    c1=h1*(1+decay)/W
    b0=1+2/eta
    var=_unit_discrepancy(q)*(b0*b0+2*b0*(1+1/W))
    best=None
    for i in range(32,76):
        alpha=arb(i)/100;S=(1-alpha)*ly;ex=e0-alpha*(1+e0)
        if not (S>arb(15).log() and ex<0):continue
        h=c0+c1*S
        head=(2*A/W*(1/S+1/ly**2).sqrt()+(-S/2).exp()*(h*h+2*c1*h+2*c1**2).sqrt())**2
        c=head+var*(ex*ly).exp()
        best=c if best is None else best.min(c)
    assert best is not None
    return eta,best,ps


def low_rows(U,V,delta,W,lh,q,cells,first,refine=4,causal=False,jordan=False):
    eta,ex,ps=discrete(U,delta,W,lh,q)
    if jordan:
        from jordan_variance import saving
        assert q==2310 and V is not None and 2*delta/V>=arb(".04") and 2*delta/U<=arb(".1") and U+lh>=26
        twice=(2*W).unique_fmpz()
        assert twice is not None and (2*W-int(twice)).is_zero()
        log_y_min=30 if U+lh>=30 else 26
        ex-=saving(str(int(twice)/2),ctx.prec,log_y_min)
        if jordan in ("inner","rough","second") and log_y_min==30:
            from inner_jordan import saving as inner_saving,rough_saving
            ex-=inner_saving(str(int(twice)/2),ctx.prec)
            if jordan in ("rough","second"):ex-=rough_saving(str(int(twice)/2),ctx.prec)
            if jordan=="second":
                from second_jordan import saving as next_coordinate
                ex-=next_coordinate(str(int(twice)/2),ctx.prec)
    e0=2*delta/U
    result=[]
    for i in range(first,cells):
        l=e0*i/cells; u=e0*(i+1)/cells
        if V is not None:l=l.max(2*delta/V)
        if l>u:
            result.append(arb(0))
            continue
        if causal=="real":
            from causal_mellin import continuous as physical
            mass=physical(l,W,q)
        elif causal:
            assert l>0
            mass=continuous(l,l,W,q,refine=2,midpoint=True)
        else:mass=continuous(l,u,W,q,refine)
        C=(1+u*(arb(1)/2+(1+u)/12))/(2*delta)
        for p in ps:C*=1-arb(p)**(-1-u)
        result.append(C*(eta*mass+ex))
    return result


if __name__=="__main__":
    ctx.prec=128
    u=arb(2)/37;l=u*63/64;w=arb('9.5')
    for refine in (1,2,4):
        v=continuous(l,u,w,2310,refine,detail=True)
        print(refine,[float(x) for x in v],float(sum(v)),flush=True)
