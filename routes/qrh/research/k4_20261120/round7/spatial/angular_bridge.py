"""Full physical cost using disjoint multi-harmonic Green source groups."""
import argparse
from pathlib import Path
from flint import arb,ctx
from angular_certificate import certify
from weighted_green import radial,kernel,H,radial_table
from frozen_green import Book
from height_profile import profile_cap
from signed_profile import positive_radius
from grid_target import weights,dot


def cheapest(values):
    ans=values[0]
    for v in values[1:]: ans=ans.min(v)
    return ans


def menu(precision):
    lines=radial_table(precision)
    # Arbitrary admissible single polynomials. Their indices do not enter the proof.
    selected=set()
    for i in range(0,len(lines[0]),4):
        selected.add(min(range(len(lines)), key=lambda j:float(lines[j][i].mid())))
    return [lines[j] for j in sorted(selected)]


def price(nodes,base,geom,rows,U,frequency,lines):
    scale,w,sources,M,modes=geom
    prices=[]
    families=[]
    for row in rows:
        if row[4]==arb(1)/2:families.append([])
        if len(row)==6:assert row[5]==len(families)-1
        families[-1].append(row[:5])
    for family in families:
        edge=family[0][3]
        options=[M*edge for _ in lines]
        for s,wt,cs in zip(nodes,w,sources,strict=True):
            node=[]
            for delta,left,right,_,ell in family:
                if ell<arb(1)/2 and not s>arb(3)/4:continue
                ml=mr=scale*wt
                for m,c in zip(modes,cs,strict=True):
                    nu,p,b,ql,qr=kernel(U,left,right,delta,s,frequency*m,ell)
                    ml+=abs(c)*ql; mr+=abs(c)*qr
                f=b*ml**p*mr**(1-p)
                node.append([f*radial(line,nu) for line in lines])
            options=[v+cheapest(z) for v,z in zip(options,zip(*node,strict=True),strict=True)]
        prices.extend(options)
    return (dot(w,base)-cheapest(prices)).max(0)


def verify(lo,hi,book,spacing=3,count=14,sub=4,nh=16,top=41):
    l,h=arb(lo),arb(hi)
    assert 140<l<h<150 and 1<=spacing<=12 and count>=3
    widest=(4*(-l/4).exp()).log1p()
    narrow=(4*(-h/4).exp()).log1p()
    omega=arb((l+h)/2,(h-l+widest)/2)
    low=min(36,int((arb('.5')/widest).log().lower().floor().unique_fmpz()))
    assert widest*arb(low).exp()<arb('.5') and narrow*arb(top).exp()>192
    (T,counts,nodes,scalar,F,tail),provider=book.spectrum(low,top,nh,sub,2)
    wt=weights([nodes],l)
    sign_radius=positive_radius(); envelope=profile_cap(widest)
    E=[envelope(narrow*t) for t in T]
    assert E[0].contains(1) and narrow*T[0]<arb('.5')
    g=arb(spacing)/1000
    shapes={p:certify(g*omega,count,p,3 if p else 4,weight_step=l*g,details=True)
            for p in (True,False)}
    groups=[]
    for offset in range(spacing):
        last=len(nodes)-2-offset
        indices=[last-(count-1-j)*spacing for j in range(count)]
        assert indices[0]>0 and all(nodes[j+spacing]-nodes[j]==g or
                   abs(nodes[j+spacing]-nodes[j]-g)<arb('1e-40') for j in indices[:-1])
        # Positive-probability LP works up to x=count*t. The final node is
        # at least one full spacing below that certificate's upper boundary.
        assert nodes[indices[0]]+count*g>=nodes[-1] or indices[0]+count*spacing==len(nodes)-1
        assert all(abs(wt[j+1]/wt[indices[0]+1]-w)<arb('1e-39') for j,w in zip(indices,shapes[True][1]))
        groups.append(indices)
    lines=menu(ctx.prec); old=E[-1]*dot(weights(F,l),tail); saved=arb(0)
    for i,(t,cc,rr) in enumerate(zip(T[1:],counts,scalar,strict=True)):
        diff=(E[i]-E[i+1]).max(0)
        if diff.is_zero():continue
        ordinary=wt[0]*cc+dot(wt[1:],rr)
        old+=diff*ordinary
        U=(t+arb('.1')).log()
        choice=shapes[widest*t<sign_radius]
        rows=provider(U)
        if not rows:continue
        for ids in groups:
            part=price([nodes[j] for j in ids],[rr[j] for j in ids],choice,rows,U,omega,lines)
            saved+=diff*wt[ids[0]+1]*part
    eps=4*(-l/4).exp()
    power=(1+eps)**(arb(3)/2)*(h+eps.log1p())**2*(-l/4).exp()/(6*arb(2).log())
    base=2*(old+(-l/2).exp()*arb(H)*arb(H).log())+power*9/8+(-3*l).exp()/(1-(-2*l).exp())
    damp=2*widest*(wt[0]*counts[-1]+dot(wt[1:],scalar[-1]))
    total=base-2*saved+damp
    print('closed physical cell',lo,hi,'ordinary',base.str(13),'multi-source saving',
          (2*saved).str(13),'damping',damp.str(8),'full',total.str(14),flush=True)
    return total


if __name__=='__main__':
    ctx.prec=160
    cli=argparse.ArgumentParser()
    cli.add_argument('--lo',default='143.3');cli.add_argument('--hi',default='143.31')
    default=Path(__file__).resolve().parents[2]/'round8'/'zero_strip'/'phase_shift_norms.json'
    cli.add_argument('--table',default=str(default));cli.add_argument('--spacing',type=int,default=3)
    cli.add_argument('--count',type=int,default=14);cli.add_argument('--nh',type=int,default=16)
    cli.add_argument('--check',action='store_true')
    args=vars(cli.parse_args());check=args.pop('check');args['book']=Book(args.pop('table'))
    v=verify(**args)
    if check:assert v<1
