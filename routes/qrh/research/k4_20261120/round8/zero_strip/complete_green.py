"""Cumulative physical phase correction, verified over one closed physical cell."""
from pathlib import Path
import argparse
import json
import sys
from types import FunctionType
from flint import arb,ctx

from weighted_green import research,radial,kernel,amplitude
sys.path.insert(0,str(research/'round7'/'spatial'))
sys.path.insert(0,str(research/'round8'/'critical'))
from height_profile import profile_cap
from signed_profile import caps as sign_caps,positive_radius
from frozen_sweep import cap as fourth_cap
import mellin_bridge as mb
from exact_bridge import H,angular_edge,radial_table,interpolated_point
from grid_target import weights,dot
from strip_boundary import THETA,PI

_spectrum_cache={}
_node_cost={}
_phase_cost={}
_geometry_cache={}
_angular_cache={}
_raw_cache={}
_trig_cache={}
_multi_raw_cache={}


def norm_row(U,V,delta,w,lh,cell,core):
    # The frozen sweep is independently certified throughout the half-line.
    cap=fourth_cap(U)
    def resid(u,ww,hh,mod):
        return mb.source(u,ww,hh,mod,210,12)
    def left(length):
        return mb.normalized_row(U,V,2310,length,w,lh,resid,fourth_fn=lambda _:cap,
                                 sieve_base=210,small_factor=arb(1)/12)[0]
    L=left(core)
    exp=16+int(((U-34)*2/3).lower().floor().unique_fmpz())
    length=2**min(20,max(12,exp))
    if length<core:L=L.min(left(length))
    return L,mb.right(U,V,delta,w,lh,cell,2310,causal='real',cutoff=300,jordan='rough',prime=True)


def hinge_shape(x,a,b,C,freq,eps):
    y=(x-a).max(0)
    B=y+C*(x-b).max(0)
    z=y.min(b-a)
    V=amplitude(C,freq,b-a,z,(x-b).max(0))
    return B,V


def grouping(nodes,step=4,offset=0):
    # Every node appears at most once. Ignore the terminal, analytically zero node.
    pairs=[]
    for start in range(offset,len(nodes)-1-2*step+1,2*step):
        for j in range(step):
            if nodes[start+j]>=arb('.795'):pairs.append((start+j,start+j+step))
    return pairs


def worst_ratio(lo,hi,harm,opposite=0):
    k=1/(1+lo)
    if harm==1:
        if opposite==0:return k
        if not hi<1:return None
        return k.max(opposite/(1-hi))
    if not hi<=arb(1)/3:
        if not hi<1:return None
        k=k.max(1/(8*hi*(1-hi)).sqrt())
    return k


def joint_saving(individual,blocks):
    """Disjoint improvements retain all admissible single-pair savings."""
    by_end={}
    for keys,saving in blocks:
        extra=saving-sum((individual.get(i,arb(0)) for i in keys),arb(0))
        if extra>0:by_end.setdefault(max(keys),[]).append((min(keys),extra))
    endpoints=set(by_end)|{start for entries in by_end.values() for start,_ in entries}
    best={};val=arb(0)
    for i in sorted(endpoints):
        best[i]=val
        for start,extra in by_end.get(i,[]):val=val.max(best[start]+extra)
    return sum(individual.values(),arb(0))+val


def group_constants(nodes,wt,pairs,freq,harm,adaptive=False):
    shape={}
    for ia,ib in pairs:
        a,b=nodes[ia],nodes[ib];gap=b-a
        C=(arb('.80') if harm==1 else arb(1))*wt[ib]/wt[ia]
        if adaptive:
            # C is frozen, and C(1-exp(-2nu h))/(2nu h) decreases in nu.
            x=freq.lower()*gap
            C=(wt[ib]/wt[ia]).min(arb('.97')*2*x/(-(-2*x).expm1()))
        xlow=freq.lower()*gap
        eps=C*(-freq*gap).exp(); mv=-C*(-2*xlow).expm1()/(2*xlow)
        if not eps<=1 or not mv<1:continue
        B,V=hinge_shape(THETA,a,b,C,freq,eps)
        K=worst_ratio(eps.min(V/B),mv,harm)
        shape[ia]=ib,C,eps,1+C+C*(1+(-2*xlow).exp())/2,K,eps.min(V/B),mv
    groups=[]
    for lower in ('.795','.818','.835','.845'):
        for upper in ('.861','.863','.865','.867','.869','.871','.873','.875'):
            keys=[ia for ia in shape if nodes[ia]>=arb(lower) and nodes[shape[ia][0]]<=arb(upper)]
            if len(keys)<2:continue
            indices=sorted({z for i in keys for z in (i,shape[i][0])})
            if any(keys==row[0] for row in groups):continue
            lo=arb(10);hi=arb(0);prev=None
            for ix in indices+[len(nodes)-1]:
                x=nodes[ix];tot=arb(0);val=arb(0)
                for ia in keys:
                    ib,C,eps,*_=shape[ia]
                    if ix<=ia:continue
                    B,V=hinge_shape(x,nodes[ia],nodes[ib],C,freq,eps)
                    tot+=wt[ia]*B
                    val+=wt[ia]*V
                if tot.is_zero():continue
                ratio=val/tot
                hi=hi.max(ratio)
                if ix==len(nodes)-1:
                    lo=lo.min(ratio)
                else:
                    gapx=freq*(x-prev[0]) if prev else freq*(x-nodes[indices[0]])
                    lower_ratio=ratio.min(prev[1]) if prev else ratio
                    lo=lo.min(gapx/gapx.sinh()*lower_ratio)
                prev=x,ratio
            groups.append((keys,lo,hi))
    return shape,groups


def verify(first,last,nh=8,sub=2,hi=42,step=2,halfwidth=4,params=None,cells=96,
           directional=False,all_positive=False,cap_factory=profile_cap,density_height=arb('1.5'),
           save_rows=None,row_override=None,load_rows=None,menus=None,book=None,phase_window=None,pack=None,multi=False,raw_cone=False,raw_abs=False,trig=False,reuse_raw=0,multi_raw=False,observer=None,observe_kind=None,multi_trig=False,coupled=False,free_green=False,extend=0,tight_jump=False,source_floor='.795',more_modes=False,scalar_mix=False,bands=None,reuse_fit=False,shared_radial=False,shared_opt=False,rotate_phase=False,rotate_opt=False):
    assert (observer is None and observe_kind is None) or (callable(observer) and observe_kind in ('positive','absolute'))
    aL,bL=arb(first),arb(last)
    assert (115 if book is not None else 140)<=aL<=bL<=146
    assert density_height>0 and (not directional or cap_factory is profile_cap)
    params=params or '1.16,9,-3;1.1,9.5,-3;1.28,9.5,-2.75'
    S={}
    saved=[]
    frozen={}
    if load_rows:
        info=json.loads(Path(load_rows).read_text(encoding='utf8'))
        assert row_override is None and (info['sub'],info['top_padding'],info['norm_scale'],info['parameter_scale'])==(sub,'.1',10**20,1000)
        for i,d0,w0,h0,l0,r0,e0 in info['rows']:
            frozen[i,d0,w0,h0]=tuple(arb(z)/10**20 for z in (l0,r0,e0))
    def row(x,y,delta,w,lh,core):
        if row_override is not None:return row_override(x,y,delta,w,lh)
        return norm_row(x,y,delta,w,lh,cells,core)
    def provider(U,V,d,w,lh,core,cell,alpha,base,smooth,q):
        upper=(V.exp()+arb('.1')).log()
        key=int((U*sub).lower().ceil().unique_fmpz())
        parms=tuple(int((z*1000).unique_fmpz()) for z in (d,w,lh))
        if load_rows:
            l,r,edge=frozen[(key,*parms)]
        elif upper-U>arb(1)/2:
            middle=(U+V)/2
            l0,r0=row(U,middle,d,w,lh,core)
            l1,r1=row(middle,upper,d,w,lh,core)
            l,r=l0.max(l1),r0.max(r1)
        else:
            l,r=row(U,upper,d,w,lh,core)
        if not load_rows:edge=angular_edge(U,upper,w,lh,q=2310)
        S.setdefault(key,[]).append((d,l,r,edge))
        if save_rows:
            ceil=lambda v:int((v*10**20).upper().ceil().unique_fmpz())
            saved.append([key,int((d*1000).unique_fmpz()),int((w*1000).unique_fmpz()),
                          int((lh*1000).unique_fmpz()),ceil(l),ceil(r),ceil(edge)])
        return l,r
    original=mb.exact.test
    test=FunctionType(original.__code__,dict(original.__globals__,finite_row=provider,cap_table=cap_factory),original.__name__,original.__defaults__)
    # A degenerate physical cell is useful for discovery; the data entry point
    # requires two distinct endpoints, even though it only returns spectral data.
    aux=bL if aL<bL else aL+arb('.000001')
    d0=(4*(-aL/4).exp()).log1p()
    lo=min(36,int((arb('.5')/d0).log().lower().floor().unique_fmpz()))
    if book is not None:lo=max(lo,-(-min(book.rows)//book.sub))
    grid_low=lo
    rotate_phase=rotate_phase or rotate_opt
    if rotate_phase:
        assert book is not None and free_green and lo>=25
        assert ((1+2/arb(lo).exp())/arb('1.01'))**2048<arb('1e-7')
        assert all(arb(2310).log()+w+lh<2*lo for _,w,lh in book.params)
    assert (book is not None or d0*arb(lo).exp()<arb('.5')) and (4*(-bL/4).exp()).log1p()*arb(hi).exp()>192
    cachekey=(str(Path(load_rows).resolve()),lo,hi,params,nh,sub,step,cells,ctx.prec) if load_rows else None
    if book is not None:
        assert not (load_rows or save_rows or row_override)
        (T,counts,nodes,oldrows,F,final),S=book.spectrum(lo,hi,nh,sub,step)
    elif cachekey is not None and cachekey in _spectrum_cache:
        (T,counts,nodes,oldrows,F,final),S=_spectrum_cache[cachekey]
    else:
        T,counts,nodes,oldrows,F,final=test(first,str(float(aux)+1e-7),params,nh,64,step,cells,2**20,'1',sub,210,'centered',2310,
                                        hi=hi,interpolate=True,tight_rows=True,spectrum_data=lambda *x:x)
        if cachekey is not None:_spectrum_cache[cachekey]=((T,counts,nodes,oldrows,F,final),S)
    if save_rows:
        Path(save_rows).write_text(json.dumps(dict(sub=sub,norm_scale=10**20,parameter_scale=1000,
            top_padding='.1',cells=cells,rows=saved)),encoding='utf8')
    weight=weights([nodes],aL)
    wt=weight[1:]; high=THETA
    dw=(4*(-bL/4).exp()).log1p(); dmax=(4*(-aL/4).exp()).log1p()
    cap=cap_factory(dmax)
    E=[cap(dw*t) for t in T]
    # All ordinates through T[1], including those below the first tabulated
    # scale T[0], can be charged the unit cap in the first Abel layer.
    E[0]=arb(1)
    oldbase=E[-1]*dot(weights(F,aL),final); signedbase=oldbase; saving=arb(0)
    if directional:
        signs=sign_caps()
        Epm=[tuple(e.min(x) for x in signs(dw*t)) for t,e in zip(T,E)]
        Epm[0]=signs(arb(0))
    first_zero=positive_radius() if cap_factory is profile_cap else PI
    choices=[(halfwidth,0,False)]
    if menus:
        choices.extend((int(w),int(o),True) for w,o in (x.split(':') for x in menus.split(',')))
    assert all(w>0 and 0<=o<2*w for w,o,_ in choices)
    # Low-pass only below the first possible sign flip; absolute cosine afterwards.
    allrad=radial_table(ctx.prec)
    fixed=phase_window or (first,last)
    fa0,fa1=map(arb,fixed)
    poisson_floor=140 if fa0>=140 else (135 if fa0>=135 else int(fa0.lower().floor().unique_fmpz()))
    assert fa0>=poisson_floor
    if phase_window:
        assert not directional and (fa0<=aL or fa0.overlaps(aL)) and (bL<=fa1 or bL.overlaps(fa1))
        pw=weights([nodes],fa1)[1:]
        assert nodes[-1]-1+2/fa0<0
        for w,o,_ in choices:
            for aidx,bidx in grouping(nodes,w,o):
                for j in (aidx,bidx):
                    # The slope jump integrates L² exp((s-1)L) against the
                    # nonnegative piecewise linear hat on [s_{j-1},s_{j+1}].
                    assert j>0 and nodes[j+1]-1+2/fa0<0
    else:pw=wt
    freq0=arb((fa0+fa1)/2,(fa1-fa0+(4*(-fa0/4).exp()).log1p())/2)
    fixed_key=tuple(fixed) if all(isinstance(v,(str,int)) for v in fixed) else object()
    gkey=(fixed_key,bool(phase_window),step,halfwidth,menus,ctx.prec)
    if gkey not in _geometry_cache:
        _geometry_cache[gkey]=[{n:group_constants(nodes,pw,grouping(nodes,w,o),n*freq0,n,adapt) for n in (1,2)} for w,o,adapt in choices]
    geometry=_geometry_cache[gkey]
    rk=(gkey,raw_cone,raw_abs)
    if (raw_cone or raw_abs) and rk not in _raw_cache:
        from raw_cone import RawCone
        _raw_cache[rk]=(RawCone(nodes,pw,freq0,step) if raw_cone else None,RawCone(nodes,pw,2*freq0,step,True) if raw_abs else None)
    assert extend>=0 and (not extend or free_green)
    source_nodes=nodes+[nodes[-1]+arb(k*step)/2000 for k in range(1,extend+1)]
    trigkey=(gkey,multi_trig,coupled,free_green,extend,tight_jump,source_floor,more_modes,scalar_mix,bands,reuse_fit,shared_radial,shared_opt,rotate_phase,rotate_opt)
    if (trig or multi_trig or coupled or free_green) and trigkey not in _trig_cache:
        from trig_cone import TrigCone
        if len(_trig_cache)>=2:del _trig_cache[next(iter(_trig_cache))]
        if free_green:
            from free_green import FreeGreen,HingeBands
            form=HingeBands if bands else FreeGreen
            _trig_cache[trigkey]={p:form(source_nodes,pw,freq0,step,p,extend,tight_jump,source_floor,more_modes,scalar_mix,reuse_fit,*([bands] if bands else [])) for p in (True,False)}
            for obj in _trig_cache[trigkey].values():
                for group in getattr(obj,'groups',[obj]):
                    group.sharing=shared_radial or shared_opt;group.reopt=shared_opt;group.rotating=rotate_phase;group.optimize_rotation=rotate_opt
        elif coupled:
            from coupled_cone import CoupledCone
            _trig_cache[trigkey]={p:CoupledCone(nodes,pw,freq0,step,p) for p in (True,False)}
        else:_trig_cache[trigkey]={p:TrigCone(nodes,pw,freq0,step,p,multi_trig) for p in (True,False)}
    if multi_raw and gkey not in _multi_raw_cache:
        from multi_raw import MultiRaw
        _multi_raw_cache[gkey]=MultiRaw(nodes,pw,freq0,step)
    if multi:
        assert pack is not None
        from angular_packing import geometry as angular_geometry,candidates as angular_candidates
        if gkey not in _angular_cache:
            _angular_cache[gkey]=angular_geometry(nodes,freq0,fa1 if phase_window else aL,step)
    patterns={}
    if pack:
        from phase_packing import patterns as allocation_patterns,saving as packed_saving,cone
        for ig,scheme in enumerate(geometry):
            for harm,(shape,groups) in scheme.items():patterns[ig,harm]=allocation_patterns(shape,groups,pw)
    for i,(t,cc,rr) in enumerate(zip(T[1:],counts,oldrows)):
        dep=(E[i]-E[i+1]).max(0)
        dp=dm=arb(0)
        if directional:
            dp=(Epm[i][0]-Epm[i+1][0]).max(0)
            dm=(Epm[i][1]-Epm[i+1][1]).max(0)
        big=dp.max(dm)
        if dep.is_zero() and big.is_zero() and observer is None:continue
        original_U=t.log()
        U=(t+arb('.1')).log()
        key=int(((original_U*sub).mid()-arb('1e-13')).floor().unique_fmpz())
        source=S(U) if callable(S) else S[key]
        positive=all_positive or dmax*t<first_zero
        if observer is not None:positive=observe_kind=='positive'
        rowbase=weight[0]*cc+dot(wt,rr)
        oldbase+=dep*rowbase
        if not source:
            signedbase+=big*rowbase
            if observer is not None:observer(i,rowbase)
            continue
        pending=(book or cachekey,gkey,grid_low,hi,sub,nh,i,positive,pack,multi,raw_cone,raw_abs,trig,reuse_raw,multi_raw,multi_trig,coupled,free_green,extend,tight_jump,source_floor,more_modes,scalar_mix,bands,reuse_fit,shared_radial,shared_opt,rotate_phase,rotate_opt)
        reuse_phase=phase_window is not None and (book is not None or cachekey is not None) and not directional
        if reuse_phase and pending in _phase_cost:
            saving+=dep*_phase_cost[pending]
            if observer is not None:observer(i,rowbase-_phase_cost[pending])
            continue
        alpha=dp.min(dm)/big if big>0 else arb(1)
        groupsrc={}
        for j,v in enumerate(source):groupsrc.setdefault(v[5] if len(v)>5 else j,[]).append(j)
        values={};best=arb(0);signedbest=arb(0)
        packed={}
        def offer(pattern,z):
            if z>0:packed[pattern]=packed.get(pattern,arb(0)).max(z)
        def caps_at(j,src,harm):
            key=(j,src)
            if key not in values:
                ck=(book or cachekey,grid_low,hi,sub,nh,step,i,j,src,ctx.prec,multi,poisson_floor,coupled,free_green)
                reuse=(book is not None or cachekey is not None)
                if reuse and ck in _node_cost:values[key]=_node_cost[ck]
                else:
                    bests=None
                    for jsrc in groupsrc[src]:
                        d,l,r,edge,*opts=source[jsrc]
                        # sinh(a t)/sinh(b t) decreases for 0<a<b and t>0.
                        nu,P,base,ql,qr=kernel(U,l,r,d,source_nodes[j],arb(poisson_floor),*opts[:1])
                        if multi:assert ql<arb('1e-7') and qr<arb('1e-7')
                        if coupled or free_green:assert ql<arb('1e-6') and qr<arb('1e-6')
                        base*=(1+ql)**P*(1+qr)**(1-P)
                        if nu*200>355 and j>=len(nodes):
                            from free_green import extended_radial
                            radii=extended_radial(allrad,nu,ctx.prec)
                        else:radii=[radial(line,nu) for line in allrad]
                        vals=[base*val for val in radii]
                        bests=vals if bests is None else [a.min(b) for a,b in zip(bests,vals,strict=True)]
                    values[key]=bests
                    if reuse:_node_cost[ck]=bests
            return values[key]
        for ig,scheme in enumerate(geometry):
          individual={};mixed={};blocks=[];mixblocks=[]
          for harm in ([1,2] if positive or directional else [2]):
            freq=freq0*harm
            shape,groups=scheme[harm]
            comp={}
            for ia,(ib,C,eps,M,K,lo,hi0) in shape.items():
                x,z=nodes[ia],nodes[ib]
                old=rr[ia]+C*rr[ib]
                new=None
                for j,srcs in groupsrc.items():
                    edge=source[srcs[0]][3]
                    for v0,v1 in zip(caps_at(ia,j,harm),caps_at(ib,j,harm),strict=True):
                        raw=v0+C*v1+M*edge
                        new=raw if new is None else new.min(raw)
                left,right=pw[ia]*old,pw[ia]*new
                comp[ia]=left,right
                if (harm==2 or positive) and K is not None:
                    individual[ia]=individual.get(ia,arb(0)).max(left-K*right)
                    if pack:offer(patterns[ig,harm][0][ia],left-K*right)
                other=worst_ratio(lo,hi0,harm,alpha)
                if other is not None:mixed[ia]=mixed.get(ia,arb(0)).max(left-other*right)
            for keys,lo,hi0 in groups:
                gk=worst_ratio(lo,hi0,harm)
                if (harm==2 or positive) and gk is not None:
                    partial=sum((comp[x][0]-gk*comp[x][1] for x in keys),arb(0))
                    blocks.append((keys,partial))
                    if pack:offer(patterns[ig,harm][1][tuple(keys)],partial)
                op=worst_ratio(lo,hi0,harm,alpha)
                if op is not None:mixblocks.append((keys,sum((comp[x][0]-op*comp[x][1] for x in keys),arb(0))))
          best=best.max(joint_saving(individual,blocks))
          signedbest=signedbest.max(joint_saving(mixed,mixblocks))
        if pack:
            if multi:
                for pattern,z in angular_candidates(_angular_cache[gkey],positive,source,groupsrc,caps_at,pw,rr):offer(pattern,z)
            best=best.max(packed_saving(packed,pack))
            if pack=='cone':best=best.max(cone(packed,pw,nodes,rr))
        bucket=int((U*reuse_raw).mid().floor().unique_fmpz()) if reuse_raw else None
        if raw_cone and positive:best=best.max(_raw_cache[rk][0].saving(rr,source,groupsrc,caps_at,packed,bucket))
        if raw_abs and not positive:best=best.max(_raw_cache[rk][1].saving(rr,source,groupsrc,caps_at,packed,bucket))
        if trig or multi_trig or coupled or free_green:best=best.max(_trig_cache[trigkey][positive].saving(U,rr,source,groupsrc,caps_at))
        if multi_raw and positive:best=best.max(_multi_raw_cache[gkey].saving(U,rr,source,groupsrc,caps_at))
        saving+=dep*best
        if observer is not None:observer(i,rowbase-best)
        if reuse_phase:_phase_cost[pending]=best
        signedbase+=big*(rowbase-signedbest)
    count_last=weight[0]*counts[-1]+dot(wt,oldrows[-1])
    # Only charge damping to the finitely many ordinates through exp(hi).
    damp=dmax*count_last
    eps=4*(-aL/4).exp()
    powers=(1+eps)**(arb(3)/2)*(bL+eps.log1p())**2*(-aL/4).exp()/(6*arb(2).log())
    old=2*(oldbase+(-aL/2).exp()*arb(H)*arb(H).log())+powers*3*density_height/4+(-3*aL).exp()/(1-(-2*aL).exp())
    if observer is not None:
        tail_price=dot(weights(F,aL),final)
        timeless=2*((-aL/2).exp()*arb(H)*arb(H).log()+damp)+(-3*aL).exp()/(1-(-2*aL).exp())
        return T,E,timeless,tail_price,3*powers/4
    new=old-2*saving+2*damp
    if directional:
        other=old+2*(signedbase-oldbase)+2*damp
        print('directional signed full total',other.str(15),flush=True)
        new=new.min(other)
    print('closed physical cell',first,last,'ordinary',old.str(13),'phase saving', (2*saving).str(13),'damping', (2*damp).str(6),'complete',new.str(13),'upper',new.upper().str(13),flush=True)
    return old,new


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--first',default='143.95');parser.add_argument('--last',default='143.951')
    parser.add_argument('--nh',type=int,default=8);parser.add_argument('--sub',type=int,default=2)
    parser.add_argument('--hi',type=int,default=42);parser.add_argument('--step',type=int,default=2)
    parser.add_argument('--halfwidth',type=int,default=4);parser.add_argument('--cells',type=int,default=96)
    parser.add_argument('--params');parser.add_argument('--diagnose',action='store_true')
    parser.add_argument('--directional',action='store_true')
    parser.add_argument('--pieces',type=int,default=1)
    parser.add_argument('--uniform',type=int,default=0,help='reuse one phase measure across this many adjacent pieces')
    parser.add_argument('--save-rows')
    parser.add_argument('--menus',help='comma-separated gap:offset choices on the real-part grid')
    parser.add_argument('--pack',choices=('greedy','linear','cone'))
    parser.add_argument('--multi',action='store_true')
    parser.add_argument('--raw-cone',action='store_true')
    parser.add_argument('--raw-abs',action='store_true')
    parser.add_argument('--reuse-raw',type=int,default=0,help='number of new raw angular proposals per unit of log height')
    parser.add_argument('--trig',action='store_true')
    parser.add_argument('--multi-raw',action='store_true')
    parser.add_argument('--multi-trig',action='store_true')
    parser.add_argument('--coupled',action='store_true')
    parser.add_argument('--free-green',action='store_true')
    parser.add_argument('--extend',type=int,default=0,help='Green source lines strictly to the right of the QRH strip')
    parser.add_argument('--tight-jump',action='store_true',help='monotone joint bounds for the angular source-derivative coefficients')
    parser.add_argument('--source-floor',default='.795',help='smallest participating real-part knot of the free detector')
    parser.add_argument('--more-modes',action='store_true',help='six harmonics for the detector')
    parser.add_argument('--scalar-mix',action='store_true',help='include QRH-convexified scalar hinges in the free source optimization')
    parser.add_argument('--bands',help='comma-separated abscissae partitioning the independent scalar coefficients across free determinants')
    parser.add_argument('--reuse-fit',action='store_true',help='reuse floating proposals in nearby windows and recertify every candidate')
    parser.add_argument('--shared-radial',action='store_true',help='share edge amplitude distributions across all source abscissae')
    parser.add_argument('--shared-opt',action='store_true',help='jointly optimize the sources against both common radial envelopes')
    parser.add_argument('--rotate-phase',action='store_true',help='price nonconstant angular source weights using rotated logarithms and their Fourier coefficients')
    parser.add_argument('--rotate-opt',action='store_true',help='optimize the Green sources against phase-dependent circle means')
    parser.add_argument('--load-rows')
    parser.add_argument('--shift-rows',help='exported certificate from round8/critical/shift_parallel.py')
    parser.add_argument('--shifts',default='all')
    parser.add_argument('--rotate-scalar',action='store_true',help='use the circle-mean estimate on each scalar Green source')
    parser.add_argument('--rotate-signed',action='store_true',help='use the signed circle mean and pay for finite-interval translation')
    args=parser.parse_args()
    ctx.prec=160
    vals=vars(args).copy();diag=vals.pop('diagnose');pieces=vals.pop('pieces');uniform=vals.pop('uniform')
    filename=vals.pop('shift_rows');shifts=vals.pop('shifts');rotate=vals.pop('rotate_scalar')
    if vals.pop('rotate_signed'):rotate='signed'
    assert not rotate or filename
    if filename:
        from frozen_green import Book
        vals['book']=Book(filename,shifts,rotate=rotate)
    if pieces==1:
        u,v=verify(**vals)
        if not diag:assert v<1
    else:
        from fractions import Fraction
        from decimal import Decimal
        first,last=Fraction(vals.pop('first')),Fraction(vals.pop('last'))
        assert first<last and pieces>0
        pts=[first+(last-first)*j/pieces for j in range(pieces+1)]
        def dec(z):
            s=str(Decimal(z.numerator)/Decimal(z.denominator))
            assert Fraction(s)==z
            return s
        worst=arb(0)
        for i,(x,y) in enumerate(zip(pts,pts[1:])):
            if uniform:
                assert uniform>0
                top=i//uniform*uniform
                vals['phase_window']=(dec(pts[top]),dec(pts[min(pieces,top+uniform)]))
            _,v=verify(dec(x),dec(y),**vals);worst=worst.max(v)
        print('whole bridge',dec(first),dec(last),'maximum',worst.str(15),'upper',worst.upper().str(15),flush=True)
        if not diag:assert worst<1
