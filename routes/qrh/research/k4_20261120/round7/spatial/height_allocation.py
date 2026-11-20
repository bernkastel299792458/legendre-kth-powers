"""Allocate positive- and negative-cosine height costs on the actual spectral lobes."""
import argparse
import json
from decimal import Decimal
from fractions import Fraction
from functools import partial
from pathlib import Path
import sys
from flint import arb,ctx
import numpy as np
from scipy.optimize import linprog
from scipy.sparse import csc_matrix,diags,eye,hstack,vstack
from signed_profile import local_caps
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'round8'/'zero_strip'))
from complete_green import verify
from frozen_green import Book
from weighted_green import H


def allocate(target,cplus,cabs,intervals=()):
    m=len(target)
    assert len(cplus)==len(cabs)==m
    # x+, x-, xabs are masses placed at each horizon; y+, y- are their
    # cumulative suffixes. This sparse formulation has O(m) nonzeros.
    I=eye(m,format='csc');Z=0*I
    delta=diags([1.,-1.],[0,1],shape=(m,m),dtype=float,format='csc')
    A=vstack((hstack((-I,Z,-I,delta,Z)),hstack((Z,-I,-I,Z,delta))),format='csc')
    p=np.array([float(x.mid()) for x in cplus])
    v=np.array([float(x.mid()) for x in cabs])
    z=np.maximum(0,np.array([[float(x.mid()) for x in row] for row in target]))
    obj=np.concatenate((p,p,v,np.zeros(2*m)))
    bounds=[(0,None)]*(3*m)+[(float(x),None) for x in np.concatenate((z[:,0],z[:,1]))]
    rhs=np.zeros(2*m)
    if intervals:
        n=len(intervals)
        ix=np.zeros((m,n))
        for j,(start,end,one,both) in enumerate(intervals):
            assert 0<=start<end<=m and min(one,both)>0
            ix[start:end,j]=1
        incidence=csc_matrix(ix);empty=incidence*0
        top=hstack((A,csc_matrix((2*m,3*n))))
        bottom=vstack((hstack((Z,Z,Z,-I,Z,-incidence,empty,-incidence)),
                       hstack((Z,Z,Z,Z,-I,empty,-incidence,-incidence))))
        A=vstack((top,bottom),format='csc')
        rhs=np.concatenate((rhs,-z[:,0],-z[:,1]))
        bounds=[(0,None)]*(5*m+3*n)
        obj=np.concatenate((obj,[float(row[i].mid()) for i in (2,2,3) for row in intervals]))
    prop=linprog(obj,A_ub=A,b_ub=rhs,bounds=bounds,method='highs')
    # A failed proposal can always be replaced by a zero one. The backward
    # exact repair independently enforces every physical inequality.
    ans=np.array(prop.x[:3*m]).reshape(3,m) if prop.success else np.zeros((3,m))
    scale=2**52
    paid=pos=neg=arb(0)
    localp=[arb(0) for _ in target];localn=localp.copy()
    if prop.success and intervals:
        local=prop.x[5*m:].reshape((3,len(intervals)))
        for j,(start,end,one,both) in enumerate(intervals):
            xp,xn,xa=[arb(max(0,int(round(float(row[j])*scale))))/scale for row in local]
            paid+=(xp+xn)*one+xa*both
            for k in range(start,end):
                localp[k]+=xp+xa;localn[k]+=xn+xa
    for i in range(m-1,-1,-1):
        x,y,h=[arb(max(0,int(round(float(v[i])*scale))))/scale for v in ans]
        pos+=x+h;neg+=y+h
        fixp=(target[i][0]-pos-localp[i]).upper().max(0)
        fixn=(target[i][1]-neg-localn[i]).upper().max(0)
        # Exact fixed-denominator upward rounding keeps all suffixes dyadic.
        dx=arb(int((fixp*scale).upper().ceil().unique_fmpz()))/scale
        dy=arb(int((fixn*scale).upper().ceil().unique_fmpz()))/scale
        pos+=dx;neg+=dy
        assert pos+localp[i]>=target[i][0] and neg+localn[i]>=target[i][1]
        paid+=(x+y+dx+dy)*cplus[i]+h*cabs[i]
    return paid


def add_near_heights(T,caps,paths,lo,hi):
    # A translated finite rectangle and an origin-centered cumulative rectangle
    # can both pay any smaller positive-ordinate sum with the same reward.
    rows=list(zip(T[1:],*caps,strict=True))
    for file in paths.split(','):
        obj=json.loads(Path(file).read_text(encoding='utf8'))
        if 'ordrows' in obj:
            sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'first_selected'))
            from translated_book import prices
            rows.extend((t,v,v) for t,v in prices(obj,lo) if t<T[-1])
            continue
        n=obj['panels'];size=obj['size'];scale=obj['scale']
        assert len(obj['rows'])==n and min(obj['rows'])>0
        ds=arb(lo)-arb(obj['location']);factor=(-ds).max(-ds/8).exp()/scale
        signed='signed_rows' in obj and Fraction(obj['signed_lo'])<=Fraction(lo)<Fraction(hi)<=Fraction(obj['signed_hi'])
        if signed:
            ds=arb(lo)-arb(obj['signed_lo']);pscale=(-ds).max(-ds/8).exp()/scale
        for j,v in enumerate(obj['rows'],1):
            t=arb(H+((size+1280000)*j+n-1)//n)
            absolute=factor*v
            pos=absolute.min(pscale*obj['signed_rows'][j-1]) if signed else absolute
            assert absolute>0 and pos>0
            if t<T[-1]:rows.append((t,pos,absolute))
    rows.sort(key=lambda r:float(r[0].mid()))
    merged=[]
    for t,p,a in rows:
        if merged and (t-merged[-1][0]).is_zero():
            t,v,w=merged.pop();p=p.min(v);a=a.min(w)
        assert not merged or t>merged[-1][0]
        merged.append((t,p,a))
    for i in range(len(merged)-2,-1,-1):
        t,p,a=merged[i];merged[i]=(t,p.min(merged[i+1][1]),a.min(merged[i+1][2]))
    return [arb(H)]+[v[0] for v in merged],[[v[j] for v in merged] for j in (1,2)]


def run(lo,hi,source,nh,step,sub,top,multi_raw,reuse,design=0,heights=None,window=None,
        free_green=False,annuli=None,tight_jump=False,verified_start=False,signed_limit=0,near_rows=None,inputs=False,rotate=False):
    a,b=map(arb,(lo,hi));dlo=(4*(-b/4).exp()).log1p();dhi=(4*(-a/4).exp()).log1p()
    book=source if isinstance(source,Book) else Book(source,'.012,.016',rotate='signed' if rotate else False)
    opts=dict(first=lo,last=hi,nh=nh,step=step,sub=sub,hi=top,book=book,
              menus='3:0,4:4,5:0',raw_cone=True,raw_abs=True,multi_raw=multi_raw,
              reuse_raw=reuse,phase_window=window or (lo,hi),free_green=free_green,tight_jump=tight_jump)
    caps=[]
    fixed=None
    for kind in ('positive','absolute'):
        result=[]
        def capture(i,cost):
            assert i==len(result) and cost>0
            result.append(cost)
        T,E,constant,tail_price,power_unit=verify(**opts,observer=capture,observe_kind=kind)
        charge=constant+2*E[-1]*tail_price+arb('1.5')*power_unit
        assert len(result)==len(T)-1
        caps.append(result);fixed=charge if fixed is None else fixed.min(charge)
    if near_rows:T,caps=add_near_heights(T,caps,near_rows,lo,hi)
    if inputs:return T,caps,constant,tail_price,power_unit
    w=[]
    for i,t in enumerate(T[1:]):
        y0=(dlo*H if verified_start else arb(0)) if i==0 else dlo*T[i]
        pos,neg=local_caps(y0,dhi*t)
        w.append(((pos-E[-1].lower()).upper().max(0),(neg-E[-1].lower()).upper().max(0)))
    intervals=[]
    if annuli:
        from annular_height import upper
        for pair in annuli.split(','):
            first,last=pair.split('/')
            lower,upper_t=arb(first).exp(),arb(last).exp()
            # Only buy bands fully contained in the priced interval. Skip the
            # first band, which covers verified height H to the first horizon.
            indices=[i for i in range(1,len(w)) if T[i]>=lower and T[i+1]<=upper_t]
            assert indices and indices==list(range(indices[0],indices[-1]+1))
            path=Path(__file__).resolve().parents[2]/'round8'/'zero_strip'/'phase_shift_extra.json'
            absolute,positive=upper(lo,hi,first,last,'1.1','8.5','-2.25',210,131072,
                                    grid=1,fourth=path,free=free_green)
            intervals.append((indices[0],indices[-1]+1,positive,absolute))
    pay=partial(allocate,intervals=intervals)
    total=fixed+2*pay(w,*caps)
    if design or heights:
        from joint_polygon import propose,validate
        h=tuple(map(int,heights.split(','))) if heights else propose(T,dlo,dhi,caps,tail_price,design,verified_start,signed_limit)
        alternative=validate(h,T,dlo,dhi,caps,constant,tail_price,power_unit,pay,verified_start)
        print('certified alternative polygon',h,'complete',alternative.str(16),flush=True)
        total=total.min(alternative)
    print('height allocations',len(w),'L',lo,hi,'fixed',fixed.str(12),'complete',total.str(16),flush=True)
    return total


if __name__=='__main__':
    ctx.prec=160
    p=argparse.ArgumentParser()
    p.add_argument('--lo',default='140.5');p.add_argument('--hi',default='140.51')
    default=Path(__file__).resolve().parents[2]/'round8'/'zero_strip'/'phase_shift_extra.json'
    p.add_argument('--source',default=str(default))
    p.add_argument('--nh',type=int,default=4);p.add_argument('--step',type=int,default=4)
    p.add_argument('--sub',type=int,default=16);p.add_argument('--top',type=int,default=41)
    p.add_argument('--reuse',type=int,default=16)
    p.add_argument('--multi-raw',action='store_true');p.add_argument('--check',action='store_true')
    p.add_argument('--free-green',action='store_true')
    p.add_argument('--rotate',action='store_true')
    p.add_argument('--tight-jump',action='store_true')
    p.add_argument('--verified-start',action='store_true')
    p.add_argument('--signed-limit',type=float,default=0,help='allow signed physical densities with this peak in the proposal')
    p.add_argument('--near-rows',help='translated cumulative bounds at any extra heights above H')
    p.add_argument('--annuli',help='comma-separated translated log-height pairs such as 35/36')
    p.add_argument('--design',type=int,default=0)
    p.add_argument('--heights',help='nonnegative rational polygon, common integer scale')
    p.add_argument('--pieces',type=int,default=1)
    p.add_argument('--uniform',type=int,default=1)
    params=vars(p.parse_args());check=params.pop('check')
    pieces=params.pop('pieces');uniform=params.pop('uniform')
    assert pieces>=1 and uniform>=1
    if pieces==1:value=run(**params)
    else:
        first,last=map(Fraction,(params.pop('lo'),params.pop('hi')))
        def decimal(q):
            s=str(Decimal(q.numerator)/Decimal(q.denominator))
            assert q==Fraction(s)
            return s
        edges=[decimal(first+(last-first)*i/pieces) for i in range(pieces+1)]
        params['source']=Book(params['source'],'.012,.016',rotate='signed' if params['rotate'] else False)
        value=arb(0)
        for i,(lo,hi) in enumerate(zip(edges,edges[1:])):
            start=i//uniform*uniform
            window=edges[start],edges[min(pieces,start+uniform)]
            val=run(lo,hi,**params,window=window)
            value=value.max(val)
        print('joint height bridge',edges[0],edges[-1],pieces,'upper',value.upper().str(18),flush=True)
    if check:assert value<1
