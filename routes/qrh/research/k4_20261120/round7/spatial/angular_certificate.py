"""Verify all angles and real parts in a many-source physical Green majorant."""
import argparse
from pathlib import Path
import sys
from flint import arb,ctx
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/"round8"/"zero_strip"))
from angular_design import problem
import numpy as np


def arbmax(values):
    v=values[0]
    for u in values[1:]:v=v.max(u)
    return v


def certify(step="0.45",count=14,positive=True,degree=3,cells=48,angles=240,
            weight_step=None,details=False):
    assert count>=3 and cells>=4 and angles%2==0
    modes=list(range(1 if positive else 2,degree+1,1 if positive else 2))
    t=arb(step)
    ax=[j*t for j in range(count)]
    ws=t if weight_step is None else arb(weight_step)
    w=[(j*ws).exp() for j in range(count)]
    k=z=None
    # Nearby rational design steps also give admissible candidates. The
    # enclosure below always uses the complete requested physical interval.
    for proposal in (float(t.mid()),round(float(t.mid()),2),.45):
        try:
            k,z=problem(np.arange(count)*proposal,count*proposal,np.array(modes),positive)
            break
        except AssertionError:
            continue
    if z is None:
        k,z=1,np.zeros((count,len(modes)))
    scale=10**7
    # These arbitrary rational proposals enter only the subsequent interval check.
    k=arb(int(round(k*scale)))/scale
    coef=[[arb(int(round(z[i,j]*scale)))/scale*w[i] for j in range(len(modes))]
          for i in range(count)]
    for j,m in enumerate(modes):
        coef[0][j]=-sum(coef[i][j]*(-m*ax[i]).exp() for i in range(1,count))
    tg=[arb.pi()*i/angles for i in range(angles+1)]
    cs=[[(m*y).cos() for m in [1]+modes] for y in tg]
    h2=arb.pi()**2/(8*angles**2)
    source_repair=arb(0)
    # Positive lower density on each full angular period by linear interpolation.
    for i,source in enumerate(coef):
        rel=[v/w[i] for v in source]
        err=h2*sum(m*m*abs(v) for m,v in zip(modes,rel))
        deficit=arbmax([-k-sum(c*v for c,v in zip(row[1:],rel)) for row in cs])+err
        source_repair=source_repair.max(deficit)
    def ratios(x,end):
        # Use G_m(0)=0 in closed form on the first interval, including x=0.
        if end==1:
            vals=[]
            for j,m in enumerate(modes):
                upper=arb(1) if x.is_zero() else (m*x).sinh()/(m*x)
                vals.append(coef[0][j]*upper/w[0])
            return vals
        B=sum(wi*(x-xi) for wi,xi in zip(w[:end],ax[:end]))
        out=[]
        for j,m in enumerate(modes):
            F=arb(0)
            for i in range(1,count):
                diff=x-ax[i]
                d=diff if i<end else -diff
                h=ax[i] if i<end else x
                F+=coef[i][j]*(-m*d).exp()*(-2*m*h).expm1()/(2*m)
            out.append(F/B)
        return out
    def angular(vals):
        # The positive part and the modulus have smooth branches separated at pi/2.
        err=h2*(1+sum(m*m*abs(v).upper() for v,m in zip(vals,modes)))
        defects=[]
        for idx,row in enumerate(cs):
            target=row[0] if idx<=angles//2 else (arb(0) if positive else -row[0])
            defects.append(target-k-sum(c*v for c,v in zip(row[1:],vals)))
        return arbmax(defects)+err
    target_repair=arb(0)
    for end in range(1,count+1):
        start=(end-1)*t
        # On the open space between two adjacent sources, F_m''=m² F_m.
        # At fixed angle, B*target is affine. Interpolating the dimensional
        # inequality costs curvature/B_left; only the first cell needs a limit.
        previous=ratios(start,end)
        prev_cost=angular(previous)
        for i in range(cells):
            l=start+i*t/cells;r=l+t/cells
            nxt=ratios(r,end)
            cost=angular(nxt)
            if end==1:
                curvature=sum(abs(coef[0][j])*m*m*(m*t).cosh()/w[0]
                              for j,m in enumerate(modes))
            else:
                B0=sum(wj*(l-xj) for wj,xj in zip(w[:end],ax[:end]))
                B1=B0+sum(w[:end])*(r-l)
                curvature=sum(m*m*abs(a).max(abs(b)*B1/B0) for a,b,m in zip(previous,nxt,modes))
            target_repair=target_repair.max(prev_cost.max(cost)+(r-l)**2*curvature/8)
            previous=nxt;prev_cost=cost
    pad=source_repair.max(target_repair).max(0)
    final=k+pad
    if details:
        # Coordinate x=omega*(sigma-a0); division of the Green function by
        # omega leaves these exact dimensionless source and boundary multipliers.
        slope=final*sum(w)+sum(abs(z) for row in coef[1:] for z in row)
        return final,w,coef,slope,modes
    print("positive" if positive else "absolute","modes",modes,"candidate",k.str(12),
          "source and spatial repairs",source_repair.str(9),target_repair.str(9),
          "certified common constant",final.str(14),flush=True)
    return final


if __name__=="__main__":
    ctx.prec=144
    cli=argparse.ArgumentParser()
    cli.add_argument("--step",default=".45");cli.add_argument("--count",type=int,default=14)
    cli.add_argument("--degree",type=int,default=3);cli.add_argument("--absolute",action="store_true")
    cli.add_argument("--upper")
    a=cli.parse_args()
    val=certify(a.step,a.count,not a.absolute,a.degree)
    if a.upper:assert val<arb(a.upper)
