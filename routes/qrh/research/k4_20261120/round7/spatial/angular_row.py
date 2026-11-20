"""Price a many-line positive-cosine majorant on a true cumulative height."""
from pathlib import Path
import argparse
import json
from flint import arb, ctx
from angular_certificate import certify
from weighted_green import radial, kernel
from exact_bridge import angular_edge, interpolated_point, radial_table
from grid_target import chord_bounds
from signed_profile import positive_radius


def least(values):
    answer = values[0]
    for candidate in values[1:]:
        answer = answer.min(candidate)
    return answer


def row(lo, hi, log_height, start, spacing, count, degrees):
    a, b, u = map(arb, (lo, hi, log_height))
    nodes = [arb(start + j * spacing) / 1000 for j in range(count)]
    assert start + count * spacing == 875 and 110 < a <= b < 150
    width = (4 * (-a / 4).exp()).log1p()
    assert u.exp() * width < positive_radius() and arb.pi() / a < arb('.1')
    frequency = arb((a+b)/2, (b-a+width)/2)
    g = arb(spacing) / 1000
    multiplier, weights, sources, edge_scale, modes = certify(
        frequency * g, count, True, degrees, weight_step=a*g, details=True)
    U = (u.exp() + arb('.1')).log()
    cache = Path(__file__).resolve().parents[2] / 'round8' / 'zero_strip' / 'phase_norms.json'
    frozen = json.loads(cache.read_text(encoding='utf8'))
    scale = frozen['norm_scale']
    assert frozen['top_padding'] == '.1' and frozen['sub'] == 4
    # Each closed cached slab extends to log(exp((k+1)/4)+.1).
    key = int((u * 4).lower().floor().unique_fmpz())
    assert arb(key)/4 <= u <= arb(key+1)/4
    rows = [(arb(d)/frozen['parameter_scale'], arb(l)/scale, arb(r)/scale, arb(e)/scale)
            for k,d,_,_,l,r,e in frozen['rows'] if k == key]
    assert rows and scale == 10**20
    polynomials = radial_table(ctx.prec)
    cost = []
    for delta, left, right, edge in rows:
        terms = [edge_scale * edge for _ in polynomials]
        for n, w, coefficients in zip(nodes, weights, sources, strict=True):
            h = multiplier * w
            ml = mr = h
            for m,c in zip(modes, coefficients, strict=True):
                nu,p,base,ql,qr = kernel(U,left,right,delta,n,frequency*m)
                ml += abs(c)*ql
                mr += abs(c)*qr
            factor = base * ml**p * mr**(1-p)
            for j, line in enumerate(polynomials):
                terms[j] += factor * radial(line,nu)
        cost.extend(terms)
    improved = least(cost)
    # Ordinary competitors may select a separate polynomial and detector per knot.
    all_x = [arb(j)/1000 for j in range(650,876)]
    hats = []
    for s in all_x[:-1]:
        ordinary = []
        for delta,left,right,edge in rows:
            nu,_,base,_,_ = kernel(U,left,right,delta,s,frequency)
            ordinary.append(base*interpolated_point(nu)+edge)
        hats.append(least(ordinary))
    hats.append(arb(0))
    roof = chord_bounds(all_x,hats)
    idx = [start+j*spacing-650 for j in range(count)]
    plain = sum(w*hats[i] for i,w in zip(idx,weights,strict=True))
    convex = sum(w*roof[i] for i,w in zip(idx,weights,strict=True))
    print('L',lo,hi,'log T',log_height,'nodes',start,spacing,count,
          'certified source scale',multiplier.str(12),'weighted',improved.str(13),
          'scalar',plain.str(13),'convex scalar',convex.str(13),
          'ratio to convex', (improved/convex).str(12),flush=True)
    return improved, convex


if __name__ == '__main__':
    cli = argparse.ArgumentParser()
    cli.add_argument('--lo',default='143.4'); cli.add_argument('--hi',default='143.41')
    cli.add_argument('--log-height',default='36')
    cli.add_argument('--start',type=int,default=833); cli.add_argument('--spacing',type=int,default=3)
    cli.add_argument('--count',type=int,default=14); cli.add_argument('--degrees',type=int,default=3)
    cli.add_argument('--upper-ratio')
    ctx.prec = 160
    args=vars(cli.parse_args()); limit=args.pop('upper_ratio')
    new,old = row(**args)
    if limit: assert new/old < arb(limit)
