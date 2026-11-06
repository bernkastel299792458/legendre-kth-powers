"""Generate the finite proof-index assembly for the M3 far pilot.

The generated modules reuse kernel-checked exp/log enclosure theorems.
Arb proposes literal dyadic witnesses only. Every link to the integer
witness table is proved again in Lean; running this generator is not a
proof check. The frozen original Arb certificates are not modified.
"""
from pathlib import Path
import argparse
ROOT = Path(__file__).resolve().parents[1]
import generate_m3_far as g
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--check', action='store_true',
                    help='Compare generated sources in memory without changing files.')
args = parser.parse_args()
g.ctx.prec=256
folder=ROOT/'lean/LegendreK6/M3Far/FactorBounds'
allnames=[]
for kind,count,size in [('Sigma',384,32),('Height',125,32)]:
 prefix=kind.lower()
 for first in range(0,count,size):
  last=min(first+size,count)
  name=f'{kind}{first//size:03d}'
  allnames.append(name)
  lines=[f'import LegendreK6.M3Far.Enclosures.{name}',
   'import LegendreK6.M3FarIntegerData','',
   '/-! Join checked analytic enclosures to the exact dyadic witness table. -/',
   f'namespace LegendreK6.M3Far.FactorBounds.{name}',
   'set_option maxRecDepth 100000','set_option maxHeartbeats 0','',
   f'theorem bounds (i : Fin {count}) (hlo : {first} ≤ i.val) (hhi : i.val < {last}) :',
   f'    {prefix}Factor i ≤ {prefix}DyadicFactor i ∧ {prefix}Power i ≤ {prefix}DyadicPower i := by',
   '  interval_cases hi : i.val']
  for i in range(first,last):
   vals=g.sigma_data(i) if kind=='Sigma' else g.height_data(i)[:2]
   lines += [f'  · have heq : i = ({i} : Fin {count}) := Fin.ext hi','    subst i','    constructor']
   for term,v in zip(['Factor','Power'],vals):
    n=int(v*2**48)
    lines += [f'    · apply Enclosures.{name}.{prefix}_{term.lower()}_upper_{i}.trans',
     f'      change {g.R(v)} ≤ (({n} : ℕ) : ℝ) / 2^48',
     '      norm_num']
  lines += [f'end LegendreK6.M3Far.FactorBounds.{name}','']
  g.write_generated(folder/(name+'.lean'), '\n'.join(lines), args.check)
print(len(allnames), 'bound blocks match' if args.check else 'bound blocks generated')


folder=ROOT/'lean/LegendreK6'
names=[f'Sigma{k:03d}' for k in range(12)]+[f'Height{k:03d}' for k in range(4)]
s=[f'import LegendreK6.M3Far.FactorBounds.{name}' for name in names]
s+=['','/-! All checked pointwise enclosures for the complete conservative pilot. -/','namespace LegendreK6.M3Far','set_option maxHeartbeats 0','set_option maxRecDepth 100000','']
for prefix,count,size in [('sigma',384,32),('height',125,32)]:
 total=(count+size-1)//size
 s += [f'theorem {prefix}DyadicBounds (i : Fin {count}) :',f'    {prefix}Factor i ≤ {prefix}DyadicFactor i ∧ {prefix}Power i ≤ {prefix}DyadicPower i := by',
       '  have hi := i.isLt',f'  have hk : i.val / {size} < {total} := by omega',f'  interval_cases h : i.val / {size}']
 for k in range(total):
  s += [f'  · exact FactorBounds.{prefix.capitalize()}{k:03d}.bounds i (by omega) (by omega)']
 s+=['']
 for term in ['Factor','Power']:
  idx=1 if term=='Factor' else 2
  s += [f'theorem {prefix}{term}_upper (i : Fin {count}) :',f'    {prefix}{term} i ≤ {prefix}Dyadic{term} i := ({prefix}DyadicBounds i).{idx}','']
s += ['end LegendreK6.M3Far','']
g.write_generated(folder/'M3FarFactorBounds.lean', '\n'.join(s), args.check)
s=['import LegendreK6.M3FarFactorBounds','import LegendreK6.M3FarIntegerCertificate','import LegendreK6.M3FarExpression','',
'/-! Kernel-checked numerical conclusion for the actual low-rank expression. -/',
'namespace LegendreK6.M3Far','',
'theorem lowRankTaylor20_le :',
'    lowRankTaylor20 Finset.univ Finset.univ sigmaFactor sigmaPower heightFactor heightPower ≤',
'      (9 / 20 : ℝ) := by',
'  apply (lowRankTaylor20_mono Finset.univ Finset.univ',
'    sigmaFactor sigmaPower sigmaDyadicFactor sigmaDyadicPower',
'    heightFactor heightPower heightDyadicFactor heightDyadicPower',
'    (fun j _ => sigmaFactor_nonneg j) (fun j _ => (sigmaPower_bounds j).1)',
'    (fun i _ => heightFactor_nonneg i) (fun i _ => (heightPower_bounds i).1)',
'    (fun j _ => sigmaFactor_upper j) (fun j _ => sigmaPower_upper j)',
'    (fun i _ => heightFactor_upper i) (fun i _ => heightPower_upper i)).trans',
'  exact dyadicLowRank20_le','',
'end LegendreK6.M3Far','']
g.write_generated(folder/'M3FarLowRankBound.lean', '\n'.join(s), args.check)
print('Both final bound modules match' if args.check else 'Written final bound modules; Lean verification required')
