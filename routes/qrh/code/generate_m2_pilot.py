"""Generate proposed Lean enclosures for the conservative M2 pilot.

Arb only proposes dyadic witnesses. Each emitted theorem proves the bound
from its actual real expression using kernel-checked interval arithmetic.
Generation is not verification. Frozen numerical certificates are read-only.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from flint import arb, ctx

ROOT = Path(__file__).resolve().parents[1]
ROWS = ('5.069','6.046','7.077','8.185','9.387','10.70',
        '12.11','13.66','15.35','17.21','19.31','21.77')

def A(x):
    f = Fraction(x)
    return arb(f.numerator) / f.denominator

def enclosure(v, bits, padding=0):
    scale = 1 << bits
    low = (v * scale).floor().unique_fmpz()
    high = (v * scale).ceil().unique_fmpz()
    if low is None or high is None:
        raise ValueError('Arb enclosure does not resolve a dyadic witness')
    return Fraction(int(low)-padding, scale), Fraction(int(high)+padding, scale)

def R(q):
    q = Fraction(q)
    return f'(({q.numerator} / {q.denominator} : ℚ) : ℝ)'

def QR(q):
    q = Fraction(q)
    return f'(({q.numerator} / {q.denominator} : ℚ) : ℝ)'

def sigma_data(j):
    lo, hi = A(Fraction(2048+j,4096)), A(Fraction(2049+j,4096))
    p = 3*(1-lo)/(2-lo)
    factor = arb(ROWS[j//128])*(((hi-1)*A('715/4')+p*A('2057/64')).exp()
                              -((lo-1)*A('715/4')+p*A('2057/64')).exp())
    return enclosure(factor,48)[1], enclosure(p-A('1/3'),48)[1]

def height_z(u):
    return (-u).exp() + (A('179/6')-u).exp()/6

def zkernel(z):
    return arb(1).min(A('64/31')*z).min(A('4096/31')*z*z)

def height_data(i):
    u = A(Fraction(1842+i,64))
    mass = zkernel(height_z(u-A('1/64'))) - zkernel(height_z(u))
    coefficient = 2*u*u*mass
    if i == 987:
        coefficient += 32*A('4096/31')*height_z(u)**2*u*u
    power = u+u.log()-A('2057/64')
    factor = coefficient*(power/3).exp()
    return enclosure(factor,48,65536)[1], enclosure(power,48,1)[1], enclosure(u.log(),56,1)

def write_generated(output, content, check_only=False):
    """Write generated source, or compare without changing any file."""
    if check_only:
        if not output.is_file() or output.read_bytes() != content.encode('utf-8'):
            raise ValueError(f'Generated source differs: {output}')
    else:
        output.parent.mkdir(parents=True, exist_ok=True)
        output.write_text(content, encoding='utf-8', newline='\n')


def generate(sigma_indices, height_indices, output, namespace_suffix='', check_only=False):
    ctx.prec = 256
    lines = [
        'import LegendreK6.M2PilotDefinitions',
        'import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic',
        'import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp',
        '', '/-! Generated proposals: every bound is checked by Lean, not by trusting Arb. -/',
        'namespace LegendreK6.M2Pilot' + namespace_suffix,
        'set_option maxRecDepth 100000',
        'set_option maxHeartbeats 0', '']
    for j in sigma_indices:
        c, a = sigma_data(j)
        lo, hi = Fraction(2048+j,4096), Fraction(2049+j,4096)
        p = 3*(1-lo)/(2-lo)
        eh, el = (hi-1)*Fraction(715,4)+p*Fraction(2057,64), (lo-1)*Fraction(715,4)+p*Fraction(2057,64)
        lines += [
            f'theorem sigma_factor_upper_{j} : sigmaFactor ({j} : Fin 1536) ≤ {R(c)} := by',
            f'  have h : {QR(ROWS[j//128])} * (Real.exp {QR(eh)} - Real.exp {QR(el)}) ≤ {QR(c)} := by',
            '    dyadic_interval [prec := 96]',
            '  norm_num [sigmaFactor, sigmaHi, sigmaLo, left, exponent, row, csB1, shiftV] at h ⊢',
            '  exact h',
            f'theorem sigma_power_upper_{j} : sigmaPower ({j} : Fin 1536) ≤ {R(a)} := by',
            '  norm_num [sigmaPower, exponent, sigmaLo, shiftP]', '']
    grid = sorted({1841+i for i in height_indices} | {1842+i for i in height_indices})
    for num in grid:
        u = Fraction(num,64)
        zl, zh = enclosure(height_z(A(u)),64,1)
        gl, gh = enclosure(zkernel(height_z(A(u))),56,2)
        lines += [
            f'theorem height_z_bounds_{num} : {R(zl)} ≤ heightZ {R(u)} ∧',
            f'    heightZ {R(u)} ≤ {R(zh)} := by',
            f'  have h : {QR(zl)} ≤ Real.exp (-{QR(u)}) + {QR(Fraction(1,6))} * Real.exp {QR(Fraction(179,6)-u)} ∧',
            f'      Real.exp (-{QR(u)}) + {QR(Fraction(1,6))} * Real.exp {QR(Fraction(179,6)-u)} ≤ {QR(zh)} := by',
            '    constructor <;> dyadic_interval [prec := 80]',
            '  norm_num [heightZ, right] at h ⊢',
            '  constructor <;> linarith',
            f'theorem kernel_bounds_{num} : {R(gl)} ≤ logKernel {R(u)} ∧',
            f'    logKernel {R(u)} ≤ {R(gh)} := by',
            f'  obtain ⟨hl, hh⟩ := height_z_bounds_{num}',
            '  constructor',
            f'  · exact (show {R(gl)} ≤ zKernel {R(zl)} by norm_num [zKernel]).trans',
            '      (zKernel_monotone (by norm_num) hl)',
            f'  · exact (zKernel_monotone (heightZ_nonneg {R(u)}) hh).trans',
            f'      (show zKernel {R(zh)} ≤ {R(gh)} by norm_num [zKernel])', '']
    for i in height_indices:
        factor, power, (ll, lh) = height_data(i)
        u = Fraction(1842+i,64)
        lines += [
            f'theorem log_height_bounds_{i} : {R(ll)} ≤ Real.log {R(u)} ∧',
            f'    Real.log {R(u)} ≤ {R(lh)} := by',
            f'  have hl : Real.exp {QR(ll)} ≤ {QR(u)} := by dyadic_interval [prec := 80]',
            f'  have hh : {QR(u)} ≤ Real.exp {QR(lh)} := by dyadic_interval [prec := 80]',
            '  constructor',
            '  · exact (Real.le_log_iff_exp_le (by norm_num)).2 hl',
            '  · exact (Real.log_le_iff_le_exp (by norm_num)).2 hh',
            f'theorem height_power_upper_{i} : heightPower ({i} : Fin 988) ≤ {R(power)} := by',
            f'  have hh := log_height_bounds_{i}',
            '  norm_num [heightPower, heightV, height, shiftV] at *',
            '  linarith',
            f'theorem height_factor_upper_{i} : heightFactor ({i} : Fin 988) ≤ {R(factor)} := by',
            f'  obtain ⟨hll, hlh⟩ := log_height_bounds_{i}',
            f'  obtain ⟨hpl, hph⟩ := kernel_bounds_{1841+i}',
            f'  obtain ⟨hcl, hch⟩ := kernel_bounds_{1842+i}',
            f'  obtain ⟨hzl, hzh⟩ := height_z_bounds_{1842+i}',
            f'  have h : ({QR(2*u*u)} * (logKernel {R(u-Fraction(1,64))} - logKernel {R(u)})' +
              (f' + {QR(32*Fraction(4096,31)*u*u)} * (heightZ {R(u)}) ^ 2' if i==987 else '') + ') *',
            f'      Real.exp ({QR(Fraction(1,3))} * ({QR(u)} + Real.log {R(u)} - {QR(Fraction(2057,64))})) ≤ {QR(factor)} := by',
            '    dyadic_interval [prec := 80]',
            '  norm_num [heightFactor, heightCoefficient, heightMass, heightPower, heightV,',
            '    height, shiftP, shiftV] at h ⊢',
            '  nlinarith only [h]', '']
    lines += ['end LegendreK6.M2Pilot' + namespace_suffix, '']
    write_generated(output, '\n'.join(lines), check_only)
    return dict(status='SOURCE_MATCHES' if check_only else 'GENERATED_UNCHECKED',source=str(output.relative_to(ROOT)),
                sigma_indices=sigma_indices,height_indices=height_indices,
                bytes=output.stat().st_size,sha256=hashlib.sha256(output.read_bytes()).hexdigest())

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--sigma',nargs='*',type=int,default=[0,1535])
    parser.add_argument('--height',nargs='*',type=int,default=[0,987])
    parser.add_argument('--output',type=Path,default=ROOT/'lean/LegendreK6/M2Pilot/EnclosureSample.lean')
    parser.add_argument('--namespace-suffix',default='')
    parser.add_argument('--all-blocks',action='store_true',
                        help='Generate all 1536 sigma and 988 height enclosures in independent blocks.')
    parser.add_argument('--check',action='store_true',
                        help='Regenerate in memory and compare sources without changing any files.')
    args=parser.parse_args()
    if args.all_blocks:
        blocks=[]
        folder=ROOT/'lean/LegendreK6/M2Pilot/Enclosures'
        for first in range(0,1536,128):
            name=f'Sigma{first//128:03d}'
            blocks.append(generate(list(range(first,min(first+128,1536))),[],
                                   folder/(name+'.lean'),'.Enclosures.'+name,args.check))
        for first in range(0,988,32):
            name=f'Height{first//32:03d}'
            blocks.append(generate([],list(range(first,min(first+32,988))),
                                   folder/(name+'.lean'),'.Enclosures.'+name,args.check))
        report=ROOT/'tmp/m2_enclosure_generation.json'
        if not args.check:
            report.parent.mkdir(parents=True,exist_ok=True)
            report.write_text(json.dumps(dict(status='GENERATED_UNCHECKED',blocks=blocks),indent=2)+'\n')
        print(json.dumps(dict(status='SOURCE_MATCHES' if args.check else 'GENERATED_UNCHECKED',number_of_blocks=len(blocks),
                              bytes=sum(r['bytes'] for r in blocks),report=str(report)),indent=2))
        return
    if any(not 0 <= j < 1536 for j in args.sigma) or any(not 0 <= i < 988 for i in args.height):
        parser.error('Index outside the fixed pilot grids')
    print(json.dumps(generate(sorted(set(args.sigma)),sorted(set(args.height)),args.output,args.namespace_suffix,args.check),indent=2))

if __name__=='__main__':
    main()
