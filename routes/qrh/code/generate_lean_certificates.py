"""Emit kernel-checkable finite data and recursive Lucas primality certificates.

The Python generator is not trusted by Lean. Factorizations and modular-power
witnesses are only suggestions: the emitted proofs are checked by the Lean kernel.
The rational certificate module checks saved rational data, NOT the Arb
transcendental enclosures from which those data were obtained.
Generated source/data deliberately use CRLF on every platform, preserving
the exact bytes of the initial kernel-checked release.
"""
from __future__ import annotations
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import tempfile

import flint

PROOF = Path(__file__).resolve().parents[1]
LEAN = PROOF / 'lean' / 'LegendreK6'
PRATT_DATA = PROOF / 'results' / 'pratt_certificate_data.json'


def rat(value):
    q = Fraction(value)
    return str(q.numerator) if q.denominator == 1 else f'({q.numerator} / {q.denominator})'


def read(name):
    path = PROOF / 'results' / name
    return json.loads(path.read_text(encoding='utf-8')), hashlib.sha256(path.read_bytes()).hexdigest()


def finite_data():
    refined, rhash = read('smooth_k6_certificate.json')
    old, ohash = read('smooth_segment_certificate.json')
    lower, lhash = read('lower_range_k6_certificate.json')
    header = '''import Mathlib.Data.Rat.Defs

/-! Generated exact rational data, not a formalization of the Arb enclosures.
    Regenerate with proof/code/generate_lean_certificates.py. -/
namespace LegendreK6

structure SavedCell where
  left : ℚ
  right : ℚ
  upper : ℚ
  scaledUpper : ℚ
  deriving DecidableEq, Repr

'''
    output = [header, f'-- refined source SHA256: {rhash}\n', 'def refinedCells : List SavedCell := [\n']
    for i, cell in enumerate(refined['cells']):
        vals = [cell['left'], cell['right'], cell['delta_upper_rational'], cell['sensitivity']['all_three_scaled_upper']]
        output.append('  ⟨' + ', '.join(map(rat, vals)) + '⟩' + (',' if i + 1 < len(refined['cells']) else '') + '\n')
    output += [']\n\n', f'-- old segment source SHA256: {ohash}\n', 'def polynomialCells : List SavedCell := [\n']
    for i, cell in enumerate(old['cells']):
        vals = [cell['left'], cell['right'], cell['delta_upper_rational'], Fraction(53, 50)*Fraction(cell['delta_upper_rational'])]
        output.append('  ⟨' + ', '.join(map(rat, vals)) + '⟩' + (',' if i + 1 < len(old['cells']) else '') + '\n')
    output += [']\n\n', f'-- lower range source SHA256: {lhash}\n', 'def chlIntegerRows : List (ℕ × ℕ) := [\n']
    rows = lower['coverage']['chain']
    for i, row in enumerate(rows):
        output.append(f"  ({row['next_start']}, {row['new_end']})" + (',' if i+1 < len(rows) else '') + '\n')
    output += [']\n\nend LegendreK6\n']
    LEAN.mkdir(parents=True, exist_ok=True)
    (LEAN/'CertificateData.lean').write_text(''.join(output), encoding='utf-8', newline='\r\n')


def generate_pratt(block_size=200):
    lower, lhash = read('lower_range_k6_certificate.json')
    witnesses = lower['small_range']['witnesses_indexed_by_n_minus_one']
    todo, done, factors = set(witnesses), set(), {}
    while todo:
        p = todo.pop()
        done.add(p)
        if p == 2:
            continue
        fs = [(int(q), int(e)) for q,e in flint.fmpz(p-1).factor()]
        assert __import__('math').prod(q**e for q,e in fs) == p-1
        factors[p] = fs
        todo.update(q for q,e in fs if q not in done)
    primes = sorted(done)
    records = []
    chunks = [primes[i:i+block_size] for i in range(0, len(primes), block_size)]
    directory = LEAN/'Pratt'
    directory.mkdir(exist_ok=True)
    for block, ps in enumerate(chunks):
        if block:
            imports = f'import LegendreK6.Pratt.Block{block-1:03d}\n'
        else:
            imports = 'import Mathlib.NumberTheory.LucasPrimality\nimport Mathlib.Tactic\n'
        lines = [imports, '\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace LegendreK6.Pratt\n\n']
        for p in ps:
            if p < 1000:
                lines.append(f'theorem prime_{p} : Nat.Prime {p} := by norm_num\n\n')
                records.append({'p':p, 'mode':'small_trial_division'})
                continue
            fs = factors[p]
            a = 2
            while pow(a, p-1, p) != 1 or any(pow(a,(p-1)//q,p)==1 for q,e in fs):
                a += 1
            records.append({'p':p,'a':a,'factors':fs})
            lines += [f'theorem prime_{p} : Nat.Prime {p} := by\n',
                      f'  apply lucas_primality {p} ({a} : ZMod {p})\n',
                      '  · reduce_mod_char\n',
                      '  · intro q hq hd\n']
            def product(seq):
                q,e = seq[0]
                head = f'({q} : ℕ)^{e}'
                return head if len(seq)==1 else head + ' * (' + product(seq[1:]) + ')'
            lines += [f'    have hfac : {p} - 1 = {product(fs)} := by norm_num\n',
                      '    rw [hfac] at hd\n']
            def branches(seq, indent):
                q,e=seq[0]
                prefix=' '*indent
                if len(seq)>1:
                    lines.append(prefix+'rcases hq.dvd_mul.mp hd with hd | hd\n')
                    lines.append(prefix+f'· have heq : q = {q} := Nat.prime_eq_prime_of_dvd_pow hq prime_{q} hd\n')
                    lines.append(prefix+'  subst q\n')
                    lines.append(prefix+f'  change ({a} : ZMod {p})^{(p-1)//q} ≠ 1\n')
                    lines.append(prefix+'  reduce_mod_char\n'+prefix+'  decide\n')
                    lines.append(prefix+'· ')
                    start=len(lines)
                    branches(seq[1:], indent+2)
                    # Combine the first recursive line with the previous bullet.
                    lines[start] = lines[start][indent+2:]
                else:
                    lines.append(prefix+f'have heq : q = {q} := Nat.prime_eq_prime_of_dvd_pow hq prime_{q} hd\n')
                    lines.append(prefix+'subst q\n')
                    lines.append(prefix+f'change ({a} : ZMod {p})^{(p-1)//q} ≠ 1\n')
                    lines.append(prefix+'reduce_mod_char\n'+prefix+'decide\n')
            branches(fs, 4)
            lines.append('\n')
        lines.append('end LegendreK6.Pratt\n')
        (directory/f'Block{block:03d}.lean').write_text(''.join(lines),encoding='utf-8',newline='\r\n')
    result = {'source_sha256':lhash,'method':'recursive Lucas certificates; Python only generates suggestions',
              'number_of_prime_nodes':len(primes),'number_of_witnesses':len(witnesses),'blocks':len(chunks),'records':records}
    PRATT_DATA.parent.mkdir(parents=True, exist_ok=True)
    PRATT_DATA.write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8',newline='\r\n')
    # Individual finite short-interval facts: every primality assertion is a
    # previously kernel-proved theorem; the two inequalities use norm_num.
    lines=[f'import LegendreK6.Pratt.Block{len(chunks)-1:03d}\n',
           'import LegendreK6.Definitions\n\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\n\nnamespace LegendreK6\n\n']
    for n,p in enumerate(witnesses,1):
        lines.append(f'theorem small_prime_{n} : NatSixthShort {n} := by\n')
        lines.append(f'  exact ⟨{p}, Pratt.prime_{p}, by norm_num, by norm_num⟩\n\n')
    lines.append('theorem small_range_prime (n : ℕ) (hn : 1 ≤ n) (hmax : n ≤ 1259) : NatSixthShort n := by\n')
    # Binary case split keeps proof depth bounded and avoids massive interval_cases.
    def cases(lo, hi, indent):
        prefix=' '*indent
        if lo==hi:
            lines.append(prefix+f'have heq : n = {lo} := by omega\n')
            lines.append(prefix+'subst n\n')
            lines.append(prefix+f'exact small_prime_{lo}\n')
            return
        mid=(lo+hi)//2
        lines.append(prefix+f'by_cases hsplit_{lo}_{hi} : n ≤ {mid}\n')
        lines.append(prefix+'· ')
        idx=len(lines);cases(lo,mid,indent+2);lines[idx]=lines[idx][indent+2:]
        lines.append(prefix+'· ')
        idx=len(lines);cases(mid+1,hi,indent+2);lines[idx]=lines[idx][indent+2:]
    cases(1,len(witnesses),2)
    lines.append('\nend LegendreK6\n')
    (LEAN/'PrimeWitnesses.lean').write_text(''.join(lines),encoding='utf-8',newline='\r\n')
    print(f'Generated {len(primes)} recursive prime nodes in {len(chunks)} blocks and {len(witnesses)} short-interval proofs.', flush=True)


def main():
    global LEAN, PRATT_DATA
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--data-only', action='store_true')
    parser.add_argument('--check', action='store_true',
                        help='Regenerate in a temporary directory and compare bytes without modifying saved outputs')
    args=parser.parse_args()
    if args.check:
        original_lean, original_data = LEAN, PRATT_DATA
        with tempfile.TemporaryDirectory(prefix='legendre_k6_lean_cert_check_') as temporary:
            LEAN = Path(temporary)/'LegendreK6'
            PRATT_DATA = Path(temporary)/'pratt_certificate_data.json'
            finite_data()
            if not args.data_only:
                generate_pratt()
            outputs = list(LEAN.rglob('*.lean'))
            for output in outputs:
                saved = original_lean/output.relative_to(LEAN)
                if saved.read_bytes() != output.read_bytes():
                    raise ValueError(f'Generated source does not match saved file: {saved}')
            if not args.data_only and original_data.read_bytes() != PRATT_DATA.read_bytes():
                raise ValueError('Pratt data file differs from deterministic regeneration')
            print(f'GENERATED_SOURCES_MATCH: {len(outputs)} Lean files; no saved outputs modified.')
    else:
        finite_data()
        if not args.data_only:
            generate_pratt()


if __name__=='__main__':
    main()
