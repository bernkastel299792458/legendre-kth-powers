"""Collect results from out/ into out/summary.md (tables used in REPORT.md).
Usage: python -I summarize.py"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))  # works under python -I
import csv
import json

HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(HERE, 'out')
lines = []
P = lines.append

P('## Fixed-certificate per-piece thresholds (certificates\' own pieces / M / c / sigma*)\n')
P('| family | pieces with finite threshold | min threshold | binding piece (L) |')
P('|---|---|---|---|')
for fam in ('Z1', 'Z2'):
    fn = os.path.join(OUT, f'fixed_{fam}.csv')
    if not os.path.exists(fn):
        continue
    r = [x for x in csv.DictReader(open(fn)) if x['status'] == 'thr']
    for kind in 'SH':
        t = [x for x in r if x['kind'] == kind]
        if t:
            m = min(t, key=lambda x: float(x['thr_ok']))
            P(f"| {fam} ({'Prop S' if kind == 'S' else 'Prop H'}) | {len(t)} | {float(m['thr_ok']):.6f} | "
              f"[{float(m['L_a']):.3f}, {float(m['L_b']):.3f}] |")

P('\n## Re-optimised global thresholds (repair: narrower pieces, M in {2,3,4}, re-optimised c/sigma*, movable S/H junction)\n')
P('| family | closes at | fails at | binding L (failing ranges at the fail value) | confirm: all delta<1 / contiguous / max delta | S-range of cover |')
P('|---|---|---|---|---|---|')
for fam in ('Z1', 'Z2', 'optprof55', 'Z1_pubLW'):
    fn = os.path.join(OUT, f'reopt_{fam}.json')
    if not os.path.exists(fn):
        continue
    s = json.load(open(fn))
    c = s.get('confirm', {})
    where = s.get('holes_at_fail') or s.get('bad_at_fail') or s.get('holes') or []
    where = '; '.join(f"[{a:.1f}, {b:.1f}]" for a, b in where[:3])
    ok = s.get('ok', s.get('weak') if s['status'] == 'closes_at_weak' else None)
    fail = s.get('fail', s.get('strong') if s['status'] == 'fails_at_strong' else None)
    conf = f"{c.get('all_delta_lt_1')} / {c.get('contiguous_L1_to_1e8')} / {c.get('max_delta', float('nan')):.7f}" if c else ''
    sr = s.get('cover_S_range')
    sr = f"[{sr[0]:.2f}, {sr[1]:.2f}]" if sr else ''
    P(f"| {fam} | {ok} | {fail} | {where} | {conf} | {sr} |")

fn = os.path.join(OUT, 'bands.csv')
if os.path.exists(fn):
    P('\n## Band-localised requirement (re-optimised, rigorous)\n')
    P('| band v = log t | active | value used | smallest s that closes | weakest admissible constant on band | first failure (L) at s_fail |')
    P('|---|---|---|---|---|---|')
    for r in csv.DictReader(open(fn)):
        P(f"| ({float(r['v_lo']):.2f}, {float(r['v_hi']):.2f}] | {r['active_constant']} | {r['proof_value']} | "
          f"{r['s_ok']} (fails {r['s_fail']}) | {r['weakest_admissible_constant']} | {r['binding_L_ranges']} |")

fn = os.path.join(OUT, 'bands_z2.csv')
if os.path.exists(fn):
    P('\n## Littlewood band requirement: Z2 = z on the band only (19.62 elsewhere, Z1 = 4.896), re-optimised\n')
    P('| band v = log t | largest z that closes | smallest z that fails | first failure (L) |')
    P('|---|---|---|---|')
    for r in csv.DictReader(open(fn)):
        P(f"| ({float(r['v_lo']):g}, {float(r['v_hi']):g}] | {r['Z2_on_band_closes']} | {r['Z2_on_band_fails'] or '-'} | {r['binding_L_ranges'][:60]} |")
fn = os.path.join(OUT, 'priority_z2.json')
if os.path.exists(fn):
    P('\n## Priority models (v3 code)\n')
    P('| model | closes | full re-check (all delta<1 / contiguous / max delta at L) | failing / hole ranges |')
    P('|---|---|---|---|')
    for k, v in json.load(open(fn)).items():
        c = v.get('confirm')
        cs = f"{c['all_delta_lt_1']} / {c['contiguous_L1_to_1e8']} / {c['max_delta']:.7f} at {c['max_at_L']:.2f}" if c else ''
        hs = '; '.join(f"[{a:.1f}, {b:.1f}]" for a, b in (v['holes'][:2] or []))
        P(f"| {k}: {v['model']} | {v['closes']} | {cs} | {hs} |")

open(os.path.join(OUT, 'summary.md'), 'w', encoding='utf-8').write('\n'.join(lines) + '\n')
print('\n'.join(lines))
