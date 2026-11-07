"""Summary of v2_raw.json (+ v2h_raw.json): C/C_printed at B_her, lowest feasible B, B_edge; per lemma set."""
import sys, os, json
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from frontier import her_row_mid
HERE = os.path.dirname(os.path.abspath(__file__))

def main(fn='v2_raw.json'):
    res = [q for q in json.load(open(os.path.join(HERE, fn))) if q.get('ok')]
    ivs = []
    for q in res:
        k = (q['row']['L0'], q['row']['L1'])
        if k not in ivs:
            ivs.append(k)
    out = [f"{'interval':>14} {'C_pr':>9} {'B_her':>6} | {'ABC B_her':>9} {'ratio':>7} {'lam':>3} | {'BC B_her':>9} {'ratio':>7} | {'C B_her':>9} {'ratio':>7} | "
           f"{'ABC lowest B':>18} | {'ABC B_edge':>18} | {'ABC pre B_her':>12} | {'ABC a0=0.98 B_her':>17}"]
    for (L0, L1) in ivs:
        if fn.startswith('v2h'):
            import high
            hr = high.her_row_containing(L0, L1)
        else:
            hr = her_row_mid(L0, L1)
        Cp = float(hr['Cpr'])
        def pick(lems, Blab, a0=None, st='refereed'):
            c = [q for q in res if (q['row']['L0'], q['row']['L1']) == (L0, L1) and q['row']['lems'] == lems and q['Blab'] == Blab
                 and q.get('status', 'refereed') == st and (a0 is None or q['row']['a0'] == a0)]
            return c[0] if c else None
        a = pick('lemA,lemB,lemC', 'B_her', hr['a0']); b = pick('lemB,lemC', 'B_her', hr['a0'] if not fn.startswith('v2h') else None)
        c = pick('lemC', 'B_her', hr['a0'] if not fn.startswith('v2h') else None)
        low = sorted([q for q in res if (q['row']['L0'], q['row']['L1']) == (L0, L1) and q['row']['lems'] == ('lemA,lemB,lemC' if not fn.startswith('v2h') else 'lemB,lemC')
                      and q.get('status', 'refereed') == 'refereed'], key=lambda q: float(q['B']))
        e = pick('lemA,lemB,lemC' if not fn.startswith('v2h') else 'lemB,lemC', 'B_edge', hr['a0'] if not fn.startswith('v2h') else None)
        p = pick('lemA,lemB,lemC', 'B_her', hr['a0'], 'audited preprint')
        z = pick('lemA,lemB,lemC', 'B_her', '0.98')
        f = lambda q: (f"{q['C']:9.4g} {q['C']/Cp:7.4f}" if q else f"{'-':>9} {'-':>7}")
        out.append(f"{L0+'-'+L1:>14} {Cp:9.4g} {hr['Bpr']:>6} | {f(a)} {(a['row']['lam'] if a else '-'):>3} | {f(b)} | {f(c)} | "
                   + (f"B={float(low[0]['B']):6.3f} C={low[0]['C']:8.3g}" if low else f"{'-':>18}") + " | "
                   + (f"B={float(e['B']):6.3f} C={e['C']:8.3g}" if e else f"{'-':>18}") + " | "
                   + (f"{p['C']:12.4g}" if p else f"{'-':>12}") + " | " + (f"{z['C']:17.4g}" if z else f"{'-':>17}"))
    txt = "\n".join(out)
    open(os.path.join(HERE, fn.replace('_raw.json', '_summary.txt')), 'w').write(txt + "\n")
    print(txt)

if __name__ == '__main__':
    main(sys.argv[1] if len(sys.argv) > 1 else 'v2_raw.json')
