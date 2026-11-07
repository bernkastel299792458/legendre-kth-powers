"""Summaries of frontier_raw.json (after `python frontier.py merge 12`).  Writes frontier_summary.txt."""
import sys, os, json
from decimal import Decimal
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from beltables import rows as her_rows
HERE = os.path.dirname(os.path.abspath(__file__))

def main():
    res = [q for q in json.load(open(os.path.join(HERE, 'frontier_raw.json'))) if q.get('ok')]
    her = {r['L0']: r for r in her_rows()}
    out = []
    def pick(L0, L1, a0, status, Blab, lam1):
        c = [q for q in res if q['L0'] == L0 and q['L1'] == L1 and q['a0'] == a0 and q['status'] == status
             and q['Blab'] == Blab and ((q['row']['lam'] == '1') == lam1)]
        return c[0] if c else None
    ivs = []
    for q in res:
        k = (q['L0'], q['L1'])
        if k not in ivs:
            ivs.append(k)
    out.append("C_new / C_printed(her row containing the interval), same B as her row, her alpha0.")
    out.append("lam* = optimised box height (own modification); lam=1 = Bellotti's box height; ref = refereed zfr; pre = with 4.896")
    out.append(f"{'interval':>14} {'her row':>12} {'a0':>6} {'B':>7} {'C_pr':>10} | {'ref lam*':>10} {'ratio':>6} {'lam':>6} | {'pre lam*':>10} {'ratio':>6} | {'ref lam=1':>10} {'ratio':>6} | {'pre lam=1':>10} {'ratio':>6}")
    for (L0, L1) in ivs:
        hr = her[[q for q in res if q['L0'] == L0 and q['L1'] == L1][0]['hr']]
        a0 = hr['a0']; Cpr = float(hr['Cpr'])
        a = pick(L0, L1, a0, 'refereed', 'B_her', False)
        b = pick(L0, L1, a0, 'audited preprint', 'B_her', False)
        c = pick(L0, L1, a0, 'refereed', 'B_her', True)
        d = pick(L0, L1, a0, 'audited preprint', 'B_her', True)
        f = lambda q: (f"{q['C']:10.5g} {q['C']/Cpr:6.3f}" if q else f"{'-':>10} {'-':>6}")
        out.append(f"{L0+'-'+L1:>14} {hr['L0']+'-'+hr['L1']:>12} {a0:>6} {hr['Bpr']:>7} {Cpr:10.5g} | {f(a)} {(a['row']['lam'] if a else '-'):>6} | {f(b)} | {f(c)} | {f(d)}")
    out.append("")
    out.append("Frontier per interval (refereed zfr unless noted; lam*): B -> C for each alpha0")
    for (L0, L1) in ivs:
        line = f"{L0+'-'+L1:>14}: "
        for st in ('refereed', 'audited preprint'):
            for a0 in sorted({q['a0'] for q in res if q['L0'] == L0 and q['L1'] == L1}, reverse=True):
                opts = [q for q in res if q['L0'] == L0 and q['L1'] == L1 and q['a0'] == a0 and q['status'] == st and q['row']['lam'] != '1']
                if not opts:
                    continue
                opts.sort(key=lambda q: float(q['B']))
                line += f" [{'ref' if st=='refereed' else 'pre'} a0={a0}: " + ", ".join(f"B={float(q['B']):.3f}:C={q['C']:.4g}" for q in opts) + "]"
        out.append(line)
    txt = "\n".join(out)
    open(os.path.join(HERE, 'frontier_summary.txt'), 'w').write(txt + "\n")
    print(txt)

if __name__ == '__main__':
    main()
