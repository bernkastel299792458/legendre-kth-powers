"""Small numeric checks quoted in the report.
(1) KLN Lemma 3.2: minimum over t > 0 of a1 t^{1/6} log t + a2 versus max |zeta(1/2+it)| on [0,3]  (report M3).
(2) BTY: crossover height where the published Littlewood region (21.233) beats 1/(4.896 log t)  (report §3.5).
(3) Bellotti Table 2: every row hard-coded in proof/code (rigorous_smooth.LOW_ROWS_SRC, rigorous_hyb.BELLOTTI)
    against the arXiv v2 HTML extraction in papers/bellotti_table2_html.txt  (report §3.5).
Run:  python -B misc_checks.py"""
import sys
sys.dont_write_bytecode = True
import re
from pathlib import Path
from mpmath import mp, mpf, zeta, e, exp

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
mp.dps = 30

# (1)
m = -6 / e                                            # min of t^{1/6} log t, attained at t = e^{-6}
print('(1) KLN a1=0.63, a2=2.851: min bound =', mp.nstr(mpf('0.63') * m + mpf('2.851'), 10))
print('    JY  a1=0.77, a2=3.161: min bound =', mp.nstr(mpf('0.77') * m + mpf('3.161'), 10))
zmax = max((abs(zeta(mpf(1) / 2 + 1j * mpf(i) / 2000)), mpf(i) / 2000) for i in range(0, 6001))
print('    max |zeta(1/2+it)| on [0,3] =', mp.nstr(zmax[0], 10), 'at t =', mp.nstr(zmax[1], 4),
      ' (KLN argue with 1.461; HPY 2024 give 0.618 t^{1/6} log t for t >= 3)')

# (2)
v = exp(mpf('21.233') / mpf('4.896'))                # loglog t / (21.233 log t) >= 1/(4.896 log t)  <=>  log t >= this
print('(2) BTY crossover: log t =', mp.nstr(v, 8), '(BTY state exp(76.463); Lemma 1 covers t <= exp(76.47))')

# (3)
html = open(ROOT / 'papers' / 'bellotti_table2_html.txt', encoding='utf-8').read()
src_rows = []
for line in html.splitlines():
    p = line.strip().split('\t')
    if len(p) == 5 and re.fullmatch(r'0\.\d{4}', p[2]):
        def lg(s):
            s = s.replace('\\exp(', '').replace(')', '')
            return 'LOG3E12' if '10^{12}' in s else s
        C = p[3].replace('\\cdot 10^{', 'e').replace('}', '')
        src_rows.append((lg(p[0]), lg(p[1]), p[2].rstrip('0'), C, p[4]))
# last row is stated in the text of arXiv v2 (p. 27): N(sigma,T) <= 1.62e11 T^{1.448(1-sigma)},
# sigma in [0.985, 1], T in (exp(481958), exp(6.7e12)]
src_rows.append(('481958', '6.7e12', '0.985', '1.62e11', '1.448'))
code =(ROOT / 'proof' / 'code' / 'rigorous_smooth.py').read_text(encoding='utf-8')
code += (ROOT / 'proof' / 'code' / 'rigorous_hyb.py').read_text(encoding='utf-8')
code_rows = re.findall(r'\("([^"]+)", "([^"]+)", "(0\.\d+)", "([^"]+)", "([^"]+)"\)', code)
code_rows = [(a, b, c.rstrip('0'), C.replace('1.12e6', '1.12e6'), B) for a, b, c, C, B in code_rows]
norm = lambda r: (r[0], r[1], r[2], str(float(r[3])), str(float(r[4])))
missing = [r for r in code_rows if norm(r) not in {norm(s) for s in src_rows}]
print(f'(3) Bellotti rows: {len(src_rows)} in the arXiv v2 extraction, {len(code_rows)} hard-coded in proof/code;',
      'all hard-coded rows match' if not missing else f'MISMATCH: {missing}')
print('    (the last row, exp(481958)..exp(6.7e12), C=1.62e11, B=1.448, is stated in the text of arXiv v2, p. 27)')
