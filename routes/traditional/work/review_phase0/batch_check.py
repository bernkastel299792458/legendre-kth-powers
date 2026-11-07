"""Run the referee's independent evaluator (indep_C.py) on rows of a Phase-0 CSV.
usage: python batch_check.py rows.csv [step] [offset] [mode]   (mode: joint | decoupled)
Checks per row: C_ref (sup over the row) <= C_csv, B >= 2x, c1>0 & c1^2-c5>0 on every piece,
U=T^u>=100, r0<1/2, x>u, status consistent with zfr inputs.  Prints one line per row, summary at end."""
import sys, csv, math, time
from decimal import Decimal
from flint import arb
import indep_C as I

path = sys.argv[1]
step = int(sys.argv[2]) if len(sys.argv) > 2 else 1
off = int(sys.argv[3]) if len(sys.argv) > 3 else 0
mode = sys.argv[4] if len(sys.argv) > 4 else 'joint'
I.DECOUPLED = (mode == 'decoupled')
if len(sys.argv) > 5: I.PIECE = float(sys.argv[5]); I.NMAX = 100000
recs = list(csv.DictReader(open(path)))
nbad = 0; worst = 0; n = 0
t0 = time.time()
for idx in range(off, len(recs), step):
    rec = recs[idx]; row = I.parse(rec)
    msgs = []
    if Decimal(rec['B']) < 2 * Decimal(rec['x']): msgs.append('B<2x')
    if not (Decimal(rec['x']) > Decimal(rec['u'])): msgs.append('x<=u')
    L0 = arb(rec['logT0']).max(I.LOG3E12)
    if not bool(arb(rec['u']) * L0 >= arb(100).log()): msgs.append('U<100')
    rho = (1 + arb(row['lam']) ** 2 / 4).sqrt()
    if not bool(rho * (1 - arb(rec['alpha0'])) < arb('0.5')): msgs.append('r0>=1/2')
    pre = 'cl4.896' in row['zfr']
    if pre and rec['status'] != 'audited preprint': msgs.append('status')
    if (not pre) and rec['status'] != 'refereed': msgs.append('status')
    try:
        w = I.C_row(row)
        Cref = float(w['C'].upper())
        if not w['allok']: msgs.append('c1/den<=0 somewhere')
        if not bool(arb(rec['C']) >= arb(w['C'].upper())): msgs.append('C_csv < C_ref')
    except AssertionError as e:
        Cref = float('nan'); msgs.append('assert:' + str(e))
    rat = Cref / float(rec['C'])
    worst = max(worst, rat) if rat == rat else worst
    n += 1
    if msgs: nbad += 1
    print(f"{rec['id']} [{rec['logT0']},{rec['logT1']}] a0={rec['alpha0']} lam={row['lam']} C_csv={rec['C']} C_ref={Cref:.6g} ratio={rat:.5f} {'FAIL ' + ','.join(msgs) if msgs else 'ok'}",
          flush=True)
print(f"SUMMARY {path} mode={mode}: {n} rows checked, {nbad} with problems, max ratio C_ref/C_csv = {worst:.6f}, {time.time()-t0:.0f}s")
