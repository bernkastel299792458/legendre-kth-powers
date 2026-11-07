import csv, math, sys
sys.path.insert(0,'.')
import lemmaA_d4 as A
rows=list(csv.DictReader(open('../phase0_bellotti/rows_reopt.csv')))
want=[29,50,70,80,90,110]
picked=[]
for h in want:
    cands=[r for r in rows if float(r['logT0'])<h<=float(r['logT1'])+1e-9 and 'Bopt=B_her;' in r['notes'] and r['zfr_input'].startswith('cl5.558691')]
    if not cands: continue
    r=min(cands,key=lambda r: float(r['C']))
    picked.append(r)
for r in picked:
    u,x,v=float(r['u']),float(r['x']),float(r['v']); L0,L1=float(r['logT0']),float(r['logT1'])
    tau=v/u; F=(1.084*(tau+1)+1.301*(1+tau*tau)-0.116)/(tau-1)
    d4_p0=math.exp((u-x)*L0)+3.09*F*x/(v-u)
    b,_=A.d4_upper(r['u'],r['v'],r['x'],L0,L1)
    print(f"{r['id']} [{L0},{L1}] a0={r['alpha0']} B={r['B']} C={r['C']} u={u} v={v} x={x}: d4_phase0={d4_p0:.2f}  d4_lemmaA<={A.f_up(b):.3f}  ratio={A.f_up(b)/d4_p0:.4f}   ({r['notes'][:12]})")
