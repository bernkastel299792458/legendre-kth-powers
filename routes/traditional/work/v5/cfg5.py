"""Shared configuration for v5 scripts: parse key=value arguments and install the inputs."""
import os
import sys
import json
import hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import phi5  # noqa: E402
import rigorous_smooth as RS  # noqa: E402
from rigorous_hyb import A  # noqa: E402

DEFAULTS = dict(CS='0', ROWS='', ROWS_KEEP_ORIG='1', BANDS='', Z1='4.896', Z2='21.233', Z3='54.004',
                KLN='17.4193,2.2311', MS='2,3', L3='100000000', TAG='', ROWS_STATUS='', KLNF='JY', PROVISIONAL='0', CSBP='0', CBANDS='', KROWS='', KFORMS='JY52')


def parse(argv):
    P = dict(DEFAULTS)
    for a in argv:
        k_, v_ = a.split('=', 1)
        P[k_] = v_
    return P


def setup(P):
    phi5.CFG['Z1'], phi5.CFG['Z2'], phi5.CFG['Z3'] = A(P['Z1']), A(P['Z2']), A(P['Z3'])
    RS.ZFR['v5'] = (A(P['Z1']), A(P['Z2']), A(P['Z3']))
    RS.CFG['zfr'] = 'v5'
    RS.CFG['full_table'] = True
    b1, b3 = P['KLN'].split(',')
    phi5.CFG['KLN'] = (A(b1), A(b3))
    forms = []
    for f in P['KLNF'].split(','):
        if f == 'JY':
            forms.append((A(b1), A(b3), 3, 2))
        elif f == 'CSB':
            forms.append(phi5.CSB)
        elif f == 'CSB5161':
            forms.append(phi5.CSB5161)
    phi5.CFG['KLNS'] = forms
    phi5.CFG['CS'] = P['CS'] == '1'
    phi5.CFG['CSBP'] = P.get('CSBP', '0') == '1'
    phi5.CFG['CSB_B4'] = P.get('CSB_B4', '0.5161')
    rows = phi5.original_rows() if P['ROWS_KEEP_ORIG'] == '1' else []
    st = set(x for x in P.get('ROWS_STATUS', '').split(',') if x) or None
    for pth in [x for x in P['ROWS'].split(';') if x]:
        rows += [r for r in phi5.load_rows_csv(pth, statuses=st)
                 if P['PROVISIONAL'] == '1' or 'UNSURE' not in r[5]]
    phi5.CFG['ROWS'] = rows
    phi5.CFG['BANDS'] = phi5.load_bands_csv(P['BANDS']) if P['BANDS'] else []
    phi5.CFG['CBANDS'] = phi5.load_bands_csv(P['CBANDS'], col='Z1') if P.get('CBANDS') else []
    if P.get('KROWS'):
        forms = set(P.get('KFORMS', 'JY52').split(','))
        kr = phi5.load_kln_rows(P['KROWS'], forms) + [r for r in phi5.JY_TOP if r[4] in forms]
        phi5.CFG['KROWS'] = kr
    else:
        phi5.CFG['KROWS'] = []
    phi5.CFG['VER'] = phi5.CFG.get('VER', 0) + 1
    phi5._RUNMIN.clear()
    phi5.install()


def tail_check(P, L, k):
    """Lemma T with sigma_1 = 0.93 when low-sigma KLN rows are configured (B3 = 2.608 = C2(0.93)), else as in v4."""
    from fractions import Fraction
    import tail5
    if P.get('KROWS'):
        return tail5.check(Fraction(L), k=k, verbose=False, s1=Fraction(93, 100), B1s="17.4193", B3s="2.608", Z3=P['Z3'])
    return tail5.check(Fraction(L), k=k, verbose=False, Z3=P['Z3'])


def fingerprint(P):
    """Config plus SHA256 of every input file, for the certificate sidecar."""
    files = [x for x in P['ROWS'].split(';') if x] + ([P['BANDS']] if P['BANDS'] else []) + ([P['CBANDS']] if P.get('CBANDS') else []) + ([P['KROWS']] if P.get('KROWS') else [])
    here = os.path.dirname(os.path.abspath(__file__))
    files += [os.path.join(here, f) for f in ('phi5.py', 'rig5.py', 'cfg5.py', 'tail5.py')]
    return dict(config=P, sha256={f: hashlib.sha256(open(f, 'rb').read()).hexdigest() for f in files})


def dump(P, path):
    with open(path, 'w', encoding='utf-8') as f:
        json.dump(fingerprint(P), f, indent=1)
