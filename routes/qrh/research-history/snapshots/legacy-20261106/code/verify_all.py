"""Replay the partial k=4 proof modules; never label the current gap proved."""
from __future__ import annotations

import hashlib
import json
import subprocess
import sys
from datetime import datetime, timezone, timedelta
from fractions import Fraction
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]


def main():
    runs=[]
    scripts=[ROOT/'code'/name for name in (
        'certify_lower_range.py','k4_bandlimited_round3.py','k4_selberg_round4.py',
        'certify_k4_monotone_round3.py','certify_k4_round3.py',
        'certify_smooth_extension.py','certify_smooth_segment.py','certify_tail_cs.py')]
    scripts.append(ROOT/'theory_round5'/'rebase_density.py')
    for path in scripts:
        script=path.name
        completed=subprocess.run([sys.executable,'-B','-X','utf8',str(path),'--verify'],
            cwd=ROOT,capture_output=True,text=True,encoding='utf-8',check=True)
        runs.append(dict(script=script,passed=True,
                         script_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                         output=completed.stdout.strip()))
        print(f'PASS {script}',flush=True)
    files={name:ROOT/'results'/name for name in (
        'lower_range_certificate.json','tail_cs_certificate.json',
        'smooth_segment_certificate.json','smooth_extension_certificate.json',
        'k4_bandlimited_round3.json','k4_monotone_round3_certificate.json',
        'k4_round3_certificate.json','k4_selberg_round4.json')}
    files['rebased_density_certificate.json']=ROOT/'theory_round5'/'rebased_density_certificate.json'
    lower=json.loads(files['lower_range_certificate.json'].read_text(encoding='utf-8'))
    tail=json.loads(files['tail_cs_certificate.json'].read_text(encoding='utf-8'))
    smooth=json.loads(files['smooth_segment_certificate.json'].read_text(encoding='utf-8'))
    extension=json.loads(files['smooth_extension_certificate.json'].read_text(encoding='utf-8'))
    bandlimited=json.loads(files['k4_bandlimited_round3.json'].read_text(encoding='utf-8'))
    monotone=json.loads(files['k4_monotone_round3_certificate.json'].read_text(encoding='utf-8'))
    round3=json.loads(files['k4_round3_certificate.json'].read_text(encoding='utf-8'))
    selberg=json.loads(files['k4_selberg_round4.json'].read_text(encoding='utf-8'))
    rebased=json.loads(files['rebased_density_certificate.json'].read_text(encoding='utf-8'))
    Llow=Fraction(lower['coverage']['target_L_numerator'],lower['coverage']['target_L_denominator'])
    Lstart,Lend=map(Fraction,smooth['log_x_interval'])
    Lextended,Ljoin=map(Fraction,extension['log_x_interval'])
    Ltail=Fraction(tail['parameters_exact']['L0'])
    if Lend<Ltail:
        raise RuntimeError('Uncovered gap between certified smooth segment and tail')
    if not Lextended < Ljoin == Lstart:
        raise RuntimeError('Extension does not join the original smooth interval exactly')
    if not lower['coverage']['all_n_with_4_log_n_le_target_L_covered']:
        raise RuntimeError('Lower-range target not verified')
    Lband0=Fraction(bandlimited['exact_parameters']['L_min'])
    Lband1=Fraction(bandlimited['exact_parameters']['L_max'])
    Lsel0=Fraction(selberg['exact_parameters']['L_min'])
    Lsel1=Fraction(selberg['exact_parameters']['L_max'])
    Lnew=Fraction(monotone['log_x_lower'])
    Lround3,Lround3end=map(Fraction,round3['log_x_interval'])
    if not Lband0<=Llow<Lband1:
        raise RuntimeError('Bandlimited segment does not join verified lower range')
    if not Lsel0==Lband1<Lsel1:
        raise RuntimeError('Selberg segment does not join preceding lower segment')
    if not Lnew==Lround3<Lround3end==Lextended:
        raise RuntimeError('New infinite tail and redundant finite segment disagree')
    if monotone['status']!='VERIFIED_ANALYTIC_TAIL':
        raise RuntimeError('New analytic tail not verified')
    Lrebased=Fraction(rebased['L0'])
    if not (Lrebased < Lnew and rebased['point']['passed']
            and rebased['status']=='POINT_AND_ANALYTIC_RATES_CHECKED'
            and Fraction(rebased['point']['delta_upper_rational']) < 1
            and Fraction(rebased['n_lower_log'])==Lrebased/4):
        raise RuntimeError('Rebased density tail metadata mismatch')
    Lnew=Lrebased
    # Exact integer coverage is bounded by the real-variable lower segment.
    from flint import arb,ctx
    ctx.prec=256
    Llower_end=arb(Lsel1.numerator)/Lsel1.denominator
    nball=(Llower_end/4).exp()
    nmax=nball.floor().unique_fmpz()
    if nmax is None:
        raise RuntimeError('Lower segment integer endpoint unresolved')
    nmax=int(nmax)
    if not (arb(nmax).log()*4<=Llower_end
            and arb(nmax+1).log()*4>Llower_end):
        raise RuntimeError('Lower segment integer endpoint not certified')
    if nmax!=int(selberg['exact_parameters']['n_max_inclusive']):
        raise RuntimeError('Selberg integer endpoint metadata mismatch')
    remaining=[] if Lsel1>=Lnew else [[str(Lsel1),str(Lnew)]]
    result=dict(
        status='PARTIAL_MODULES_VERIFIED_NOT_FULL_K4' if remaining else 'REQUIRES_FINAL_MATHEMATICAL_REVIEW',
        full_k4_proved=False,
        created=datetime.now(timezone(timedelta(hours=8))).isoformat(),
        scope='Numerical verification of documented analytic lemmas under QRH and cited literature inputs; not Lean or external peer review.',
        verified_small_n_max=nmax,
        original_lower_n_max=lower['coverage']['n_max_inclusive'],
        verified_lower_real_x_log_interval=[str(Lband0),str(Lsel1)],
        verified_real_x_lower_log=str(Lnew),
        verified_large_n_lower_log=str(Lnew/4),
        current_large_range_inputs=rebased['inputs'],
        conservative_uncovered_log_x_intervals=remaining,
        runs=runs,
        certificate_hashes={name:hashlib.sha256(path.read_bytes()).hexdigest() for name,path in files.items()},
        script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
    out=ROOT/'results'/'verification_summary.json'
    out.write_text(json.dumps(result,indent=2,ensure_ascii=False)+'\n',encoding='utf-8')
    print(result['status'])
    print(f'Conservative remaining gap in log(x): {remaining}')


if __name__=='__main__':
    main()
