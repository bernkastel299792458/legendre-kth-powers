"""Run the final proof-dependency diagnostic against one exact full build.

This checks current source/artifact hashes before and after the diagnostic.
It uses the build's isolated LEAN_PATH, never a stale development output tree.
The diagnostic inspects proof terms; Lean's kernel remains the proof checker.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / 'lean'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_build(report):
    if report['status'] != 'ALL_PRESENT_LEAN_MODULES_COMPILED':
        raise ValueError('A successful full build is required')
    if Path(report['source_root']).resolve() != LEAN_ROOT.resolve():
        raise ValueError('Build report belongs to a different source checkout')
    sources = {'.'.join(p.relative_to(LEAN_ROOT).with_suffix('').parts): p
               for p in LEAN_ROOT.rglob('*.lean') if '.lake' not in p.parts}
    rows = report['modules']
    if len(rows) != len(sources) or {r['module'] for r in rows} != set(sources):
        raise ValueError('Current module inventory differs from the full build')
    build_root = Path(report['output_root']).resolve()
    if Path(report['lean_path'][0]).resolve() != build_root:
        raise ValueError('Build library is not first in the recorded search path')
    for row in rows:
        if row['status'] != 'PASS' or row['exit_code'] != 0:
            raise ValueError('Unsuccessful module: ' + row['module'])
        if digest(sources[row['module']]) != row['source_sha256_final']:
            raise ValueError('Changed source: ' + row['module'])
        artifact = Path(row['olean']).resolve()
        if not artifact.is_relative_to(build_root):
            raise ValueError('Artifact outside the selected build root')
        if digest(artifact) != row['olean_sha256_final']:
            raise ValueError('Changed artifact: ' + row['module'])
    for path, key in [('lakefile.toml', 'lakefile_sha256'),
                      ('lake-manifest.json', 'lake_manifest_sha256')]:
        if digest(LEAN_ROOT / path) != report[key]:
            raise ValueError('Changed build configuration: ' + path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--build-report', type=Path, required=True)
    parser.add_argument('--output-dir', type=Path, required=True)
    args = parser.parse_args()
    report_bytes = args.build_report.read_bytes()
    report_sha256 = hashlib.sha256(report_bytes).hexdigest()
    report = json.loads(report_bytes.decode('utf-8-sig'))
    check_build(report)
    diagnostic = ROOT / 'audit/FinalDependencies.lean'
    before = digest(diagnostic)
    environment = os.environ.copy()
    environment['LEAN_PATH'] = os.pathsep.join(report['lean_path'])
    command = [report['lean_executable'], *report['option_args'],
               '../audit/FinalDependencies.lean']
    started = time.monotonic()
    run = subprocess.run(command, cwd=LEAN_ROOT, env=environment,
                         capture_output=True, text=True, encoding='utf-8')
    output = run.stdout + run.stderr
    errors = []
    if run.returncode:
        errors.append('Lean diagnostic failed')
    if 'FINAL_K6_REQUIRED_PROOF_DEPENDENCIES_PRESENT' not in output:
        errors.append('Actual proof dependency marker is missing')
    for forbidden in ['sorryAx', 'Lean.ofReduceBool']:
        if forbidden in output:
            errors.append('Unexpected axiom: ' + forbidden)
    for declaration in ['sixth_powers_from_named_inputs', 'sixth_power_short_from_named_inputs',
                        'all_94_cells_actual_prime_intervals', 'all_60_far_cells_actual_prime_intervals']:
        if f"'LegendreK6.{declaration}' depends on axioms: [propext, Classical.choice, Quot.sound]" not in output:
            errors.append('Expected axiom report absent: ' + declaration)
    if digest(diagnostic) != before:
        errors.append('Diagnostic source changed during the run')
    if digest(args.build_report) != report_sha256:
        errors.append('Build report changed during the run')
    try:
        check_build(report)
    except Exception as error:
        errors.append(str(error))
    args.output_dir.mkdir(parents=True, exist_ok=True)
    text_path = args.output_dir / 'final_dependencies.txt'
    text_path.write_text(output, encoding='utf-8', newline='\n')
    result = dict(status='FINAL_K6_DEPENDENCY_AUDIT_PASSED' if not errors else 'AUDIT_FAILED',
        created=datetime.now(timezone.utc).isoformat(), exit_code=run.returncode,
        seconds=round(time.monotonic()-started, 3), errors=errors,
        command=command, cwd=str(LEAN_ROOT), lean_path=report['lean_path'],
        build_report=str(args.build_report.resolve()), build_report_sha256=report_sha256,
        diagnostic_source_sha256=before, output_sha256=digest(text_path),
        checked_modules=len(report['modules']),
        scope='Complete downstream k=6 proof relative to seven individually named external inputs; '
              'not a re-proof of those inputs or a theorem assuming only QRH and CS.')
    (args.output_dir / 'final_dependency_report.json').write_text(
        json.dumps(result, indent=2)+'\n', encoding='utf-8', newline='\n')
    print(result['status'])
    print('CHECKED_MODULES=' + str(result['checked_modules']))
    for error in errors:
        print(error)
    return 1 if errors else 0


if __name__ == '__main__':
    raise SystemExit(main())
