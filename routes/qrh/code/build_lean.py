"""Compile every project Lean source and record kernel-audit evidence.

Default: use this project's .lake/packages, populated by lake update/cache get.
An optional --dependency-root borrows already built Mathlib dependencies READ
ONLY. All project outputs remain inside this package's own .lake directory.
No successful build is reported as an end-to-end QRH+CS formalization.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / 'lean'
AUDIT = ROOT / 'audit'

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def without_comments(text):
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            if not depth: out.append(text[i])
            i += 1
    return ''.join(out)

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dependency-root', type=Path)
    ap.add_argument('--lean', type=Path)
    args = ap.parse_args()
    config = tomllib.loads((LEAN_ROOT / 'lakefile.toml').read_text(encoding='utf-8'))
    lean_options = config.get('leanOptions', {})
    option_args = ['-D' + key + '=' + (str(value).lower() if isinstance(value, bool) else str(value))
                   for key, value in lean_options.items()]
    deps = (args.dependency_root or LEAN_ROOT / '.lake/packages').resolve()
    if not deps.is_dir():
        raise SystemExit('Run lake update and lake exe cache get in lean/, or supply --dependency-root.')
    lean = str(args.lean) if args.lean else shutil.which('lean')
    if not lean:
        fallback = Path.home()/'.elan/bin'/('lean.exe' if os.name == 'nt' else 'lean')
        if fallback.exists(): lean = str(fallback)
    if not lean: raise SystemExit('Lean/elan not found.')
    build = LEAN_ROOT / '.lake/build/lib/lean'
    build.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    libraries = [build, LEAN_ROOT]
    libraries += [p/'.lake/build/lib/lean' for p in sorted(deps.iterdir())
                  if (p/'.lake/build/lib/lean').is_dir()]
    env['LEAN_PATH'] = os.pathsep.join(map(str, libraries))
    version = subprocess.run([lean, '--version'], cwd=LEAN_ROOT, env=env,
                             capture_output=True, text=True, encoding='utf-8', check=True).stdout.strip()
    if '4.36.0-rc2' not in version:
        raise SystemExit('Wrong toolchain: ' + version)
    expected = json.loads((LEAN_ROOT/'lake-manifest.json').read_text(encoding='utf-8-sig'))
    revisions = {}
    for package in expected['packages']:
        path = deps/package['name']
        rev = subprocess.run(['git','-C',str(path),'rev-parse','HEAD'],capture_output=True,
                             text=True,encoding='utf-8',check=True).stdout.strip()
        if rev != package['rev']: raise SystemExit('Dependency revision mismatch: '+package['name'])
        revisions[package['name']] = rev
    sources = {'.'.join(p.relative_to(LEAN_ROOT).with_suffix('').parts):p
               for p in LEAN_ROOT.rglob('*.lean') if '.lake' not in p.parts}
    dependencies = {}
    for module,path in sources.items():
        text = without_comments(path.read_text(encoding='utf-8'))
        bad = re.search(r'\b(sorry|admit|axiom|native_decide)\b', text)
        if bad: raise SystemExit(f'Forbidden local proof shortcut: {module}: {bad.group()}')
        imports = re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+([\w.]+)', text, re.M)
        dependencies[module] = [m for m in imports if m in sources]
    ordered, active, done = [], set(), set()
    def visit(m):
        if m in done: return
        if m in active: raise ValueError('Cyclic local import: '+m)
        active.add(m)
        for d in dependencies[m]: visit(d)
        active.remove(m);done.add(m);ordered.append(m)
    for m in sorted(sources): visit(m)
    AUDIT.mkdir(exist_ok=True)
    rows, outputs = [], []
    started = time.perf_counter()
    for index,module in enumerate(ordered,1):
        path = sources[module]
        relative = path.relative_to(LEAN_ROOT)
        target = build/relative.with_suffix('.olean')
        target.parent.mkdir(parents=True,exist_ok=True)
        before = time.perf_counter()
        run = subprocess.run([lean,*option_args,'-o',str(target),relative.as_posix()],cwd=LEAN_ROOT,env=env,
                             capture_output=True,text=True,encoding='utf-8')
        output = run.stdout + run.stderr
        outputs.append(f'=== {module} ===\n'+output)
        rows.append(dict(module=module,source_sha256=digest(path),exit_code=run.returncode,
                         seconds=round(time.perf_counter()-before,3)))
        print(f'{index}/{len(ordered)} '+('PASS ' if run.returncode==0 else 'FAIL ')+module,flush=True)
        if run.returncode:
            (AUDIT/'lean_build.log').write_text('\n'.join(outputs),encoding='utf-8')
            print(output,flush=True)
            raise SystemExit(run.returncode)
        if module == 'LegendreK6.Audit':
            for forbidden in ['sorryAx','Lean.ofReduceBool']:
                if forbidden in output: raise SystemExit('Unexpected axiom: '+forbidden)
            (AUDIT/'kernel_axioms.txt').write_text(output,encoding='utf-8')
    (AUDIT/'lean_build.log').write_text('\n'.join(outputs),encoding='utf-8')
    result=dict(status='ALL_PRESENT_LEAN_MODULES_COMPILED',end_to_end_H1_H2_formalization=False,
                version=version,lean_options=lean_options,created=datetime.now(timezone.utc).isoformat(),
                elapsed_seconds=round(time.perf_counter()-started,3),modules=rows,
                dependency_revisions=revisions,
                dependency_cache_mode='read-only external cache' if args.dependency_root else 'project cache',
                scope='All local source modules compiled; the assembly theorem still takes explicit analytic segment conclusions as parameters.')
    (AUDIT/'lean_build_report.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'],flush=True)
    print('END_TO_END_H1_H2_FORMALIZATION=false',flush=True)

if __name__=='__main__': main()
