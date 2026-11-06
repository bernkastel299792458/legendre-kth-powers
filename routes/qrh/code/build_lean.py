"""Compile project Lean modules and preserve a reproducible compilation record.

Use --jobs for dependency-safe parallelism and --build-root for an isolated
output tree. Third-party dependencies are read-only. Reports are written to a
new run directory, never over an existing milestone report. Compilation is
not a declaration of mathematical scope; consult FORMALIZATION_STATUS.md and the audits.
"""
from __future__ import annotations

import argparse
from concurrent.futures import FIRST_COMPLETED, ThreadPoolExecutor, wait
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import threading
import time
import tomllib

ROOT = Path(__file__).resolve().parents[1]
LEAN_ROOT = ROOT / 'lean'
AUDIT = ROOT / 'audit'


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def optional_digest(path):
    try:
        return digest(path) if path.is_file() else None
    except OSError:
        return None


def utc_now():
    return datetime.now(timezone.utc).isoformat()


def without_comments(text):
    """Mask nested Lean comments, preserving newlines for import parsing."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.append('  ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            out.append('  ')
            i += 2
        elif not depth and text.startswith('--', i):
            end = text.find('\n', i)
            end = len(text) if end < 0 else end
            out.append(' ' * (end - i))
            i = end
        else:
            out.append(text[i] if not depth or text[i] == '\n' else ' ')
            i += 1
    if depth:
        raise ValueError('Unterminated Lean block comment')
    return ''.join(out)


def source_graph(lean_root, requested):
    """Return a deterministic topological order of the selected local closure."""
    sources = {}
    for directory, folders, files in os.walk(lean_root):
        folders[:] = sorted(folder for folder in folders if folder not in {'.lake', '.git'})
        for filename in sorted(files):
            if filename.endswith('.lean'):
                path = Path(directory) / filename
                sources['.'.join(path.relative_to(lean_root).with_suffix('').parts)] = path
    unknown = sorted(set(requested) - sources.keys())
    if unknown:
        raise ValueError('Unknown local module(s): ' + ', '.join(unknown))
    dependencies, hashes = {}, {}
    for module, path in sources.items():
        raw = path.read_bytes()
        hashes[module] = hashlib.sha256(raw).hexdigest()
        text = without_comments(raw.decode('utf-8-sig'))
        imports = []
        for header in re.findall(r'^\s*(?:(?:public|meta)\s+)*import\s+([^\n]+)', text, re.M):
            for name in header.split():
                if not re.fullmatch(r'[\w]+(?:\.[\w]+)*', name):
                    raise ValueError(f'Unsupported import syntax in {module}: {header!r}')
                if name in sources:
                    imports.append(name)
        dependencies[module] = sorted(set(imports))
    ordered, active, done = [], set(), set()

    def visit(module):
        if module in done:
            return
        if module in active:
            raise ValueError('Cyclic local import: ' + module)
        active.add(module)
        for dependency in dependencies[module]:
            visit(dependency)
        active.remove(module)
        done.add(module)
        ordered.append(module)

    for module in sorted(set(requested) if requested else sources):
        visit(module)
    for module in ordered:
        text = without_comments(sources[module].read_text(encoding='utf-8-sig'))
        bad = re.search(r'\b(?:sorry|admit|axiom|native_decide|Lean\.ofReduceBool)\b|'
                        r'\bdecide\s*\+\s*native\b', text)
        if bad:
            raise ValueError(f'Forbidden local proof shortcut: {module}: {bad.group()}')
    return sources, dependencies, hashes, ordered


def reject_cache_output(path, dependency_root):
    """Never create project outputs or reports in the borrowed dependency tree."""
    if path == dependency_root or path.is_relative_to(dependency_root):
        raise ValueError('Output path is inside the read-only dependency cache: ' + str(path))


class Compiler:
    def __init__(self, lean, options, lean_root, build_root, environment, sources, hashes):
        self.lean = lean
        self.options = options
        self.lean_root = lean_root
        self.build_root = build_root
        self.environment = environment
        self.sources = sources
        self.hashes = hashes
        self.lock = threading.Lock()
        self.processes = set()
        self.stopping = False

    def terminate_owned(self):
        """Interrupt only subprocesses created by this build, never other sessions."""
        with self.lock:
            self.stopping = True
            processes = list(self.processes)
        for process in processes:
            if process.poll() is None:
                process.terminate()
        for process in processes:
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                process.kill()

    def compile(self, module):
        path = self.sources[module]
        relative = path.relative_to(self.lean_root)
        target = self.build_root / relative.with_suffix('.olean')
        command = [self.lean, *self.options, '-o', str(target), relative.as_posix()]
        row = dict(module=module, source=str(path), source_relative=relative.as_posix(),
                   source_sha256_discovered=self.hashes[module], source_sha256_before=None,
                   source_sha256_after=None, source_unchanged=False, olean=str(target),
                   olean_sha256=None, command=command, cwd=str(self.lean_root),
                   started_at=utc_now(), exit_code=None, status='FAILED', errors=[])
        started = time.perf_counter()
        output = ''
        process = None
        try:
            row['source_sha256_before'] = digest(path)
            if row['source_sha256_before'] != self.hashes[module]:
                raise ValueError('Source changed after dependency discovery; refusing stale scheduling')
            target.parent.mkdir(parents=True, exist_ok=True)
            row['olean_existed_before'] = target.is_file()
            row['olean_sha256_before'] = optional_digest(target)
            with self.lock:
                if self.stopping:
                    raise RuntimeError('Build interrupted before subprocess start')
                process = subprocess.Popen(command, cwd=self.lean_root, env=self.environment,
                                           stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                                           text=True, encoding='utf-8', errors='replace')
                self.processes.add(process)
            output, _ = process.communicate()
            row['exit_code'] = process.returncode
            if process.returncode != 0:
                row['errors'].append(f'Lean exited with code {process.returncode}')
            if module == 'LegendreK6.Audit':
                for forbidden in ('sorryAx', 'Lean.ofReduceBool'):
                    if forbidden in output:
                        row['errors'].append('Unexpected audit axiom: ' + forbidden)
        except Exception as error:
            row['errors'].append(f'{type(error).__name__}: {error}')
        finally:
            if process is not None:
                with self.lock:
                    self.processes.discard(process)
            row['source_sha256_after'] = optional_digest(path)
            row['source_unchanged'] = (row['source_sha256_before'] is not None and
                                       row['source_sha256_before'] == row['source_sha256_after'])
            row['source_sha256'] = row['source_sha256_before']
            row['olean_sha256'] = optional_digest(target)
            if not row['source_unchanged']:
                row['errors'].append('Source hash changed during compilation or source is missing')
            if row['olean_sha256'] is None:
                row['errors'].append('No olean artifact was produced')
            if row['exit_code'] == 0 and not row['errors']:
                row['status'] = 'PASS'
            row['finished_at'] = utc_now()
            row['seconds'] = round(time.perf_counter() - started, 3)
        return row, output


def compile_graph(compiler, dependencies, ordered, jobs):
    """Run ready modules only; on failure drain running jobs and skip new work."""
    rank = {module: index for index, module in enumerate(ordered)}
    pending = set(ordered)
    completed, outputs, running = {}, {}, {}
    stop_submitting, interrupted = False, False
    with ThreadPoolExecutor(max_workers=jobs) as executor:
        while pending or running:
            try:
                if not stop_submitting:
                    ready = sorted((module for module in pending
                                    if all(dependency in completed and
                                           completed[dependency]['status'] == 'PASS'
                                           for dependency in dependencies[module])), key=rank.get)
                    for module in ready[:jobs - len(running)]:
                        pending.remove(module)
                        running[executor.submit(compiler.compile, module)] = module
                if not running:
                    break
                finished, _ = wait(running, return_when=FIRST_COMPLETED)
                for future in sorted(finished, key=lambda item: rank[running[item]]):
                    module = running[future]
                    row, output = future.result()
                    completed[module], outputs[module] = row, output
                    running.pop(future)
                    print(f'{len(completed)}/{len(ordered)} {row["status"]} {module}', flush=True)
                    if row['status'] != 'PASS':
                        stop_submitting = True
            except KeyboardInterrupt:
                interrupted = stop_submitting = True
                print('INTERRUPTED: stopping this build\'s subprocesses and collecting records.', flush=True)
                compiler.terminate_owned()
    for module in pending:
        completed[module] = dict(module=module, status='NOT_STARTED', exit_code=None,
                                 source=str(compiler.sources[module]),
                                 source_sha256_discovered=compiler.hashes[module],
                                 source_sha256_before=None, source_sha256_after=None,
                                 source_unchanged=None, olean_sha256=None,
                                 errors=['Build interrupted' if interrupted else
                                         'Not scheduled after a compilation failure'])
        outputs[module] = ''
    # A source or artifact changed after its own compilation also invalidates the run.
    for module in ordered:
        row = completed[module]
        row['source_sha256_final'] = optional_digest(compiler.sources[module])
        if row['status'] == 'PASS':
            row['olean_sha256_final'] = optional_digest(Path(row['olean']))
            if row['source_sha256_final'] != row['source_sha256_after']:
                row['status'] = 'FAILED'
                row['errors'].append('Source changed after compilation')
            if row['olean_sha256_final'] != row['olean_sha256']:
                row['status'] = 'FAILED'
                row['errors'].append('Olean changed after compilation')
    return [completed[module] for module in ordered], outputs, interrupted


def positive_integer(text):
    value = int(text)
    if value < 1:
        raise argparse.ArgumentTypeError('must be at least 1')
    return value


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--dependency-root', type=Path)
    ap.add_argument('--lean', type=Path)
    ap.add_argument('--jobs', type=positive_integer, default=1)
    ap.add_argument('--build-root', type=Path,
                    help='olean output/search directory; use a new directory for a clean rebuild')
    ap.add_argument('--module', action='append', default=[], metavar='MODULE',
                    help='build only this module and its local import closure; repeatable')
    ap.add_argument('--report-root', type=Path,
                    help='new report directory; defaults to audit/builds/<unique UTC run id>')
    args = ap.parse_args(argv)
    deps = (args.dependency_root or LEAN_ROOT / '.lake/packages').resolve()
    build = (args.build_root or LEAN_ROOT / '.lake/build/lib/lean').resolve()
    run_id = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S.%fZ') + f'-{os.getpid()}'
    reports = (args.report_root or AUDIT / 'builds' / run_id).resolve()
    try:
        reject_cache_output(reports, deps)
    except ValueError as error:
        raise SystemExit(str(error)) from error
    # Refuse to overwrite any previous report, including an explicitly selected one.
    if reports.exists():
        raise SystemExit('Report directory already exists; choose a new path: ' + str(reports))
    reports.mkdir(parents=True)
    started = time.perf_counter()
    result = dict(status='PREFLIGHT_FAILED', end_to_end_H1_H2_formalization=False,
                  created=utc_now(), jobs=args.jobs, requested_modules=args.module,
                  source_root=str(LEAN_ROOT), output_root=str(build), report_root=str(reports),
                  output_root_existed=build.exists(), dependency_root=str(deps),
                  dependency_cache_mode='read-only external cache' if args.dependency_root else
                                        'read-only project cache',
                  version=None, lean_options={}, option_args=[], dependency_revisions={},
                  expected_dependency_revisions={}, preflight_commands=[], modules=[],
                  scope='Compilation record only. Mathematical coverage and explicit upstream '
                        'premises are documented in FORMALIZATION_STATUS.md and audit/. The H1/H2-only '
                        'end-to-end formalization flag is not inferred from source or artifact existence.')
    outputs = {}
    exit_code = 1

    def preflight(command, environment):
        run = subprocess.run(command, cwd=LEAN_ROOT, env=environment, capture_output=True,
                             text=True, encoding='utf-8', errors='replace')
        result['preflight_commands'].append(dict(command=command, cwd=str(LEAN_ROOT),
            exit_code=run.returncode, stdout=run.stdout, stderr=run.stderr))
        if run.returncode:
            raise RuntimeError(f'Preflight command failed ({run.returncode}): {command!r}')
        return run.stdout.strip()

    try:
        reject_cache_output(build, deps)
        config = tomllib.loads((LEAN_ROOT / 'lakefile.toml').read_text(encoding='utf-8-sig'))
        lean_options = config.get('leanOptions', {})
        result['lean_options'] = lean_options
        option_args = ['-D' + key + '=' + (str(value).lower() if isinstance(value, bool) else str(value))
                       for key, value in lean_options.items()]
        result['option_args'] = option_args
        result['toolchain_specification'] = (LEAN_ROOT / 'lean-toolchain').read_text().strip()
        result['lakefile_sha256'] = digest(LEAN_ROOT / 'lakefile.toml')
        result['lake_manifest_sha256'] = digest(LEAN_ROOT / 'lake-manifest.json')
        result['build_script_sha256'] = digest(Path(__file__).resolve())
        if not deps.is_dir():
            raise ValueError('Dependency cache missing; run lake update/cache get separately or supply --dependency-root.')
        lean = str(args.lean.resolve()) if args.lean else shutil.which('lean')
        if not lean:
            fallback = Path.home() / '.elan/bin' / ('lean.exe' if os.name == 'nt' else 'lean')
            if fallback.exists():
                lean = str(fallback)
        if not lean:
            raise ValueError('Lean/elan not found')
        result['lean_executable'] = lean
        expected = json.loads((LEAN_ROOT / 'lake-manifest.json').read_text(encoding='utf-8-sig'))
        libraries = [build] + [deps / package['name'] / '.lake/build/lib/lean'
                              for package in sorted(expected['packages'], key=lambda item: item['name'])
                              if (deps / package['name'] / '.lake/build/lib/lean').is_dir()]
        environment = os.environ.copy()
        environment['LEAN_PATH'] = os.pathsep.join(map(str, libraries))
        result['lean_path'] = list(map(str, libraries))
        result['version'] = preflight([lean, '--version'], environment)
        expected_version = result['toolchain_specification'].rsplit(':', 1)[-1].removeprefix('v')
        if not re.search(r'\bversion ' + re.escape(expected_version) + r'(?=[,\s)])', result['version']):
            raise ValueError('Wrong toolchain: ' + result['version'])
        for package in expected['packages']:
            result['expected_dependency_revisions'][package['name']] = package['rev']
            revision = preflight(['git', '-C', str(deps / package['name']), 'rev-parse', 'HEAD'], environment)
            result['dependency_revisions'][package['name']] = revision
            if revision != package['rev']:
                raise ValueError('Dependency revision mismatch: ' + package['name'])
        sources, dependencies, hashes, ordered = source_graph(LEAN_ROOT, args.module)
        result['topological_order'] = ordered
        result['local_dependencies'] = {module: dependencies[module] for module in ordered}
        if not ordered:
            raise ValueError('No local Lean modules selected')
        build.mkdir(parents=True, exist_ok=True)
        compiler = Compiler(lean, option_args, LEAN_ROOT, build, environment, sources, hashes)
        result['status'] = 'RUNNING'
        rows, outputs, interrupted = compile_graph(compiler, dependencies, ordered, args.jobs)
        result['modules'] = rows
        passed = all(row['status'] == 'PASS' for row in rows)
        result['status'] = ('INTERRUPTED' if interrupted else
                            'SELECTED_LEAN_MODULES_COMPILED' if passed and args.module else
                            'ALL_PRESENT_LEAN_MODULES_COMPILED' if passed else 'BUILD_FAILED')
        exit_code = 130 if interrupted else 0 if passed else 1
        audit_row = next((row for row in rows if row['module'] == 'LegendreK6.Audit'), None)
        if audit_row and audit_row['status'] == 'PASS':
            (reports / 'kernel_axioms.txt').write_text(outputs['LegendreK6.Audit'], encoding='utf-8')
    except KeyboardInterrupt:
        result['status'] = 'INTERRUPTED'
        result['error'] = 'KeyboardInterrupt during preflight/reporting'
        exit_code = 130
    except Exception as error:
        result['status'] = 'BUILD_FAILED' if result['status'] == 'RUNNING' else 'PREFLIGHT_FAILED'
        result['error'] = f'{type(error).__name__}: {error}'
    finally:
        result['elapsed_seconds'] = round(time.perf_counter() - started, 3)
        result['finished_at'] = utc_now()
        log = ''.join(f'=== {row["module"]} [{row["status"]}] ===\n'
                      + outputs.get(row['module'], '')
                      + (('\n' + '\n'.join(row.get('errors', []))) if row.get('errors') else '')
                      + '\n' for row in result['modules'])
        if result.get('error'):
            log += result['error'] + '\n'
        (reports / 'lean_build.log').write_text(log, encoding='utf-8')
        (reports / 'lean_build_report.json').write_text(json.dumps(result, indent=2) + '\n', encoding='utf-8')
    print(result['status'], flush=True)
    print('REPORT_ROOT=' + str(reports), flush=True)
    print('END_TO_END_H1_H2_FORMALIZATION=false', flush=True)
    if result.get('error'):
        print(result['error'], flush=True)
    return exit_code


if __name__ == '__main__':
    raise SystemExit(main())
