"""Build the current Chinese mathematical manuscript with Tectonic.

The TeX files are authoritative; this script never rewrites mathematical
source. Intermediates are kept in the route's ignored tmp directory.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import re
from pathlib import Path
import shutil
import subprocess
import time

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent.parent


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def sources() -> dict[str, str]:
    paths = [HERE / 'main.tex', HERE / 'references.bib', HERE / 'plainurl.bst',
             Path(__file__).resolve()]
    paths.extend(sorted((HERE / 'sections').glob('*.tex')))
    return {p.relative_to(ROOT).as_posix(): digest(p) for p in paths}


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--engine', help='Tectonic executable (defaults to PATH)')
    parser.add_argument('--check', action='store_true', help='Check existing PDF/source binding')
    args = parser.parse_args()
    report_path = HERE / 'build_report.json'
    output = HERE / 'main.pdf'
    if args.check:
        report = json.loads(report_path.read_text(encoding='utf-8'))
        if report['sources_sha256'] != sources() or report['pdf_sha256'] != digest(output):
            raise SystemExit('PAPER_SOURCE_OR_PDF_MISMATCH')
        print('PAPER_SOURCE_PDF_BINDING_PASS', len(report['sources_sha256']))
        return
    engine = args.engine or shutil.which('tectonic')
    if not engine:
        raise SystemExit('Install Tectonic, or supply --engine /path/to/tectonic.')
    engine = str(Path(engine).resolve())
    version = subprocess.check_output([engine, '--version'], text=True).strip()
    captured_sources = sources()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    build_root = ROOT / 'tmp' / 'paper-builds' / stamp
    build_root.mkdir(parents=True, exist_ok=False)
    command = [engine, '-X', 'compile', 'main.tex', '--outdir', str(build_root),
               '--keep-logs', '--keep-intermediates']
    started = time.monotonic()
    completed = subprocess.run(command, cwd=HERE, capture_output=True)
    log = completed.stdout + b'\n' + completed.stderr
    (build_root / 'compiler_output.txt').write_bytes(log)
    print(log.decode('utf-8', errors='replace'))
    if completed.returncode:
        raise SystemExit(completed.returncode)
    bibliography = build_root / 'main.bbl'
    if not bibliography.is_file() or not bibliography.stat().st_size:
        raise SystemExit('INCOMPLETE_PAPER: bibliography missing; inspect the BibTeX log.')
    aux = (build_root / 'main.aux').read_text(encoding='utf-8')
    bbl = bibliography.read_text(encoding='utf-8')
    cited = {key for group in re.findall(r'\\citation\{([^}]+)\}', aux)
             for key in group.split(',')}
    items = set(re.findall(r'\\bibitem(?:\[[^\]]*\])?\{([^}]+)\}', bbl))
    if cited - items:
        raise SystemExit('INCOMPLETE_PAPER: missing bibliography entries: ' + str(sorted(cited - items)))
    final_log = (build_root / 'main.log').read_text(encoding='utf-8', errors='replace')
    unresolved = re.findall(r'LaTeX Warning: (?:Citation|Reference)[^\n]*undefined[^\n]*', final_log)
    if unresolved:
        raise SystemExit('INCOMPLETE_PAPER: unresolved cross-references: ' + str(unresolved))
    if sources() != captured_sources:
        raise SystemExit('Paper sources changed during the build; rebuild the settled sources.')
    shutil.copyfile(build_root / 'main.pdf', output)
    report = {
        'schema': 'qrh-current-paper-build-v1',
        'status': 'PDF_COMPILED_VISUAL_REVIEW_SEPARATE',
        'created_utc': datetime.now(timezone.utc).isoformat(),
        'engine': version,
        'bibliography_entries': len(items),
        'unresolved_references': unresolved,
        'elapsed_seconds': round(time.monotonic() - started, 3),
        'sources_sha256': captured_sources,
        'pdf': 'paper/current/main.pdf',
        'pdf_sha256': digest(output),
        'compiler_output_sha256': hashlib.sha256(log).hexdigest(),
        'local_intermediates': build_root.relative_to(ROOT).as_posix(),
        'publication_status': 'LOCAL_USER_REVIEW_PENDING',
        'mathematical_validation': 'See the independent Lean, dependency, and certificate records.',
    }
    report_path.write_text(json.dumps(report, ensure_ascii=False, indent=2) + '\n',
                           encoding='utf-8', newline='\n')
    print('CURRENT_PAPER_BUILT', output)


if __name__ == '__main__':
    main()
