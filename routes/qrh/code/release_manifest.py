"""Create/check SHA256 identifiers for the exact published package bytes."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCHEMA = 'conditional-k6-public-review-v2'
EXCLUDED_PARTS = {'.lake', '__pycache__', 'tmp', '.git'}
EXCLUDED_SUFFIXES = {'.aux', '.out', '.toc', '.xdv', '.pyc', '.fls', '.fdb_latexmk'}
EXTERNAL_INPUTS = [
    'QRHSevenEighths', 'CSv2', 'RosserZeroCount', 'IntegratedExplicitFormula',
    'FiniteRH3e12', 'CHJIIShortInterval', 'CHLRows',
]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def formalization_metadata():
    """Bind acceptance to portable source/evidence hashes, not local oleans.

    Fresh artifact checks belong to the build and its matching audit. This
    release check also works before installing Lean on another machine.
    """
    checkpoint_name = 'audit/milestone3_checkpoint.json'
    checkpoint_path = ROOT / checkpoint_name
    scope = dict(
        status='not_accepted',
        theorem='LegendreK6.sixth_powers_from_named_inputs',
        conclusion='For every integer n >= 1, an actual Nat.Prime p satisfies n^6 < p < (n+1)^6.',
        external_inputs=['LegendreK6.' + name for name in EXTERNAL_INPUTS],
        external_inputs_reproved=False,
    )
    result = dict(
        end_to_end_H1_H2_lean_formalization=False,
        downstream_from_named_inputs_lean_formalization=False,
        formalization_scope=scope,
    )
    if not checkpoint_path.exists():
        return result
    checkpoint = json.loads(checkpoint_path.read_text(encoding='utf-8'))
    require(checkpoint['status'] == 'MILESTONE_3_COMPLETE_RELATIVE_TO_NAMED_INPUTS',
            'Final checkpoint is not accepted')
    require(checkpoint['external_inputs'] == EXTERNAL_INPUTS, 'Checkpoint input list differs')
    evidence = {}
    parsed_evidence = {}
    for label, relative in [
        ('build', 'audit/builds/final-20261106/lean_build_report.json'),
        ('dependency_audit', 'audit/builds/final-20261106/final_dependency_report.json'),
    ]:
        path = ROOT / relative
        data = path.read_bytes()
        sha256 = hashlib.sha256(data).hexdigest()
        require(checkpoint['sha256'].get(relative) == sha256, 'Checkpoint evidence hash differs: ' + relative)
        evidence[label] = dict(path=relative, sha256=sha256)
        parsed_evidence[label] = json.loads(data.decode('utf-8'))
    build = parsed_evidence['build']
    audit = parsed_evidence['dependency_audit']
    require(build['status'] == 'ALL_PRESENT_LEAN_MODULES_COMPILED', 'Full build did not pass')
    require(build['output_root_existed'] is False, 'Build output was not fresh')
    require(audit['status'] == 'FINAL_K6_DEPENDENCY_AUDIT_PASSED', 'Final dependency audit did not pass')
    require(audit['build_report_sha256'] == evidence['build']['sha256'], 'Audit is bound to another build')
    require(digest(ROOT / 'audit/FinalDependencies.lean') == audit['diagnostic_source_sha256'],
            'Dependency diagnostic source differs')
    require(digest(ROOT / 'audit/builds/final-20261106/final_dependencies.txt') == audit['output_sha256'],
            'Dependency diagnostic output differs')
    lean_root = ROOT / 'lean'
    sources = {p.relative_to(lean_root).as_posix(): p for p in lean_root.rglob('*.lean')
               if '.lake' not in p.parts}
    rows = build['modules']
    require(len(rows) == len(sources) == audit['checked_modules'], 'Current source count differs')
    require({r['source_relative'] for r in rows} == set(sources), 'Current source inventory differs')
    for row in rows:
        require(row['status'] == 'PASS' and row['exit_code'] == 0 and
                row['olean_existed_before'] is False and row['source_unchanged'] is True,
                'Module did not pass a fresh build: ' + row['module'])
        sha256 = digest(sources[row['source_relative']])
        require(all(row[key] == sha256 for key in
                    ['source_sha256_discovered', 'source_sha256_before',
                     'source_sha256_after', 'source_sha256_final']),
                'Module source differs from accepted build: ' + row['module'])
    for relative, key in [('lakefile.toml', 'lakefile_sha256'),
                          ('lake-manifest.json', 'lake_manifest_sha256')]:
        require(digest(lean_root / relative) == build[key], 'Build configuration differs: ' + relative)
    require((lean_root / 'lean-toolchain').read_text().strip() == build['toolchain_specification'],
            'Lean toolchain specification differs')
    scope['status'] = 'complete_downstream_from_named_inputs'
    scope['acceptance_checkpoint'] = checkpoint_name
    scope['evidence'] = evidence
    result['downstream_from_named_inputs_lean_formalization'] = True
    return result

def paths():
    for p in sorted(ROOT.rglob('*')):
        if not p.is_file(): continue
        rel = p.relative_to(ROOT)
        if any(part in EXCLUDED_PARTS for part in rel.parts): continue
        if p.suffix in EXCLUDED_SUFFIXES: continue
        if rel.as_posix() == 'MANIFEST.json': continue
        if rel.parts[0] == 'paper' and p.suffix == '.log': continue
        yield rel.as_posix(), p

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    args=parser.parse_args()
    actual={r:digest(p) for r,p in paths()}
    metadata=formalization_metadata()
    dest=ROOT/'MANIFEST.json'
    if args.check:
        saved=json.loads(dest.read_text(encoding='utf-8'))
        if saved.get('schema') != SCHEMA:
            raise SystemExit('Release manifest schema differs')
        if any(saved.get(key) != value for key,value in metadata.items()):
            raise SystemExit('Release formalization metadata differs from current acceptance evidence')
        changed=[r for r,h in saved['sha256'].items() if actual.get(r)!=h]
        if changed: raise SystemExit('Release byte mismatch: '+', '.join(changed))
        extra=sorted(set(actual)-set(saved['sha256']))
        if extra: raise SystemExit('Unlisted release files: '+', '.join(extra))
        print('RELEASE_MANIFEST_VERIFIED',len(saved['sha256']))
    else:
        result={'schema':SCHEMA, **metadata, 'sha256':actual}
        dest.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        print('RELEASE_MANIFEST_WRITTEN',len(actual))

if __name__=='__main__':main()
