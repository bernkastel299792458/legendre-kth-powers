"""Create/check SHA256 identifiers for the exact published package bytes."""
import argparse
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
EXCLUDED_PARTS = {'.lake', '__pycache__', 'tmp', '.git'}
EXCLUDED_SUFFIXES = {'.aux', '.out', '.toc', '.xdv', '.pyc', '.fls', '.fdb_latexmk'}

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
    actual={r:hashlib.sha256(p.read_bytes()).hexdigest() for r,p in paths()}
    dest=ROOT/'MANIFEST.json'
    if args.check:
        saved=json.loads(dest.read_text(encoding='utf-8'))
        changed=[r for r,h in saved['sha256'].items() if actual.get(r)!=h]
        if changed: raise SystemExit('Release byte mismatch: '+', '.join(changed))
        extra=sorted(set(actual)-set(saved['sha256']))
        if extra: raise SystemExit('Unlisted release files: '+', '.join(extra))
        print('RELEASE_MANIFEST_VERIFIED',len(saved['sha256']))
    else:
        result={'schema':'conditional-k6-public-review-v1',
                'end_to_end_H1_H2_lean_formalization':False,'sha256':actual}
        dest.write_text(json.dumps(result,ensure_ascii=False,indent=2)+'\n',encoding='utf-8')
        print('RELEASE_MANIFEST_WRITTEN',len(actual))

if __name__=='__main__':main()
