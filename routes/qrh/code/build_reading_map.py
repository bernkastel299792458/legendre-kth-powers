"""Generate a review map from the manuscript's actual Lean references.

Checks declaration/file existence and TeX cross-reference/bibliography keys.
It does not establish semantic equivalence between prose and Lean statements.
"""
from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
PAPER = ROOT / 'paper/current'
DEST = ROOT / 'documentation/blueprint'
TITLES = {
    '01_introduction': '问题、主定理与证明路线',
    '02_inputs': '七项外部输入',
    '03_preliminaries': '实际零点与算术准备',
    '04_trapezoid': '梯形权与素数提取',
    '05_density': '密度网格与完整高度余项',
    '06_certificates': '严格数值证书与整数矩',
    '07_coverage': '连续覆盖及有限高度 RH 比较',
    '08_tail': '无限尾部',
    '09_lower': '整数下段',
    '10_assembly': '主定理总装',
    '11_methods': '方法贡献与后续研究',
    '12_formalization': '形式化、复现与 AI 贡献',
    'appendix_versions': '历史版本与材料索引',
}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def build() -> tuple[dict, str]:
    files = sorted((PAPER / 'sections').glob('*.tex'))
    all_tex = (PAPER / 'main.tex').read_text(encoding='utf-8') + '\n'
    chapters = []
    errors = []
    for chapter in files:
        source = chapter.read_text(encoding='utf-8')
        all_tex += source + '\n'
        mappings = []
        for match in re.finditer(r'\\leanref\{([^{}]+)\}\{([^{}]+)\}', source):
            module, declarations = match.groups()
            lean = ROOT / 'lean/LegendreK6' / (module + '.lean')
            if not lean.is_file():
                errors.append(f'{chapter.name}: missing Lean file {module}')
                continue
            lean_text = lean.read_text(encoding='utf-8')
            for declaration in re.split(r'\s*;\s*', declarations):
                short = declaration.strip().split('.')[-1]
                found = re.search(r'\b(?:theorem|lemma|def|abbrev|structure|inductive)\s+'
                                  + re.escape(short) + r'\b', lean_text)
                if not found:
                    errors.append(f'{chapter.name}: declaration {declaration} missing in {module}')
                    continue
                mappings.append({
                    'module': module, 'declaration_as_cited': declaration.strip(),
                    'file': lean.relative_to(ROOT).as_posix(),
                    'line': lean_text.count('\n', 0, found.start()) + 1,
                    'source_sha256': sha(lean),
                })
        chapters.append({
            'source': chapter.relative_to(ROOT).as_posix(),
            'title': TITLES[chapter.stem], 'sha256': sha(chapter),
            'lean_mappings': mappings,
        })
    labels = re.findall(r'\\label\{([^{}]+)\}', all_tex)
    duplicates = [k for k, v in Counter(labels).items() if v > 1]
    errors.extend('Duplicate TeX label: ' + k for k in duplicates)
    for label in re.findall(r'\\(?:eqref|ref|pageref)\{([^{}]+)\}', all_tex):
        if label not in labels:
            errors.append('Undefined TeX reference: ' + label)
    bib = (PAPER / 'references.bib').read_text(encoding='utf-8')
    bibkeys = set(re.findall(r'@\w+\s*\{\s*([^,\s]+)', bib))
    for group in re.findall(r'\\(?:cite|nocite)(?:\[[^\]]*\])?\{([^{}]+)\}', all_tex):
        for key in group.split(','):
            if key.strip() not in bibkeys and key.strip() != '*':
                errors.append('Missing bibliography key: ' + key)
    if errors:
        raise ValueError('\n'.join(errors))
    record = {
        'schema': 'qrh-manuscript-reading-map-v1',
        'scope': 'File/declaration names, TeX labels and bibliography keys; not a semantic proof audit.',
        'chapters': chapters,
        'checked_lean_references': sum(len(c['lean_mappings']) for c in chapters),
        'unique_lean_files': len({r['file'] for c in chapters for r in c['lean_mappings']}),
        'tex_labels': len(labels), 'bibliography_keys': sorted(bibkeys),
    }
    lines = [
        '# 论文与 Lean 声明对照', '',
        '由 `code/build_reading_map.py` 从当前论文中的 `\\leanref` 标记生成。',
        '检查文件和声明是否存在，并绑定源码散列；数学陈述是否等价由正文与交叉审阅确认。', '',
        '[完整论文](../../paper/current/main.pdf) · [证明结构](README.md) · [机器记录](reading_map.json)', '',
    ]
    for chapter in chapters:
        lines += ['## ' + chapter['title'], '',
                  f"[章节源码](../../{chapter['source']})", '']
        if not chapter['lean_mappings']:
            lines += ['本节承担引言、讨论或研究披露，不另声明新的形式化结果。', '']
            continue
        lines += ['| Lean 文件 | 声明 |', '|---|---|']
        seen = set()
        for row in chapter['lean_mappings']:
            key = (row['file'], row['declaration_as_cited'])
            if key in seen:
                continue
            seen.add(key)
            lines.append(f"| [{row['module']}](../../{row['file']}) | `{row['declaration_as_cited']}` |")
        lines.append('')
    return record, '\n'.join(lines) + '\n'


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    record, markdown = build()
    outputs = {
        DEST / 'reading_map.json': json.dumps(record, ensure_ascii=False, indent=2) + '\n',
        DEST / 'theorem_map.md': markdown,
    }
    if args.check:
        for path, content in outputs.items():
            if path.read_bytes() != content.encode('utf-8'):
                raise SystemExit('READING_MAP_DIFFERS: ' + str(path))
        print('READING_MAP_VERIFIED', record['checked_lean_references'])
    else:
        DEST.mkdir(parents=True, exist_ok=True)
        for path, content in outputs.items():
            path.write_text(content, encoding='utf-8', newline='\n')
        print('READING_MAP_WRITTEN', record['checked_lean_references'])


if __name__ == '__main__':
    main()
