#!/usr/bin/env python3
"""Copy selected project research records without rewriting or executing them.

Creation:
  python snapshot_legacy.py --source-root PATH/TO/Legendre_k8
Verification (does not require the original workspace):
  python snapshot_legacy.py --verify-only

This archive is evidence preservation, not mathematical revalidation. Existing
snapshot files with different bytes are never overwritten. No Git command,
research program, dependency installer, or network operation is invoked.
"""
from __future__ import annotations

import argparse
import ast
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import posixpath
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

HERE = Path(__file__).resolve().parent
SNAPSHOT_NAME = "legacy-20261106"
DEST = HERE / "snapshots" / SNAPSHOT_NAME
EXTENSIONS = {".md", ".py", ".json", ".csv"}
FOLDERS = (
    "research", "code", "results", "theory_round5",
    "archive/k6_before_claude_revision_2026-11-06",
)
ROOT_FILES = (
    "README.md", "ROADMAP.md", "RUNBOOK.md", "LOG.md",
    "GPT_OpenAI_QRH_status_2026-11-06.md",
    "GPT_Claude_k67_progress_vs_prior_work_2026-11-06.md",
)
EXCLUDED_DUPLICATES = {
    "archive/k6_before_claude_revision_2026-11-06/review/Claude_K6_proof_review_2026-11-06.md":
        "../audit/source_reviews/Claude_K6_proof_review_2026-11-06.md",
}
REVIEW_LINKS = {
    "review/Claude_K6_proof_review_2026-11-06.md": "../audit/source_reviews/Claude_K6_proof_review_2026-11-06.md",
    "review/Response_to_Claude_K6_2026-11-06.md": "../audit/source_reviews/Response_to_Claude_K6_2026-11-06.md",
    "review/K6_revision_numeric_audit_2026-11-06.md": "../audit/source_reviews/K6_revision_numeric_audit_2026-11-06.md",
    "review/K6_manuscript_revision_review_2026-11-06.md": "../audit/source_reviews/K6_manuscript_revision_review_2026-11-06.md",
}
SECRET_PATTERNS = {
    "private_key": re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    "credential_prefix": re.compile(r"(?<![A-Za-z0-9])(?:sk-[A-Za-z0-9_-]{20,}|gh[pousr]_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|AKIA[0-9A-Z]{16})"),
    "literal_credential": re.compile(r'''(?i)(?:api[_-]?key|secret|password|access[_-]?token)\s*[:=]\s*["'][^"'\s]{8,}["']'''),
}
UUID = re.compile(r"(?i)\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b")
COPYRIGHT = re.compile(r"(?i)(copyright|all rights reserved|SPDX-License|Version: 29 June 2022|Authors: Michaela)")


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def write_json(path: Path, data: object) -> None:
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n",
                    encoding="utf-8", newline="\n")


def selected(source: Path) -> list[Path]:
    paths = [source / name for name in ROOT_FILES]
    for folder in FOLDERS:
        paths.extend(p for p in (source / folder).rglob("*")
                     if p.is_file() and p.suffix.lower() in EXTENSIONS)
    for path in paths:
        if path.is_symlink() or not path.resolve().is_relative_to(source):
            raise ValueError("Refusing a symlink or source path outside the declared root.")
    return sorted(set(paths), key=lambda p: p.relative_to(source).as_posix())


def stage(relative: str) -> str:
    lower = relative.lower()
    if lower.startswith("archive/"):
        return "historical_k6_before_claude_revision"
    if lower.startswith("theory_round5/") or any(s in lower for s in ("round3", "round4", "round5")):
        return "parallel_k4_rounds_3_to_5_not_reaudited"
    if "k6" in lower:
        return "legacy_k6_research_and_certificates"
    if lower.startswith("gpt_"):
        return "initial_background_report_not_reaudited"
    if "/" not in relative:
        return "mixed_historical_status_and_decisions"
    return "initial_k4_and_common_framework_exploration"


def dependency_inventory(source: Path, paths: list[str]) -> dict:
    included = set(paths)
    gaps, kept_links, mathematical_false_positives = [], 0, []
    imports = set()
    python_stems = {Path(p).stem for p in paths if p.endswith(".py")}
    for relative in paths:
        text = (DEST / relative).read_bytes().decode("utf-8-sig", errors="replace")
        if relative.endswith(".md"):
            for match in re.finditer(r"\[[^\]\n]*\]\(([^)\n]+)\)", text):
                target = match.group(1).strip()
                if target.startswith("<") and ">" in target:
                    target = target[1:target.index(">")]
                else:
                    target = target.split(' "', 1)[0]
                target = unquote(target).replace("\\", "/")
                if target in {"logT", "log T"}:
                    mathematical_false_positives.append({"referrer": relative,
                        "pattern_target": target, "reason": "Manually inspected mathematical bracket/product syntax, not a file link."})
                    continue
                if not target or target.startswith("#") or urlsplit(target).scheme:
                    continue
                target = target.split("#", 1)[0].split("?", 1)[0]
                if not target:
                    continue
                normalized = posixpath.normpath(posixpath.join(posixpath.dirname(relative), target))
                if normalized in included or any(p.startswith(normalized.rstrip("/") + "/") for p in paths):
                    kept_links += 1
                    continue
                outside = normalized == ".." or normalized.startswith("../") or normalized.startswith("/")
                original_exists = False if outside else (source / normalized).exists()
                gaps.append({
                    "referrer": relative, "original_target": target,
                    "resolved_source_relative_target": normalized,
                    "reason": "outside_selected_source_root" if outside else
                              "exists_in_original_but_not_selected" if original_exists else
                              "not_found_at_original_relative_path",
                    "current_repository_reference": REVIEW_LINKS.get(normalized),
                })
        if relative.endswith(".py"):
            tree = ast.parse(text, filename=relative)
            for node in ast.walk(tree):
                if isinstance(node, ast.Import):
                    imports.update(alias.name.split(".")[0] for alias in node.names)
                elif isinstance(node, ast.ImportFrom) and node.module:
                    imports.add(node.module.split(".")[0])
    external_imports = sorted(imports - set(sys.stdlib_module_names) - python_stems - {"__future__"})
    return {
        "scope": "Static Markdown-link and Python-import inventory; no historical code executed.",
        "limitations": [
            "Markdown scan does not parse arbitrary HTML, nested parentheses, reference-style links, or headings.",
            "Python imports are inspected syntactically; dynamic runpy/Path construction is not fully resolved.",
            "Preserved links to missing material are not rewritten into claims of archival completeness.",
        ],
        "preserved_relative_link_count": kept_links,
        "missing_relative_links": gaps,
        "mathematical_syntax_false_positives": mathematical_false_positives,
        "external_python_imports_not_bundled": external_imports,
        "known_unbundled_dependencies": [
            {"path": "code/requirements.txt", "reason": "Outside requested MD/PY/JSON/CSV scope; old environment is not reconstructed."},
            {"path": "manuscript/", "reason": "Old manuscript not copied in this research-data snapshot; see current paper and separate archive index."},
            {"path": "proof/", "reason": "Old publication/build/dependency tree deliberately excluded."},
            {"path": "review/", "reason": "Review Markdown already present in repository; linked separately."},
            {"path": "computation_branch/", "reason": "Separate active computation work excluded by task scope."},
            {"path": "algorithm_only/", "reason": "Separate active algorithm work excluded by task scope."},
            {"path": "*.pdf and third-party source/dependency trees", "reason": "Third-party works and executable/dependency caches are not redistributed."},
        ],
    }


def verify() -> dict:
    manifest = json.loads((HERE / "snapshot_manifest.json").read_text(encoding="utf-8"))
    for item in manifest["files"]:
        target = HERE / item["snapshot_path"]
        if not target.resolve().is_relative_to(DEST):
            raise ValueError("Manifest path escapes the snapshot.")
        data = target.read_bytes()
        if len(data) != item["bytes"] or sha(data) != item["sha256"]:
            raise ValueError("Snapshot bytes differ: " + item["original_relative_path"])
    return {"status": "SNAPSHOT_BYTES_VERIFIED", "files": len(manifest["files"]),
            "bytes": manifest["total_bytes"], "mathematical_revalidation": False}


def create(source: Path) -> dict:
    source = source.resolve(strict=True)
    if DEST.exists() and not DEST.resolve().is_relative_to(HERE):
        raise ValueError("Snapshot destination escapes this archive directory.")
    candidates = selected(source)
    records, exclusions, privacy = [], [], []
    for path in candidates:
        relative = path.relative_to(source).as_posix()
        if relative in EXCLUDED_DUPLICATES:
            exclusions.append({"path": relative, "reason": "Existing repository review, indexed without duplication.",
                               "repository_reference": EXCLUDED_DUPLICATES[relative]})
            continue
        data = path.read_bytes()
        text = data.decode("utf-8-sig", errors="replace")
        high_risk = [name for name, pattern in SECRET_PATTERNS.items() if pattern.search(text)]
        if COPYRIGHT.search(text):
            high_risk.append("copyright_or_external_author_marker_requires_review")
        if high_risk:
            exclusions.append({"path": relative, "reason": "Excluded pending sensitive-data or provenance review.",
                               "flags": high_risk})
            continue
        flags = {}
        if UUID.search(text):
            flags["session_uuid_count"] = len(UUID.findall(text))
            privacy.append({"path": relative, "flags": flags,
                            "treatment": "Retained verbatim for local owner review; identifiers are not repeated in the narrative index."})
        before = sha(data)
        target = DEST / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        if target.exists():
            if target.read_bytes() != data:
                raise ValueError("Immutable snapshot already has different bytes: " + relative)
        else:
            target.write_bytes(data)
        after = sha(path.read_bytes())
        copied = sha(target.read_bytes())
        if before != after or before != copied:
            raise ValueError("Source changed or copy differs: " + relative)
        records.append({
            "original_relative_path": relative,
            "snapshot_path": target.relative_to(HERE).as_posix(),
            "bytes": len(data), "sha256": before,
            "source_sha256_before_copy": before, "source_sha256_after_copy": after,
            "snapshot_sha256": copied, "source_stable_during_copy": True,
            "source_mtime_ns_observed": path.stat().st_mtime_ns,
            "line_endings": {"CRLF": data.count(b"\r\n"), "LF_total": data.count(b"\n"),
                             "bare_CR": data.count(b"\r") - data.count(b"\r\n")},
            "archive_group": stage(relative), "privacy_flags": flags,
            "evidence_status": "Original research artifact preserved; not mathematically revalidated by this archival operation.",
        })
    for item in records:
        if sha((source / item["original_relative_path"]).read_bytes()) != item["sha256"]:
            raise ValueError("Source changed before final archive check: " + item["original_relative_path"])
        item["source_hash_stable_at_final_check"] = True
    (HERE / "snapshots" / ".gitattributes").write_text(
        "# Original snapshot bytes: disable line-ending normalization.\n* -text\n",
        encoding="utf-8", newline="\n")
    manifest = {
        "schema_version": 1, "snapshot_name": SNAPSHOT_NAME,
        "created_at_utc": datetime.now(timezone.utc).isoformat(),
        "source_root_label": "Legendre_k8", "source_state": "Active local legacy workspace; copied in place, never moved/reset/cleaned.",
        "publication_state": "LOCAL_OWNER_REVIEW_ONLY_NO_PUSH",
        "selection_rules": {"root_files": list(ROOT_FILES), "recursive_roots": list(FOLDERS),
                            "extensions": sorted(EXTENSIONS), "duplicate_review_policy": EXCLUDED_DUPLICATES},
        "excluded_roots_or_types": ["computation_branch/", "algorithm_only/", "proof/", ".lake/", ".git/", "third-party PDFs", "third-party source/dependency trees", "compiled artifacts", "unselected file types"],
        "originality_basis": "Selected project-authored research notes, scripts, and outputs from the task-designated roots; manual header/provenance inspection and marker scan. Third-party literature is referenced, not copied.",
        "sensitive_scan": {"credential_patterns": list(SECRET_PATTERNS), "high_risk_exclusions": [x for x in exclusions if "flags" in x],
                           "session_identifiers_retained_for_local_review": privacy,
                           "manually_resolved_false_positive": {"path": "code/k4_far_redesign_round5.py", "finding": "Email-pattern match was Python matrix-multiplication syntax, not an email address."},
                           "limitation": "Targeted heuristic/manual review is not a guarantee that arbitrary sensitive information cannot occur."},
        "candidate_count": len(candidates), "file_count": len(records), "total_bytes": sum(x["bytes"] for x in records),
        "counts_by_top_level": dict(sorted(Counter(x["original_relative_path"].split("/")[0] for x in records).items())),
        "all_source_hashes_stable_before_after_and_final": True,
        "historical_text_modified": False, "historical_programs_executed": False,
        "mathematical_revalidation": False,
        "snapshot_script_sha256": sha(Path(__file__).read_bytes()),
        "excluded_candidates": exclusions, "existing_review_references": REVIEW_LINKS,
        "files": records,
    }
    write_json(HERE / "snapshot_manifest.json", manifest)
    write_json(HERE / "dependency_gaps.json", dependency_inventory(source, [x["original_relative_path"] for x in records]))
    return verify()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source-root", type=Path)
    parser.add_argument("--verify-only", action="store_true")
    args = parser.parse_args()
    if args.verify_only:
        result = verify()
    elif args.source_root:
        result = create(args.source_root)
    else:
        parser.error("Provide --source-root for creation, or --verify-only.")
    print(json.dumps(result))


if __name__ == "__main__":
    main()
