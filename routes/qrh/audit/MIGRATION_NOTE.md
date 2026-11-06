# QRH route migration and editorial attribution

2026-11-06: the package moved from `conditional-k6/` to `routes/qrh/`.
Codex leads this route; Claude and Codex are the user-requested joint AI
authors, with Claude's earlier review contribution distinguished from the
later implementation work.

The previous manuscript SHA256 was
`c5bc5224c34267f2733de261b6485fc2a34a0bcdb02c8728660db9916c50e30a`.
The manuscript after adding the author and role paragraphs has SHA256
`74084d1b194177f89c04153b8e486aa0dfeb2eedab485855bfbb802bbb49a35a`.
Removing those two additions recovers the previous mathematical manuscript
exactly. All 107 display-math blocks remain unchanged.

Historical reports in this directory and `source_reviews/` retain the
versions, hashes, and local paths that they originally reviewed. Their old
manuscript hashes are not failed checks of the editorial revision. They are
not retroactively described as reviews of the new author page or repository
layout. Mathematical source snapshots still match
`source_snapshot_manifest.json`.

The current PDF build record is `pdf_build_report.json`; the current package
bytes are identified by `../MANIFEST.json`. CI and reproduction commands now
use the route path. See the repository [migration map](../../../MIGRATION.md)
and [collaboration protocol](../../../RESEARCH_PROTOCOL.md).

The full conditional theorem's end-to-end Lean formalization remains
incomplete. Moving files and changing attribution do not change the theorem
types or the obligations listed in `../FORMALIZATION_STATUS.md`.
