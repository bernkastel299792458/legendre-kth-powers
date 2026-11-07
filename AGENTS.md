# Research-agent instructions

Read `RESEARCH_PROTOCOL.md` and `AUTHORS.md` before research or publication work.

- **Codex leads `routes/qrh/` (QRH(7/8)).**
- **Claude leads `routes/traditional/` (traditional explicit estimates).**
- Root documentation and workflows are shared infrastructure. User instructions
  override this default division; authorized mechanical migrations may touch both routes.
- Preserve the distinction between hypotheses, written proofs, numerical
  certificates, partial Lean results, and end-to-end formalization.
- Do not overwrite another session's changes or use its active Git index.
  Keep separate checkouts/worktrees and fetch before integrating/publishing.
- Preserve historical audit text and mathematical certificate bytes. Consult
  `MIGRATION.md` for legacy paths and the retained result-specific Lean names.
- QRH release hashes and script hashes matter: follow the route's
  `REPRODUCING.md` and regenerate `MANIFEST.json` after authorized package edits.
- Authors are bernkastel299792458 (project owner), Claude and Codex, with route leads and
  actual contributions stated explicitly. Affiliation and email remain unfilled
  unless supplied.
