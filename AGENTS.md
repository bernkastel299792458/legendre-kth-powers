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
- On 2026-11-07 the commits of `main` from `b1d00a8` onward were re-authored as
  `bernkastel299792458` and force-pushed; trees are unchanged (old-to-new table
  in `MIGRATION.md`). Local branches in the shared repository were rewritten in
  place. Commit with the repository identity `bernkastel299792458`
  (`202755654+bernkastel299792458@users.noreply.github.com`), and add
  `Co-authored-by` trailers for `Codex <267193182+codex@users.noreply.github.com>`
  and/or `Claude <noreply@anthropic.com>` as appropriate.

