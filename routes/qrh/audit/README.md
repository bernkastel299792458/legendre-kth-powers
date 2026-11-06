# Audit evidence index

## Current manuscript and archival review

- [Current complete paper](../paper/current/main.pdf), [seven-input register](../documentation/inputs.md),
  and [paper-to-Lean guide](../documentation/blueprint/README.md).
- [Archival verification record](archive_review_2026-11-06.json): additional clean-source
  rebuild, matching dependency audit, preserved source hashes and numerical replay.
- [Analytic chapter cross-review](current_manuscript_analytic_crossreview.md) and
  [tail/lower-range/assembly cross-review](current_manuscript_tail_crossreview.md).
  These identify reviewer implementation overlap.
- [PDF build binding](../paper/current/build_report.json) and
  [page-by-page visual review](current_paper_visual_review.json).
- [Research-history archive](../research-history/README.md): 177 original-byte
  snapshots with selection scope, hashes and historical dependency gaps.
- [Source-preservation check](archive_source_preservation.json): 628 protected
  files match the accepted baseline byte for byte, including the traditional tree.
- [Independent check of the additional build](archive_build_independent_check.json):
  38 checks of sources, artifacts, pinned dependencies and the exact audit binding.
- [Document-tooling review](current_document_tooling_review.md) and
  [navigation/input-register review](current_package_navigation_review.json).


The accepted result is the complete downstream k=6 Lean proof from seven
explicit external mathematical inputs. It proves an actual prime strictly
between consecutive sixth powers for every integer n >= 1. The external
literature theorems are inputs, not results re-proved by this project.

## Final acceptance, 2026-11-06

- [Acceptance checkpoint](milestone3_checkpoint.json): exact scope, inputs,
  and hashes binding the final proof and evidence.
- [Clean build](builds/final-20261106/lean_build_report.json): all 241 modules
  passed in 2690.618 seconds; previously nonexistent output tree, pinned
  toolchain/dependencies and `autoImplicit=false`.
- [Matching dependency audit](builds/final-20261106/final_dependency_report.json):
  passed in 17.375 seconds against those fresh artifacts.
- [Complete types and dependency output](builds/final-20261106/final_dependencies.txt):
  seven input types, actual transitive proof dependencies, and only `propext`,
  `Classical.choice`, `Quot.sound` in the final axiom reports.
- [Independent build-record checks](final_build_independent_check.json),
  [final assembly review](milestone3_final_review.md),
  [translation and semantic review](milestone3_translation_review.md), and
  [build-tool review](build_driver_review.md). These identify implementation
  overlap and are AI cross-reviews, not human peer review.
- [Six generator checks](final_source_regeneration.json) and
  [four-certificate replay](final_numerical_replay_2026-11-06.json): deterministic
  source consistency and preserved historical numerical evidence, respectively.

For mathematical navigation, start with the [proof map](PROOF_MAP.md),
[readable addendum](../paper/lean_formalization_addendum.md), and
[exact scope](../FORMALIZATION_STATUS.md).

## Historical evidence

The subsequent [source audit of external inputs 4, 6 and 7](inputs_4_6_7_review_2026-11-06.md)
is separate from the accepted Lean build. It includes an exact published
source for the integrated explicit formula, CHJII version/constant checks,
and the CHL rounded-parameter reproduction issue. It does not remove those
inputs from the theorem or claim independent human peer review.

Earlier reports retain their original source hashes and conclusions. They
must not be interpreted as audits of later sources:

- `lean_build_report.json`, `lean_build.log`, and `kernel_axioms.txt` at this
  directory's top level are the 58-module M1 checkpoint.
- `milestone1_*` and `milestone2_*` record sequential partial achievements;
  their then-open obligations are addressed by the final checkpoint above.
- `FINITE_LEAN_REVIEW.md`, `PUBLICATION_SCOPE_REVIEW.md`, `MIGRATION_NOTE.md`,
  and `source_reviews/` describe earlier packages and their limited scopes.
- `final_dependencies_incremental.txt` predates the clean build. The matching
  fresh output under `builds/final-20261106/` is the final acceptance evidence.
- The original paper and polynomial-weight certificates remain historical
  artifacts. The final far-range proof uses a new trapezoid certificate and
  continuous translation, as disclosed in the addendum.

The release [MANIFEST](../MANIFEST.json) binds current published file bytes.
GitHub CI results are separate evidence and must identify their actual commit.
