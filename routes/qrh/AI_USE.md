# AI contribution and review disclosure

## AI authors and route responsibilities

At the project owner's explicit direction, the project credits **Claude and
Codex** as its AI authors, with the following division of work:

| AI author | Research responsibility | Contribution to this QRH paper |
|---|---|---|
| **Claude (Anthropic)** | Leads the traditional explicit-estimate route | Supplied the earlier 76-cell review and its recommendations; that report's historical scope is retained. |
| **Codex (OpenAI)** | Leads the QRH(7/8) route | Principal analytic development, numerical implementation, certificate refinement, Lean components, and manuscript preparation in this package. |

This attribution names the AI systems and their recorded contributions.
It does not identify them as human researchers, assign unrecorded work to
either system, or claim that both independently verified every current file.
Future work follows the same route responsibilities; cross-review remains
identified separately from implementation.

## Recorded work and review scope

OpenAI Codex assisted with literature retrieval and transcription, analytic
proof development, kernel selection, Python/Arb programming, debugging,
certificate production, Lean source generation, and manuscript preparation.
Separate agent contexts cross-checked parts of the work. They shared project
materials and do not constitute human expert peer review.

The project owner supplied a Claude review of the earlier 76-cell version.
It prompted explicit separation of QRH and CS v2, correction of the input
version documentation, and the refined 94-cell certificate. That review does
not certify the later Lean implementation. Subsequent reports state their
actual scope, including whether the reviewer also contributed to an
implementation. Original reports are retained under `audit/source_reviews/`.

The human research initiator set the objectives, accepted the two research
premises, and requested open dependencies, reviewable artifacts, and this
disclosure. Human author names, affiliations, and contact details are not
filled in. No named human specialist has been recorded as completing a
line-by-line review. AI providers and cited authors have not endorsed this
result, and no journal acceptance is claimed.

Precise service-side model build identifiers, every prompt, and random seeds
were not completely recorded. No exact model-replay claim is made. What is
reproducible is the frozen mathematical input, deterministic program/source
generation, specified toolchain, certificates, and compiler/verification
commands. Model agreement is not proof.

The argument is conditional on seven individually named inputs, including
QRH and CS v2. The final downstream theorem has passed a fresh 241-module
build and matching dependency audit, without local analytic conclusions or
numerical budgets as inputs. See `FORMALIZATION_STATUS.md` and the records
in `audit/builds/final-20261106/`. Those external inputs were not re-proved.

The new formal argument uses a continuous grid translation, a finite-RH
lower-range comparison and a trapezoid far-range certificate. It does not
claim a line-by-line translation of the historical polynomial-weight proof.
Codex agents implemented and cross-reviewed these changes; each review
distinguishes its author's implementation from independently read code.
The Claude review retains its historical scope. The new method is described
in `paper/lean_formalization_addendum.md`.
