# AI contribution and review disclosure

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

The mathematical argument is conditional on H1/H2 and the explicitly cited
literature inputs. The present Lean development is partial as a formalization
of that complete argument. The missing steps are listed in
`FORMALIZATION_STATUS.md`; no collection of successful local compilations
changes that status by itself.
