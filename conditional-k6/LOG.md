# Publication log

## 2026-11-06: public review package

The user requested a readable academic manuscript, reproducible certificates,
Lean verification, explicit scope and dependencies, references, and an AI-use
statement. Human names, affiliations, and emails are intentionally unfilled.
The designated publication repository is
<https://github.com/bernkastel299792458/legendre-kth-powers>.

The package keeps H1 (QRH(7/8)) and H2 (CS arXiv:2507.15184v2, Corollary 1,
Table 1 rows 16--27) explicit. An independent audit of the upstream CS proof
is outside this package's assigned scope. Historical reviews are retained as
versioned evidence, not advertised as reviews of the subsequent Lean work.

The four reviewed certificate programs and their certificates were copied
with their mathematical-version bytes unchanged. The aggregate verifier's
paper link was adapted to this package and its derivation is recorded
separately. Four-module replay passed; the refined 94-cell middle segment has
at least 6.0264% budget remaining. Uniformly increasing all three CS
coefficient columns by 6% passes the full written proof chain with all other
inputs and exponents fixed.

The Chinese paper includes the integrated explicit formula, bounded-variation
trapezoid argument, Stieltjes envelope, the two finite real-variable ranges,
the infinite tail, the finite integer range, and exact range assembly. It
includes 12 references, version-specific assumptions, reproduction commands,
and an AI-use statement. PDF build and visual checks are recorded in
`audit/pdf_build_report.json`.

Substantial Lean proofs were added: 1259 prime witnesses via 5349 recursive
Lucas/Pratt nodes, exact CHL thresholds and coverage, algebraic reductions,
rational certificate checks and real-parameter coverage, selected analytic
identities, weighted von Mangoldt prime extraction, and a six-term tail bound
valid for every L >= 700. The actual build and axiom output are archived.

**The requested end-to-end Lean formalization is not complete.** In
particular, the actual zeta analytic bridges and the full transcendental
cell enclosures are not derived inside Lean. The current assembly theorem
takes `CHLRows` and `AnalyticSegmentInputs` as parameters. This publication
does not rename those segment conclusions H1/H2 or present successful local
compilation as a proof of the complete conditional theorem. See
`FORMALIZATION_STATUS.md` for the remaining obligations.

Original code is dedicated under 0BSD; original paper, documentation and
certificate data under CC0-1.0. The surrounding repository's existing
research and Apache-2.0 license are unaffected. Third-party work is excluded
from this dedication. The package is published for review, without a claim
of human expert peer review or priority.

Final local verification compiled all 46 present Lean modules successfully in
576.033 seconds. The theorem axiom audit reported only `propext`,
`Classical.choice`, and `Quot.sound`; the full parameter types remain visible.
All 28 PDF pages were rendered and inspected. A final cross-platform
reproducibility fix made the generator explicitly preserve CRLF bytes on all
platforms; its read-only check matched all 29 generated Lean files and the
Pratt JSON without changing any compiled source.

The first Linux CI run (42152323034) passed the lower, 94-cell, and 60-cell
modules but failed the historical tail replay's whole-record equality. Its
runner selected Python 3.12.16, whereas the frozen tail metadata records
3.12.10. The CI setup now pins Python 3.12.10 and runs the tail check first,
with visible diagnostics. No mathematical source or certificate bytes were
changed for this infrastructure correction. The failed run remains public.
