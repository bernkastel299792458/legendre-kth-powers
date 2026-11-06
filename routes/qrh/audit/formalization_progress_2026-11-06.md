# Formalization implementation log — 2026-11-06

Baseline: commit `2448d78d8060a840800d222b8c0e4ccd23a9506b`.
Toolchain: Lean `v4.36.0-rc2`; Mathlib
`9d581dfff2e41de989072ea63abf3daf69311520`.

The user authorized implementation of all three milestones. Work begins on
an isolated Codex branch; the existing public release and the traditional
research workspace are not overwritten. The borrowed dependency cache is
read only; project build outputs remain local to this checkout.

## Initial implemented pieces

The following modules have individually compiled; full integration and the
tail theorem must be checked separately before declaring milestone 1 done.

- `PrimePowerBudget`: actual weighted nonprime sums bounded by `W*(psi-theta)`,
  the unconditional Chebyshev square-root/log bound, the manuscript budget
  in its used domain, and actual strict-open-interval prime extraction.
- `CpowInterval`: norm of the actual complex-power increment, then its finite
  sum with natural multiplicities.
- `FiniteZeroLayer`: the finite layer integral, closed sigma thresholds,
  low-beta base contribution, and integrability.
- `TailDomains`: all selected tail parameter domains and exact exponential,
  real-power, square-root, and logarithm conversions.
- `TailErrorBudgets`: actual truncation expression, actual prime-power
  difference, and full right-endpoint contribution bounded by the last
  three terms of the existing six-term function.
- `DensityInput`: actual QRH and CS v2 statements and the derivation of the
  manuscript's coarser tail density bound from the twelve-row input.
- `LiteratureInputs`: actual shared-truncation CHJII statement, literal
  closed-rectangle Rosser count, and derivation of `N(T) <= T log T`.

The real-axis and final density/prime assembly work is in progress. These
initial successes do not yet remove `H.tail`.

## Subsequent closure of the actual tail

`ZetaZeros` now proves real-axis nonvanishing in `(0,1)` without a new
literature input. It uses Mathlib's existing completed zeta and modified
theta/Mellin kernel: positivity and integrability give a comparison with
the values at 2 and -1, the functional equation identifies these values,
and the pole correction rules out a real zero. The final conjugation sum
identity therefore has no nonvanishing hypothesis left to discharge.

`TailDensity` instantiates the finite layer integral with actual positive
zeros. `TailZeroSum` then incorporates the actual complex-power increments,
positive/negative pairing, height enlargement, and Rosser's derived total
count. `TailFromInputs` connects this to the actual CHJII residual, actual
Chebyshev functions and strict endpoint extraction. Its complete final type
contains exactly QRH, CS v2, Rosser and CHJII, besides x and its domain.

The tail module compiled successfully. The proof-dependency diagnostic
`Milestone1Dependencies.lean` also passed, recording the actual transitively
used local proof constants and printing all four input definitions. The
tail theorem's axioms are only `propext`, `Classical.choice`, `Quot.sound`.
The audit does not treat that list as a substitute for inspecting parameters.

`AssemblyWithTail` supplies the tail to the earlier general assembly lemma;
its replacement input structure contains only `middle` and `far`. The full
58-module rebuild was started after all mathematical source edits settled;
its result will be appended below before accepting the milestone checkpoint.

The CS input annotation now explicitly says that the project's open-strip
count restricts the source's count; this weakens the upper-bound statement
instead of strengthening it. Rosser's two relevant pages were also rendered
and visually checked after text extraction, confirming the closed rectangle
and the theorem's `T >= 2` domain. Local source PDFs are not redistributed.

## Source-to-statement checks

CS: [arXiv:2507.15184v2](https://arxiv.org/html/2507.15184v2), Corollary 1
and Table 1, rows 16–27. All finite decimal constants are exact rational
numbers. The accepted input uses both original exponents and closed sigma
intervals, with `0 < gamma <= T` and true analytic multiplicities. The
tail's enlarged constants and cubic logarithm are *proved consequences*,
not substituted into the accepted statement. This checks the interface;
it is not a repeat of the separately assigned audit of the CS derivation.

CHJII: [arXiv:2402.04272v3](https://arxiv.org/html/2402.04272v3), Theorem 1.3
and Table 1, `log(x_M)=40`, `alpha=1/2`, `omega=0`, `M=2.894`. The input
retains one common `Tstar` in `[T,2T]`, `max(51,log(x)^2)<T`, and
`T<(sqrt(x)-2)/4`. The complex norm of the actual residual expresses the
stated O-star bound. Two independently truncated one-point formulas are
not substituted for this theorem.

Rosser: the publisher PDF returned HTTP 403 in this run. The same author's
[public HDR](https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf)
was downloaded and checked at printed p. 34, (2.2)–(2.3), and printed p. 82,
Theorem 86. The latter explicitly states `T >= 2`, the constants 0.137,
0.443, 1.588, and the closed rectangle `0 <= beta <= 1, 0 <= gamma <= T`.
The Lean input preserves this larger set as `rosserCount`; a proved subset
relation transfers its upper bound to `totalZeroCount`. Consequently no
unstated real-axis nonvanishing fact is needed for this transfer. The
original 1941 proof is not being re-proved or independently checked here.

## Verification commands

During development, each module is checked with `code/run_lean.ps1`, using
the pinned native Lean executable and the read-only matching Mathlib cache.
Final milestone evidence must include the aggregate build, full theorem
types and axioms, a review of assumptions, and a refreshed release manifest.

## Milestone 1 accepted checkpoint

The aggregate build completed on 2026-11-06 at 04:36:57 UTC: all 58 current
Lean modules passed, in 1298.034 seconds. `lean_build_report.json` records
every source hash and pinned dependency revision. The reviewer checked that
all 58 current source hashes match the report. The new global assembly and
its audit compiled as part of that build. Generated audit text was normalized
to LF for repository storage; no mathematical output was changed.

The complete tail theorem has exactly four mathematical inputs:
`QRHSevenEighths`, `CSv2`, `RosserZeroCount`, and `CHJIIShortInterval`.
It concludes an actual strict prime interval for every positive real x with
`700 <= log x`. Its local analytic and arithmetic dependencies are present
in the proof term, and its axiom report contains only `propext`,
`Classical.choice`, and `Quot.sound`. The replacement global assembly's only
remaining project-specific conclusion inputs are `middle` and `far`.

See `milestone1_review.md` for the scope and limits of the AI cross-check.
Milestone 1 is accepted relative to those named literature inputs. Milestones
2 and 3 remain open; `end_to_end_H1_H2_formalization` remains false. The frozen
paper, historical reviews, original certificate data, and original core
certificate programs were not changed by this checkpoint.

## Milestone 2 completed proof checkpoint

The final `M2Pilot.pilot_short_interval_from_inputs` compiled successfully.
For every positive x with `715/4 <= log x <= 179`, it proves the actual
strict prime interval `ShortInterval6 x` from precisely QRH(7/8), CS v2,
Rosser's count and the classical integrated explicit formula. No numerical
budget, weighted zero estimate or local prime conclusion remains as an input.
All 43 enclosure blocks, 43 real-to-dyadic connection blocks, integer moments
and final aggregation passed. The complete budget is at most
`234943/250000 = 0.939772 < 47/50`. The final actual-dependency diagnostic
passed in 24.0 seconds, with only the standard three Lean axioms.

The human-readable note's height-index notation was corrected: moments use
the right endpoints `t_i = u_(i+1)`, not the starting node `u_0`. Lean already
used the correct indices. Original paper/certificates/reviews are preserved.
This checkpoint uses recorded incremental builds; it does not claim a new
clean whole-tree rebuild. The earlier aggregate report remains M1 evidence.
Full finite-range coverage, final assembly and final reproducible build
remain milestone 3 work; full conditional k=6 formalization is not complete.
