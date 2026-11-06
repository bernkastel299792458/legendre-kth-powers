# Formalization status

**The end-to-end conditional k=6 Lean proof is not complete. Milestones 1
and 2 are proved relative to their explicitly named literature inputs.** The
infinite tail and one complete difficult middle cell are connected to actual
prime intervals. Full finite-range coverage remains open. See the [implementation plan](FORMALIZATION_PLAN.md) and
[dated evidence log](audit/formalization_progress_2026-11-06.md).

## Milestone 1: actual prime intervals in the infinite tail

`tail_short_interval_from_inputs` proves, for every real x > 0 with
log x >= 700, that an actual prime lies strictly in (x, x + 4*x^(3/4)).
Its mathematical inputs are `QRHSevenEighths`, `CSv2`, `RosserZeroCount`,
and `CHJIIShortInterval`, with their exact statements printed in the audit.

Actual zeta zeros, finite positive analytic multiplicities, conjugation,
real-axis nonvanishing, complex-power increments, the finite layer integral,
the CS table and Rosser reductions, actual psi/theta budgets, the common
CHJII truncation, and all six tail terms are connected. The final theorem
has no local prime conclusion, weighted-error bound, total-count corollary,
certificate soundness flag, or real-axis nonvanishing parameter.

See [TailFromInputs.lean](lean/LegendreK6/TailFromInputs.lean), the
[actual proof-dependency audit](audit/milestone1_dependencies.txt), and
[AI review with its precise scope](audit/milestone1_review.md). The aggregate
build evidence is recorded separately in `audit/lean_build_report.json`.

## Milestone 2: a complete difficult cell

`M2Pilot.pilot_short_interval_from_inputs` proves `ShortInterval6 x` for
all positive real x with `715/4 <= log x <= 179`. Its complete mathematical
input list is QRH(7/8), CS v2, Rosser's zero count, and the classical
integrated explicit formula. It has no weighted-budget, numerical-certificate,
or local-prime conclusion parameter. This pilot does not use finite-height RH.

The actual zero sum is derived from the four-point integrated formula,
paired by conjugation, bounded by finite density/height grids and a proved
geometric residual, and connected to actual prime-power subtraction. All
2524 coefficient/power pairs are enclosed inside Lean. A positive Taylor
expansion reduces the main matrix to exact integer moments; its rational
inequality uses ordinary kernel reduction. The complete budget is at most
`234943/250000 = 0.939772 < 47/50 < 1`.

See [the result](lean/LegendreK6/M2PilotResult.lean),
[human-readable derivation](audit/milestone2_mathematical_note.md),
[actual proof dependencies and full types](audit/milestone2_dependencies.txt),
and [review with independence limits](audit/milestone2_analytic_review.md).
M2 evidence consists of incremental module builds, all 43 enclosure and 43
connection blocks, final aggregation, and proof-dependency/axiom checks.
The previous 58-module aggregate build report records M1; it is not a clean
rebuild of the expanded M2 source tree. A final full rebuild remains required.

## Kernel-checked components

- Exact sixth-power algebra and strict endpoint reductions.
- The actual primality of all 1259 small-range witnesses, via 5349 recursive
  Lucas/Pratt nodes. This component does not assume Sorenson–Webster or trust
  the Python generator's primality decisions.
- The CHL integer ranges and exponential thresholds, with real exponentials
  proved by Mathlib's reflective interval tactic. Given the explicitly stated
  CHL literature rows, these establish the entire lower range through
  n = 1242317999994 and its overlap with L = 167.
- Exact rational checks and continuous real-parameter coverage of the 94 new
  and 60 inherited cells; saved rational maxima, margins, and 6% scaling.
- Four-point quadratic/affine identities; the exact exponential sigma-weight
  integral; common zero-weight domination and coefficient-scaling algebra.
- The six-term tail's numerical threshold, proved using kernel-checked exp/log
  bounds, and its analytic decay on the entire range L >= 700.
- Finite von Mangoldt weighted-sum extraction of an interior prime, given
  the explicitly stated weighted lower bound and support conditions.
- Actual prime-power budgets, strict theta endpoint extraction, and the
  complete infinite-tail theorem described above.
- The current assembly is `sixth_powers_of_finite_segment_inputs`, conditional
  on only the two finite analytic segment conclusions. The older three-field
  assembly remains as a general lemma, with its inputs explicitly visible.

The final build report identifies which of these source files were actually
compiled. `#print axioms` must be read together with `#check`: an extra local
conclusion supplied as a theorem argument does not appear as a custom axiom.

## Remaining end-to-end obligations

1. Translate the finite-height RH input accurately and connect the lower
   middle cells whose kernel ceases to be flat below the CS height threshold.
2. Extend the complete trapezoid argument beyond the pilot to the full
   middle range, proving every new comparison and numerical bound used.
3. Prove the polynomial weight's full analytic formula, convergence, strict
   endpoints, Mellin bounds, and prime-power/trivial-zero budgets.
4. Cover all 94 middle and 60 far cells with actual analytic and numerical
   proof terms. Existing rational coverage and Arb output alone do not
   establish the transcendental inequalities in Lean.
5. Remove `middle` and `far` from the global theorem, audit the exact complete
   external input list, and reproduce the full pinned source build.

The unresolved obligations are not hidden behind renamed QRH/CS assumptions,
axioms, `sorry`, `native_decide`, or a blanket claim that a certificate is sound.
The paper contains the human-readable arguments; a future formalization must
produce the missing proof terms before this status can be upgraded.

## Reading the result correctly

The current strongest assembly has the complete input structure:

```text
QRHSevenEighths -> CSv2 -> RosserZeroCount -> CHJIIShortInterval ->
  CHLRows -> FiniteAnalyticSegmentInputs -> SixthPowerConclusion
```

`FiniteAnalyticSegmentInputs` contains only `middle` (167 <= log x <= 400)
and `far` (400 <= log x <= 700); the tail is supplied by its proved theorem.
This is still weaker than the final target with no local analytic conclusion
inputs. A standard-axioms-only audit does not discharge theorem parameters.

The agreed milestones concern the full project derivation relative to
individually enumerated literature inputs. Proving all those literature
theorems too, so that only QRH and CS remain as mathematical assumptions,
is a distinct, stronger scope and must not be conflated with this endpoint.

The PDF and historical reviews retain the original release's formalization
status. This document and subsequent dated build evidence record the new
implementation without expanding the historical reviewers' scope.
