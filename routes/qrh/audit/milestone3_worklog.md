# Milestone 3 implementation log

**Current status: all three milestones accepted; see the final checkpoint at the end.**
The earlier plan and progress statements below are retained chronologically.

M1 and M2 are committed separately as `b1d00a8` and `a136d67`. Full k=6
formalization remains unfinished. This log describes new work only.

The final finite-range theorems will keep named QRH, CS v2, Rosser and
integrated-formula inputs, and add the accurately sourced finite RH input
for the low middle range. Classical inputs remain theorem parameters.

The revised method uses a simultaneous log-x/log-height translation and
trapezoid bounds for both ranges. The historical polynomial-weight argument
and certificates are preserved; the new proof is not claimed to formalize
that historical derivation line by line. All original finite cells must
still be covered by actual prime theorems, before global assembly is closed.

Exploratory numbers (not completed proof): the far pilot `[400,400.25]`
with 384 sigma cells, 125 height cells, endpoint U=115 and du=1/8 gives
an Arb budget about 0.434199143. The lower-middle reuse with rational
sigma factors 64, 3/2, 1 gives a proposed low-rank main about 0.963395219;
the auxiliary multiplier is at most 64. Both need actual Lean certificates.

At this stage DensityGridTranslation, FarDomains and FarTrapezoidCell
have compiled. The last theorem is an intermediate criterion with its
numerical premise visible. Full coverage and final assembly are pending.

## Complete incremental assembly, followed by isolated rebuild

`FinalResult` and `FinalCellCoverage` compiled successfully. The final
`SixthPowerConclusion` has exactly seven named mathematical inputs and no
local analytic conclusion or numerical-budget premise. The actual dependency
diagnostic passed in 27.562 seconds; all required lower/middle/far/tail,
primality, analytic and numerical proof constants were present, with only
standard axioms. The full output is `final_dependencies_incremental.txt`.

A literal-data performance trial did not reduce the high-memory kernel
normalization and was reverted byte-for-byte. The accepted source remains
the original proved mapIdx transformation. Its failed/stopped experiment is
recorded in `m3_lower_literal_performance_2026-11-06.json`.

All 241 current modules are now being rebuilt with two dependency-safe workers
into `lean/.lake/final-20261106`, with no old project build on LEAN_PATH.
The run record will be written to `audit/builds/final-20261106`. This log does
not pre-empt that run's result. All Lean sources and build tools are frozen
for it. Six read-only generated-source checks passed while the build ran.
Original protected paper/certificate/review bytes still match commit 2448d78.

## Milestone 3 and final acceptance, 2026-11-06

All three milestones are complete relative to the seven named external
inputs. The isolated build compiled all 241 current modules successfully
in 2690.618 seconds. The matching final dependency audit passed in 17.375
seconds, with all required actual proof dependencies and only the standard
three axioms. No local analytic-segment conclusion or numerical-budget
premise remains in the final theorem.

The final result covers every positive integer, and every point of the
94 middle and 60 far cells. The far obligation is discharged using the
disclosed trapezoid method refinement; the old polynomial-weight derivation
was not translated line by line. The lower-middle budget is 0.966283,
the difficult pilot budget 0.939772, and the far pilot budget 0.450022.
All required real enclosures and integer inequalities are kernel-checked.

Exact external inputs: QRHSevenEighths, CSv2, RosserZeroCount,
IntegratedExplicitFormula, FiniteRH3e12, CHJIIShortInterval, CHLRows.
The stronger QRH/CS-only formalization is not claimed. Four original
numerical certificates also replayed successfully in 232.797 seconds,
with protected source/data/summary hashes unchanged; six generated-source
checks passed. The original manuscript and historical reviews are preserved.

Acceptance records are under `audit/builds/final-20261106/` (or
`builds/final-20261106/` relative to the audit directory). See
`audit/milestone3_checkpoint.json`, the audit index, and
`FORMALIZATION_STATUS.md` for final scope and provenance. Earlier entries
in this log describe their historical checkpoint, not remaining local gaps.
