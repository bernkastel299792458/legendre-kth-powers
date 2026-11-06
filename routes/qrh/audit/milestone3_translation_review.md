# Milestone 3 translation implementation and limited cross-review

Date: 2026-11-06. Implementer/reviewer: Codex subagent `lean_cpow_interval`.
This record distinguishes implementation from cross-review. It is not an
independent audit of the entire project or the complete k=6 proof.

## Implemented and compiled

`DensityGridTranslation.lean`, `TrapezoidBudgetTranslation.lean`, and
`M3MiddleUpper.lean` were implemented by this subagent. All three compiled
successfully with pinned Lean 4.36.0-rc2 and `-DautoImplicit=false`, using
`code/run_lean.ps1` and the read-only pinned dependency cache. Only minor
tactic-linter warnings remain.

The density translation theorem applies to every real k >= 4, A >= 167,
u >= 28, and d >= 0, with each sigma cell satisfying
1/2 <= lo <= hi <= 7/8 and width <= 1/1024. The actual exponential sigma
weight is compared through its exact integral. The full height-budget
translation scales q by exp(d/k) and shifts every logarithmic height by d/k.
Both the kernel and the complete geometric-tail coefficient are exactly
invariant, while the density envelope decreases. No weighted-zero
comparison is accepted as an unexplained premise.

`M3MiddleUpper.middle_upper_short_interval_from_inputs` proves
ShortInterval6 x for positive x with 715/4 <= log x <= 400. Its only
external mathematical premises are QRHSevenEighths, CSv2, RosserZeroCount,
and IntegratedExplicitFormula. It reuses the checked M2 zero budget
93977/100000 and bounds the prime-power and trivial-zero terms by
1/1000000 each. It does not assert the entire k=6 theorem.

The final six-declaration kernel audit exited 0. Every audited declaration
depends only on propext, Classical.choice, and Quot.sound. There is no
sorryAx, custom proof axiom, or Lean.ofReduceBool in these proof closures.
The preceding density-translation audit gave the same standard-axiom set.

## Read-only cross-review of the lower-middle comparison

M3LowerComparison, M3LowerIntegerCertificate, M3LowerInteger,
M3LowerBudgetDefinitions, and M3LowerMainBound were written by the root
Codex agent, not this subagent. This review covers their displayed
comparisons, index thresholds, integer interpretation, and weighted-main
connection. It does not certify the remaining finite-RH bridge or final
lower-range assembly. Actual compilation of these modules is recorded
separately by the root agent.

No issue was found within that scope:

- For s_j=(2048+j)/4096, s_j>=4/5 begins at j=ceil(6144/5)=1229;
  s_j>=5/6 begins at j=ceil(4096/3)=1366. Threshold-crossing cells use
  their left endpoint and therefore receive the larger multiplier.
- The closed domain 167<=L<=715/4 gives 0<=A-L<=47/4. The three
  exponential exponents are bounded by 47/12, 47/120, and 0, respectively,
  and hence covered by factors 64, 3/2, and 1. Both endpoints are included.
  The reverse integral comparison correctly uses L<=A to discard L/A<=1.
- The baseline reverse growth is exp((A-L)/3), also covered by the
  exp(47/12)<=64 bound.
- doubleSigmaRows applies integer multipliers 128, 3, and 2, followed by
  exactly one overall half-factor. Every sigma moment, including the
  Taylor remainder, is linear in that coefficient. Consequently
  193/100 becomes 193/200 with no omitted factor of two.
- The conjugate-zero factor and geometric residual already present in
  the M2 height coefficients are preserved. The half-factor only undoes
  the deliberate doubling of the sigma multipliers.
- weightedMain changes only the sigma coefficient. The original exponent,
  heightV, heightCoefficient, and degree-21 remainder remain in place,
  so the shifted exponential and dyadic monotonicity proofs apply to
  the intended expression.

The hashes below identify exact snapshots. Subsequent source edits require
checking the changes; this record is not blanket approval of later versions.

## Source snapshots

| Source | SHA256 |
|---|---|
| `DensityGridTranslation.lean` | `4d9bb4b3732565cfd9ab5c7ecbc1f6b4018cadd90bffda71622648f9084fddb2` |
| `TrapezoidBudgetTranslation.lean` | `d2ffd1e40ee7d235dfd9f470a8ead8f0266068d8ba63a2bec6a9f6aa98f51c2c` |
| `M3MiddleUpper.lean` | `74d1ab5007187d9d145ce6cfd6abb37c07a708d7afb28e70704053ab41688be5` |
| `M3LowerComparison.lean` | `68b15734a6ab800b49f48eb051575c4684c331f2a10aa2497d19b542cc19d5a7` |
| `M3LowerIntegerCertificate.lean` | `7813bc1b451e798f5b720158ddbc41b91b5ac65cf49b1f6f3c9c95eb49be9bab` |
| `M3LowerInteger.lean` | `960519b8775e2167d4a8be5e32cc149571512beed371ba1cefc009aa74b35245` |
| `M3LowerBudgetDefinitions.lean` | `cc6f01292529aa4f3faa229cba4a92bc7bfaaba36add4139fef618bf3ec7979f` |
| `M3LowerMainBound.lean` | `c1b9c93b11322d7bb5f80ef3f7f557a0711df364d06fed9e010aa91d25d6f1ff` |

## Final translation/middle-upper audit output

```text
'LegendreK6.trapezoidHeightBudget_translation_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreK6.one_add_exp_div_translate_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreK6.M3MiddleUpper.shifted_zero_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreK6.M3MiddleUpper.upper_prime_power_budget_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreK6.M3MiddleUpper.middle_upper_at_log_from_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreK6.M3MiddleUpper.middle_upper_short_interval_from_inputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
LegendreK6.M3MiddleUpper.middle_upper_short_interval_from_inputs (HQ : LegendreK6.QRHSevenEighths)
  (HC : LegendreK6.CSv2) (HR : LegendreK6.RosserZeroCount) (HF : LegendreK6.IntegratedExplicitFormula) (x : ℝ)
  (hx : 0 < x) (hlo : 715 / 4 ≤ Real.log x) (hhi : Real.log x ≤ 400) : LegendreK6.ShortInterval6 x
```

## Subsequent lower-range build confirmation

The root agent reported successful compilation of the integer certificate,
its real interpretation, weightedMain<=193/200, and M3LowerResult. This
subagent then inspected the resulting object metadata and the final source
signature; this was not an independent clean rebuild. The exposed theorem
`M3Lower.lower_middle_short_interval_from_inputs` has only QRHSevenEighths,
CSv2, RosserZeroCount, IntegratedExplicitFormula, FiniteRH3e12, positive x,
and 167<=log x<=715/4 as inputs. Its Z and budget inequalities are local
derivations, not extra theorem parameters.

| Module | Source SHA256 | Object modification time (UTC) | Object bytes |
|---|---|---|---|
| `M3LowerIntegerCertificate` | `7813bc1b451e798f5b720158ddbc41b91b5ac65cf49b1f6f3c9c95eb49be9bab` | 2026-11-06T06:05:39.690005+00:00 | 83560 |
| `M3LowerInteger` | `960519b8775e2167d4a8be5e32cc149571512beed371ba1cefc009aa74b35245` | 2026-11-06T06:08:04.565992+00:00 | 216080 |
| `M3LowerMainBound` | `c1b9c93b11322d7bb5f80ef3f7f557a0711df364d06fed9e010aa91d25d6f1ff` | 2026-11-06T06:09:30.041953+00:00 | 47464 |
| `M3LowerResult` | `c342c0af5c7639208881e63647a40f360546acd43261ef503e35b6328af05279` | 2026-11-06T06:09:51.354369+00:00 | 246168 |

## Far-range handoff and final compiled result

The far pilot, its numerical certificates, and FarUniformBudgets were
implemented by the `lean_prime_power_budget` subagent. That subagent
explicitly transferred its uncompiled M3FarTranslation draft to this
subagent. The draft was moved to M3FarUpper, adapted to the shared
q-envelope lemma, compiled first with an explicit pilot-budget premise,
and then connected to the actual compiled M3Far.zeroBudget_le theorem.
The final public theorem has no pilot-budget hypothesis. This is a
collaborative implementation, not an independent reproduction of the
far numerical certificate.

`M3FarUpper.far_short_interval_from_inputs` was compiled with
`-DautoImplicit=false` and proves ShortInterval4 x on the complete closed
range 400<=log x<=700. It uses only QRHSevenEighths, CSv2, RosserZeroCount,
and IntegratedExplicitFormula, plus positive x and the stated domain.
The zero budget is <=22501/50000; each of the two remaining budgets is
<=1/1000000. The final kernel dependency audit exited 0 and reported
only the three standard axioms.

| Source | SHA256 | Object modification time (UTC) |
|---|---|---|
| `M3FarUpper.lean` | `e61e8a3d5e60a25686d47033b2d2eb146979b91ab137f1ece5516615efee329e` | 2026-11-06T06:14:50.458157+00:00 |
| `M3FarResult.lean` | `096699fca4a1f745cb93584463158cc010dc48b9591d29a631024902d45f6862` | 2026-11-06T06:14:20.935377+00:00 |
| `FarUniformBudgets.lean` | `7280279af681b0c11f9b693812f02032ee74fb54bf287d3b0d038bb0b87cd3b3` | 2026-11-06T06:07:48.769379+00:00 |

```text
'LegendreK6.M3Far.zeroBudget_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'LegendreK6.M3FarUpper.far_short_interval_from_inputs' depends on axioms: [propext, Classical.choice, Quot.sound]
LegendreK6.M3FarUpper.far_short_interval_from_inputs (HQ : LegendreK6.QRHSevenEighths) (HC : LegendreK6.CSv2)
  (HR : LegendreK6.RosserZeroCount) (HI : LegendreK6.IntegratedExplicitFormula) (x : ℝ) (hx : 0 < x)
  (hlo : 400 ≤ Real.log x) (hhi : Real.log x ≤ 700) : LegendreK6.ShortInterval4 x
```

## Final read-only semantic check while acceptance is pending

This additional check was performed during the isolated whole-tree rebuild.
No Lean source was changed and no compiler was run for this check. Final
acceptance remains pending the rebuild and its matching dependency audit.
No semantic issue was found in the scope below; this is still the same
implementation-overlapping AI cross-review, not independent peer review.

The type of `sixth_powers_from_named_inputs` is exactly seven named inputs
followed by SixthPowerConclusion. Expanding that conclusion gives every
natural n>=1 and an actual Nat.Prime p with n^6<p<(n+1)^6. The companion
short theorem has the strictly stronger upper endpoint n^6+6*n^5. There
is no local segment conclusion, weighted-zero bound or certificate-validity
flag among the final parameters. Older conditional assembly lemmas are
instantiated internally by the proved segment theorems.

The seven actual input definitions were read directly:

| Input | Meaning checked in source |
|---|---|
| QRHSevenEighths | Every actual nontrivial zeta zero in the open critical strip has real part <=7/8. |
| CSv2 | Twelve explicit closed sigma rows, T>=3e12, positive-height multiplicity-aware density counts, and the stated powers/constants; not a weighted-zero bound. |
| RosserZeroCount | The full absolute-error counting formula for T>=2, using the defined closed rectangle and constants 137/1000, 443/1000, 397/250. |
| IntegratedExplicitFormula | Convergence of the actual height-truncated zero-primitive sum for t>1 to the literal unweighted integrated-Psi formula. |
| FiniteRH3e12 | Actual nontrivial zeros with 0<gamma<=3e12 have real part 1/2; no simplicity assumption. |
| CHJIIShortInterval | The actual psi difference and zero increment share one existential Tstar in [T,2T], with the source domains and error constant 1447/500. |
| CHLRows | Exactly twelve explicit CHLInterval propositions, whose source orientation is y*(1-1/Delta)<p<=y. |

The external source theorems themselves were not reproved by this review.
In particular, this is a downstream theorem relative to all seven inputs,
not a theorem whose only premises are QRH and CS v2.

Endpoint and coverage checks:

- n=0 is explicitly excluded; `small_prime_1` supplies p=2 for n=1. For
  the CHL branch n>=2, the endpoint n^6+6*n^5=n^5*(n+6) is composite,
  converting the source's closed upper endpoint to a strict inequality.
  The proved binomial gap then gives the strict (n+1)^6 endpoint.
- The log-domain splits at 167, 715/4, 400 and 700 include their boundary
  points. The real-to-integer and fourth-to-sixth reductions preserve
  strict prime endpoints. There is no uncovered joining point.
- Certificates contains exact counts 94 and 60, checked adjacent closed
  cells, and coverage for every real parameter in [167,400] and [400,700].
  FinalCellCoverage applies actual continuous prime-interval theorems on
  each listed cell; it does not use a saved rational maximum as an
  enclosure premise. The global theorem itself uses continuous segments.
- The current M3 worklog, far-method note, formalization status, and proof
  map disclose the new trapezoid/continuous-translation route and preserve
  the historical polynomial certificates. They do not claim a line-by-line
  formalization of that earlier derivation or a new global 6% sensitivity
  theorem. Historical chronological entries retain their earlier scope;
  the current status explicitly leaves isolated-build acceptance pending.

The following hashes identify the exact semantic source snapshots read.

| Source | SHA256 |
|---|---|
| `FinalResult.lean` | `57b9148fbdd078083abf425c2d7fc552bff551a83c97ef79a539c63147a0ea24` |
| `FinalCellCoverage.lean` | `af81a4c1efbdd568f994b8e4797572845b48e7e17be4f543bebaed02d8595e5b` |
| `Definitions.lean` | `41eb5d0dd3e5debfb2821c9ecf9eb6b71d0f3df1737d9b3316fbda0f373056ac` |
| `Reduction.lean` | `b9cb1ebad378ba363b3b9a69d49b12b558957950303540009a08592ded3468f4` |
| `Assembly.lean` | `e862e4484f224258f5f0a8c9a3dc251c20b9501227c84486e62ac4d436cd5cf6` |
| `AssemblyWithTail.lean` | `a89e5068affa44f1bd5c2a2324f99c9e6c9fab4965d2f4ed39db8a46b012a3c3` |
| `LowerRange.lean` | `50a9b13f8f82200a8fe998fe3d996751569ea3267c2498241b063c9c38b2494f` |
| `PrimeWitnesses.lean` | `930ae7f08c0033e64156087d889ab4d4089677cd8f94b7c49db2888a528c0f32` |
| `CHL.lean` | `1b30f370040ceadfeffc325036f0ce0cdd9dc2f4376998dcb8b6deafd452ee4e` |
| `CHLRange.lean` | `4c4e7c0a8a3950a071cd86b698beca2aeefe8959fa93f9a7c43fd32fce9239dd` |
| `DensityInput.lean` | `990d6e27408ddfd9e69db0fad1c0c6580460d96c15f99a44cceb8a6b581146a9` |
| `LiteratureInputs.lean` | `feb8446dcfb232adedec2937a271ed010e35f8addeec240a60f75c2c74c8df78` |
| `IntegratedExplicitFormula.lean` | `9dfad65f0a4a3849e4f89f6aca7b0f25511a2958466e1bd2712845d8e368aced` |
| `FiniteRHInput.lean` | `d502c92b71fe95655c23d0e6d6a8d7de2e8376d707e6eeeb62d2d8bd2460a266` |
| `Certificates.lean` | `47418f58ac24fc5d7533ad537a8523c6e6c3432e7a41aeac73d375770a7a6b52` |
| `ZetaZeros.lean` | `9fb065bdae1cc73f614f433628ad98e97f81ceec74e8ad093de9e1eb24c6de1d` |
