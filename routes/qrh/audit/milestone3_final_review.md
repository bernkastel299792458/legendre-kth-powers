# Milestone 3 final-assembly cross-review

Date: 2026-11-06. Reviewer: Codex sub-agent `lean_prime_power_budget`.

**Final disposition: PASS for milestone 3 and the complete downstream k=6
formalization relative to the seven explicitly named literature inputs.**
The 241-module fresh project build and its matching final dependency audit
have passed. The reviewer checked the complete final types, all four final
axiom reports, required proof dependencies, and current source/artifact hash
bindings. No local analytic-segment or numerical-budget premise remains.
This does not certify or reprove the seven upstream inputs.

Sections 1–8 preserve the review checkpoints before final build acceptance.
Their earlier PENDING statements are superseded by the final evidence and
judgment in Section 9. The reviewer's implementation overlap and the
distinction between inspecting a recorded build and personally rerunning it
remain explicit below.

## 1. Scope and independence

The reviewer did not implement the final `FinalResult` or `FinalCellCoverage`
assembly, the CHL integer coverage, the generated prime witnesses, finite-RH
interface, lower-middle comparison, or the general forward-translation
theorems. Their review here is an additional AI cross-check by a different
agent from their implementers. It is not human expert peer review.

The reviewer implemented M1's `PrimePowerBudget`, `TailDomains`, and
`TailErrorBudgets`; M2's `IntegratedPsi`, `IntegratedExplicitFormula`,
`MiddleDomains`, `TrapezoidPrime`, and `M2PilotGrid`; and the M3 far-domain,
far-cell, far numerical-pilot and certificate modules. The initial far
translation draft was also supplied by this reviewer before another agent
completed `M3FarUpper`. Assessment of these portions is self-review. The
whole proof must not be described as wholly independently reviewed by this
agent. Earlier scope and source checks remain recorded in
[M1 review](milestone1_review.md) and
[M2 review](milestone2_analytic_review.md).

This checkpoint combines source inspection with reading the root agent's
recorded incremental diagnostic. The reviewer did not rerun that aggregate
diagnostic or a fresh full build. Source inventory counts below are separate
read-only checks, not substitutes for kernel verification.

## 2. Final theorem and assumption boundary

The inspected final type is:

```lean
sixth_powers_from_named_inputs
  (HQ : QRHSevenEighths) (HC : CSv2) (HR : RosserZeroCount)
  (HI : IntegratedExplicitFormula) (HFR : FiniteRH3e12)
  (HJ : CHJIIShortInterval) (HCHL : CHLRows) : SixthPowerConclusion
```

Here `SixthPowerConclusion` expands to
`∀ n : ℕ, 1 ≤ n → ∃ p : ℕ, Nat.Prime p ∧ n^6 < p ∧ p < (n+1)^6`.
The separately checked `sixth_power_short_from_named_inputs` has the same
seven inputs and proves the stronger `p < n^6 + 6*n^5` for each positive
integer. Neither theorem quantifies over a surrogate prime predicate.

The old `AnalyticSegmentInputs` and `FiniteAnalyticSegmentInputs` structures
still occur inside the proof dependency closure. They are constructed from
proved middle, far, and tail theorems in `FinalResult`; they are **not** final
theorem parameters. Likewise the generic budget criteria in the proof are
instantiated with certified bounds. Their existence as useful conditional
lemmas is not an unresolved final assumption.

| Input | Inspected boundary and provenance |
|---|---|
| `QRHSevenEighths` | A statement about the real parts of actual nontrivial zeros of `riemannZeta`. It contains no prime interval or project-specific weighted estimate. The project accepts the upstream QRH result; this review does not reprove it. |
| `CSv2` | The twelve explicit v2 table rows, actual multiplicity count, source height threshold, real-power and logarithmic exponents. The M1 review checked the statement and all 36 constants against the source. Restricting the source's strip count to the project's open strip weakens an upper bound; it does not strengthen it. No new review of the upstream CS derivation was performed. |
| `RosserZeroCount` | The full counting error formula, retaining coefficients `0.137`, `0.443`, `1.588` and the source's closed rectangle. The coarse bound used downstream is derived through a proved subset comparison. The original Dusart pages were checked by the root agent, not independently by this reviewer; this review checks the code and that disclosed provenance. |
| `IntegratedExplicitFormula` | The actual height-truncated zero sum converges to the literal classical expression for `t > 1`. The affine signs, actual zeta derivatives, actual analytic multiplicities and trivial-zero series are visible in the definition. It assumes neither a trapezoid formula nor its error budget. The earlier M2 review visually checked the cited Hildebrand formula and absolute convergence statement. |
| `FiniteRH3e12` | For actual nontrivial zeros with `0 < Im rho <= 3*10^12`, the real part is `1/2`. It assumes no simplicity or alternative zero enumeration. This is an explicit additional literature input used in the lower-middle range. |
| `CHJIIShortInterval` | The short-interval formula uses a single shared `Tstar` in `[T,2*T]`, the two endpoint errors, nonnegative `h`, and the stated strict inequalities on `T`. The selected row is `log(x_M)=40`, `alpha=1/2`, `omega=0`, `M=2.894`. No weighted-zero bound is included. |
| `CHLRows` | Precisely the twelve corrected source statements, with prime interval `(y*(1-1/Delta),y]`, are supplied. All subsequent integer thresholds, overlaps and conversion to a strict right endpoint are proved locally. |

The current review independently rechecked the closed finite-RH cutoff
against the abstract and Theorem 1 of
[Platt–Trudgian v1](https://arxiv.org/pdf/2004.09765v1). The theorem reaches
a height above `3*10^12`, so the chosen cutoff is a restriction. The
underlying computational verification is accepted as a literature theorem,
not reproduced here.

The statement and chosen constants in
[CHJII v3, Theorem 1.3 and Table 1](https://arxiv.org/html/2402.04272v3)
were rechecked. In particular the shared truncation is stated for the
interval directly; the code does not select two unrelated truncations and
silently identify them.

The reviewer also directly compared all twelve `CHLRows` pairs with
[CHL v3, Theorem 1 and Table 2](https://arxiv.org/html/2103.05986v3).
The thresholds are `4*10^18` and `exp(43), exp(46), exp(50), exp(55),
exp(60), exp(75), exp(90), exp(105), exp(120), exp(135), exp(150)`;
all corresponding integer Delta values match. The source's closed right
endpoint is preserved at the input, and only converted later using the
specific composite integer endpoint. These statement checks do not certify
the upstream numerical work of CHL.

## 3. Actual coverage and strict endpoints

Let `L = log x` in the positive-real analytic ranges. The final assembly uses
the following overlapping closed ranges:

| Range | Actual local conclusion |
|---|---|
| Positive integers with `log((n:Real)^6) <= 167` | `NatSixthShort n` from the concrete small-prime witnesses and CHL integer coverage |
| `167 <= L <= 715/4` | `ShortInterval6 x` from finite RH, the scaled kernel and the backward density-weight comparison |
| `715/4 <= L <= 400` | `ShortInterval6 x` from the M2 pilot and proved forward translation |
| `400 <= L <= 700` | `ShortInterval4 x` from the new far trapezoid pilot and proved forward translation |
| `700 <= L` | `ShortInterval4 x` from the completed nonsmoothed CHJII tail |

The branch conditions in `FinalResult` and `Assembly` assign every equality
at `167`, `715/4`, `400`, and `700` to a proved branch. No open gap remains.
The analytic theorems quantify over all real `L` in their ranges, not only
grid nodes, rational values or sampled values.

For the integer lower range, read-only counting found exactly 1259 theorem
declarations `small_prime_1` through `small_prime_1259`, in order, and 5349
distinct primality declarations in 27 Pratt blocks. The first witness is
the actual prime 2. The dispatch tree covers every integer in `1..1259`.
The reviewer inspected its interface, representative certificates and the
coverage code; this is not a claim to have manually rechecked every modular
arithmetic calculation in all 5349 nodes. Those calculations are Lean
proof obligations, not trusted Python primality decisions.

The CHL branch starts at 1260 and reaches `1242317999994`. Each row supplies
the condition `n <= 6*(Delta-1)` and a proved exponential lower threshold.
`lower_join_exp` proves `exp(167) < (1242317999994:Real)^6`, which supplies
the overlap with the analytic range. For `n >= 2`, the upper integer
endpoint `n^6+6*n^5 = n^5*(n+6)` is composite. Excluding equality converts
the CHL conclusion `p <= n^6+6*n^5` into a strict upper inequality without
strengthening the cited input.

`Reduction` proves the real-power equality at `x=(n:Real)^6`, carries the
actual natural prime through the real/natural casts, and proves the exact
integer binomial gap `n^6+6*n^5 < (n+1)^6`. For the far and tail ranges it
first derives `x >= 1` and uses `4*x^(3/4) <= 6*x^(5/6)`. Thus the shorter
fourth-power length gives the required sixth-power interval while preserving
both strict endpoints.

## 4. Historical 94 and 60 cells

`Certificates` has exact checks of the saved list lengths and joins, and a
coverage lemma quantified over **real** points with cast rational endpoints.
`FinalCellCoverage` proves that every saved refined cell lies in `[167,400]`
and every saved far cell lies in `[400,700]`. Its two theorems then supply
actual strict prime intervals at every positive real `x` whose logarithm
lies in the respective closed cell:

- `all_94_cells_actual_prime_intervals` concludes `ShortInterval6 x` from
  HQ, HC, HR, HI and HFR.
- `all_60_far_cells_actual_prime_intervals` concludes `ShortInterval4 x`
  from HQ, HC, HR and HI.

The rational-to-real endpoint casts were checked. The saved numerical
maxima are not premises of these theorems. These results establish the
interval conclusions for all historical cells; they do not assert equality
between their old saved numerical budgets and the new proof budgets.

The far proof is a new trapezoid argument, covering the same far range.
It is not a line-by-line formalization of the historical polynomial-weight
derivation. Preserving the historical source and documenting this difference
is mathematically appropriate.

## 5. New lower-middle comparison and numerical semantics

The separate low-height term retains every zero with `0 < gamma <= H`,
including equality at `H=3*10^12`. Actual analytic multiplicities remain in
all sums. Above H the scaled min-kernel bound is applied; the comparison
enlarges the reference high sum to a whole reference sum with nonnegative
extra low terms. It therefore overcounts harmlessly rather than dropping a
low-height residual. The conjugate factor is exactly two.

The backward weight comparison uses the actual left sigma endpoint. With
`A0=715/4`, `167 <= L <= A0`, and `r=exp((L-A0)/6)`, it proves
`r*W_j(L) <= exp((5/6-s_j)*(A0-L))*W_j(A0)`. The piecewise coefficients
64, 3/2 and 1 follow from the indices `j < 1229`, `j < 1366`, and the
remaining indices. A cell crossing a threshold receives the safe larger
coefficient according to its left endpoint.

The doubled integer table multiplies the sigma coefficient by 128, 3 or 2,
and preserves the corresponding sigma power. `double_factor` and
`double_power` tie its list index to the actual `Fin 1536` coefficient;
they do not replace the genuine finite sum by an unrelated row list. The
moment denominator remains `2^(48*(d+1))`. The doubled rational budget is
bounded by `193/100`, and the scaling identity divides it by exactly two,
giving `193/200` for the actual weighted main expression.

The remaining upper bounds are `64/50000` for the auxiliary term and
`10^-6` each for the finite-RH low term, prime powers and trivial zeros.
The resulting total `0.966283` is strictly less than one. It is a new
conservative formal bound, not an assertion that the older coefficient
sensitivity certificate was also formalized.

The new far pilot uses 384 sigma cells and 125 height cells. Its certified
bounds sum to `9/20 + 1/50000 + 2/10^6 = 225011/500000`, with zero-only
budget `22501/50000`. The original M2 total remains
`234943/250000 = 0.939772 < 47/50`. The factor of two for conjugate zeros,
the division of Phi by the height-node square in the coefficient identity,
and the last-node geometric residual are present in the actual expression
identities. The residual controls remaining weights of low zeros as well
as high zeros; it is not merely a tail count above the last node.

Before the final rebuild, a performance experiment tried replacing repeated
reduction of the lower table's `mapIdx` by literal data, tied to the original
table with a kernel equality proof. It did not improve memory use and was
reverted. The reviewer subsequently inspected the restored accepted source:
`doubleSigmaRows` is again defined directly by `sigmaRows.mapIdx`, and
`double_factor` / `double_power` use `List.getElem_mapIdx`. No additional
literal table or lower-data generator is in the accepted proof. The root
reported byte-for-byte restoration; hashes of the inspected restored files
are recorded below. This does not yet assert a successful new aggregate
build.

## 6. Incremental kernel and dependency evidence

The reviewer read [FinalDependencies.lean](FinalDependencies.lean) and its
recorded output [final_dependencies_incremental.txt](final_dependencies_incremental.txt).
The root reported exit 0 in 27.562 seconds. The inspected output includes
`FINAL_K6_REQUIRED_PROOF_DEPENDENCIES_PRESENT`, the four complete final
theorem types, and expansions of all seven named inputs.

The diagnostic traverses local constants in actual proof values and types,
and checks required dependencies. Those include the lower scaled-weight
comparison, actual low-height RH sum, lower integer moment budget, both
forward translations, M2 and M3 numeric factors, the real trapezoid kernel,
integrated weighted identity, full geometric residual, actual tail proof,
real-axis nonvanishing, conjugate multiplicities, small-prime witnesses and
CHL integer coverage. The mere presence of helper statements or imports
would not satisfy this check if absent from the proof closure.

The main theorem, stronger theorem, and two cell-coverage theorems each
have the printed axiom set `[propext, Classical.choice, Quot.sound]`.
Neither `sorryAx` nor `ofReduceBool` occurs in these axiom lists. Combined
with the printed full types, this rules out confusing named theorem
parameters with absent custom axioms. It does not itself validate a
literature premise or establish reproducibility in a fresh build tree.

Stable reviewed snapshot hashes (SHA-256):

| File | SHA-256 |
|---|---|
| `lean/LegendreK6/FinalResult.lean` | `57b9148fbdd078083abf425c2d7fc552bff551a83c97ef79a539c63147a0ea24` |
| `lean/LegendreK6/FinalCellCoverage.lean` | `af81a4c1efbdd568f994b8e4797572845b48e7e17be4f543bebaed02d8595e5b` |
| `audit/final_dependencies_incremental.txt` | `430d823cb8ddbdbcba386d46ab77679d7d6fcf1147b9a89d2a2709636fe238aa` |
| `lean/LegendreK6/M3LowerIntegerCertificate.lean` (restored) | `7813bc1b451e798f5b720158ddbc41b91b5ac65cf49b1f6f3c9c95eb49be9bab` |
| `lean/LegendreK6/M3LowerInteger.lean` (restored) | `960519b8775e2167d4a8be5e32cc149571512beed371ba1cefc009aa74b35245` |

These identify what this checkpoint inspected, including the restored
accepted lower-table implementation. The fresh build's full source manifest
is still to be checked at final acceptance. The M1 58-module report is
historical evidence for M1, not a fresh build report for the enlarged final
repository.

## 7. Human-readable supplement and remaining acceptance work

The seven inputs, actual multiplicity convention, integrated formula signs,
shared truncation, min-kernel constants, full geometric residual, numerical
totals, continuous translations, strict endpoint treatment and new far method
in [the Chinese supplement](../paper/lean_formalization_addendum.md) agree
with the reviewed source. The reviewer corrected one terminology error:
“有限指数阶梯恒等式” became “有限指数阶梯不等式”. No mathematical source was
changed in this review. The supplement's draft status is to be updated by
the root after final validation; its current wording is conservative and
must not be read as an already completed clean build.

An additional harmless documentation typo was reported to the root and
corrected by the root: the run-command comment in `FinalDependencies.lean`
had named the old M2 diagnostic. The corrected comment now names the final
diagnostic. Its actual code imports `FinalCellCoverage`, checks the final
theorems and produced the output reviewed above; the comment correction does
not alter those checks.

Final acceptance still requires the new output-tree build to finish
successfully, the resulting full final audit to be inspected, and the final
source hashes (including the restored original lower-table implementation) to
match the built snapshot. No additional mathematical gap was identified in
this review. Until those build and source-binding checks finish, this report
approves the reviewed logical assembly and incremental evidence only.

## 8. Documentation consistency during the fresh build

While the 241-module fresh build was running, the reviewer checked the
readable supplement, proof map, route README, both root README versions,
formalization status and plan, reproduction guide, paper directory README,
AI disclosure and M3 worklog. The new final mathematical type is consistently
the seven-input statement; none of the current final-scope statements claims
an unconditional result or only QRH/CS inputs.

The supplement now makes the finite-segment domains `L >= 167`, `A >= 167`,
`u_0 >= 28`, and `exp(u_0) >= 3*10^12` explicit, and defines both q parameters
in the lower-middle comparison. The proof map's finite-RH row now says
scaled-kernel inequality, distinguishing it from the exact kernel invariance
in the forward translation. The status table now includes `1 <= n` in the
integer lower range. The route and paper READMEs distinguish the historical
paper and M1 audit from the new proof and its incremental audit; the old
6% coefficient-sensitivity statement is not attributed to the new lower
budget. These are documentation clarifications only.

The root will update final acceptance wording after the fresh build and
matching audit. Specifically, the opening status statements in both root
READMEs, the route README, `FORMALIZATION_STATUS.md`, the supplement and
`AI_USE.md`, together with their later pending-build paragraphs, must then
point to the actual final records. The supplement's old draft sentence also
still describes far certificates and assembly as in progress; it should be
replaced as a whole. The historical progression in `FORMALIZATION_PLAN.md`
and the M3 worklog should be retained and followed by an explicit final
checkpoint, so the earlier unproved plans are not mistaken for present
obligations. In the plan, the original polynomial-weight milestone is
superseded by the already disclosed trapezoid method refinement, rather
than having been fulfilled by a polynomial proof.

## 9. Final fresh-build acceptance

The root agent completed the new output-tree build and matching diagnostic.
The reviewer then read the full final theorem/axiom output and both reports,
and independently recomputed the current source and artifact hashes. No Lean
compilation was rerun by this reviewer during final acceptance.

### Recorded build and matching audit

- [Fresh project build report](builds/final-20261106/lean_build_report.json):
  `ALL_PRESENT_LEAN_MODULES_COMPILED`, **241/241 PASS**, elapsed **2690.618
  seconds**. The output directory `lean/.lake/final-20261106` did not exist
  before this run, and no module's output artifact existed before its
  compilation. No module subset was requested.
- [Matching dependency report](builds/final-20261106/final_dependency_report.json):
  `FINAL_K6_DEPENDENCY_AUDIT_PASSED`, exit **0**, elapsed **17.375 seconds**,
  `errors: []`, and **241** checked modules.
- [Final dependency/type output](builds/final-20261106/final_dependencies.txt)
  and [build kernel audit](builds/final-20261106/kernel_axioms.txt) record the
  actual final declarations. The dependency output contains
  `FINAL_K6_REQUIRED_PROOF_DEPENDENCIES_PRESENT`.

The build used Lean `4.36.0-rc2`, commit
`b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`, and Mathlib commit
`9d581dfff2e41de989072ea63abf3daf69311520`. All nine reported dependency
revisions equal the pinned expected revisions. Every module command includes
`-DautoImplicit=false`. Both the build and final diagnostic use the same
library path: the fresh project output followed by the matching read-only
external dependency cache. The previous project output directory is absent
from that path. This is a fresh build of all project modules; it is not a
claim that Mathlib and every external dependency were rebuilt from source.

### Final theorem types and proof closure

The fresh audit prints precisely the seven inputs HQ, HC, HR, HI, HFR, HJ and
HCHL for `sixth_powers_from_named_inputs` and for the stronger
`sixth_power_short_from_named_inputs`. The latter additionally takes `n`
and `1 <= n`. Their conclusions are the actual natural-prime predicates
expanded in Section 2. No local prime conclusion, segment correctness,
numerical-bound assumption or certificate-validity flag has appeared in
the final types.

The two historical-cell theorems also have the expected fresh types: five
literature inputs for the 94 middle cells, four for the 60 far cells, with
only their explicit cell-membership and real-domain hypotheses in addition.
All four final theorems have exactly the printed axiom list
`[propext, Classical.choice, Quot.sound]`. Neither `sorryAx` nor
`ofReduceBool` occurs in the final dependency output.

The required-dependency diagnostic passed against the fresh artifacts, so
the actual proof closure described in Section 6, including its analytic,
integer, numerical and strict-prime connections, is present. The fresh
dependency output is byte-identical to the earlier incremental output;
its successful recomputation uses the separately recorded fresh library
path and current-source checks.

### Independent read-only hash verification

The reviewer recomputed **all 241 current Lean source hashes** and
**all 241 fresh `.olean` hashes**, and compared them with the report.
Every source matched its discovered, precompile, postcompile and final
hash; every artifact matched both recorded artifact hashes. All module
statuses and exit codes were successful, and all per-module error lists
were empty. The reviewer also checked the dependency report's bindings to
the build report, diagnostic source and final output. This check returned
no errors.

The restored original lower-table implementation is the accepted built
version. The following key final hashes also match the reviewed source;
the full 241-module inventory is in the build report:

| File | SHA-256 |
|---|---|
| `audit/builds/final-20261106/lean_build_report.json` | `bddf96be2d66f280e0bb8ace907967393d606bb5b49808bff99d793c389dcf43` |
| `audit/builds/final-20261106/final_dependency_report.json` | `70c5bfe5d30dbf3c159a079ada4bda025205c179e28fe4bfb654c8f6c76eb5f0` |
| `audit/builds/final-20261106/final_dependencies.txt` | `430d823cb8ddbdbcba386d46ab77679d7d6fcf1147b9a89d2a2709636fe238aa` |
| `audit/builds/final-20261106/kernel_axioms.txt` | `aadb7440f10a0c64662d1545f98802de32aaeb169efad6f9355d73ca249a3de7` |
| `audit/FinalDependencies.lean` | `2180d7708aec8aa57ec201b9a1f72ec0f47025ed58a2e082c75d86a550f6308a` |
| `lean/LegendreK6/FinalResult.lean` | `57b9148fbdd078083abf425c2d7fc552bff551a83c97ef79a539c63147a0ea24` |
| `lean/LegendreK6/FinalCellCoverage.lean` | `af81a4c1efbdd568f994b8e4797572845b48e7e17be4f543bebaed02d8595e5b` |
| `lean/LegendreK6/M3LowerIntegerCertificate.lean` | `7813bc1b451e798f5b720158ddbc41b91b5ac65cf49b1f6f3c9c95eb49be9bab` |
| `lean/LegendreK6/M3LowerInteger.lean` | `960519b8775e2167d4a8be5e32cc149571512beed371ba1cefc009aa74b35245` |

The build metadata field `end_to_end_H1_H2_formalization: false` correctly
continues to distinguish the stronger QRH/CS-only claim, which has not been
proved here. It does not negate the completed derivation from the seven
named inputs. Those inputs, their accepted source translations and the
review limitations in Sections 1–2 remain part of the final conclusion.

Separately, this reviewer personally ran the unchanged original-certificate
replay with Python 3.12.10 and python-flint 0.9.0. All four original modules
passed in 232.797 seconds, exit 0; all five scripts, four certificates and
the old aggregate summary retained their original hashes. The
[new replay record](final_numerical_replay_2026-11-06.json) and
[complete aggregate output](final_numerical_replay_2026-11-06.txt) preserve
that check. It concerns the historical written proof and is not substituted
for the new Lean proof or its fresh build.

### Final judgment and independence

The previously pending fresh-build and source-binding acceptance conditions
are now satisfied. This report accepts the complete downstream formalized
conclusion for every integer `n >= 1`, including the stronger short interval
and actual coverage of all 94 middle and 60 far cells, **relative to the
seven declared external inputs**.

The reviewer did not implement the final assembly and supplied an additional
cross-check of that assembly and its lower-middle/translation interfaces.
The reviewer did implement the modules listed in Section 1, including the
far proof and parts of the integrated-formula chain. Those portions remain
self-review; neither this final acceptance nor the fresh build converts
them into an independent review of the entire proof. The report does not
claim human peer review, unconditional k=6, a QRH/CS-only formalization, an
upstream-literature reproof, or a full-range result for k=4 or k=3.

After the matching audit passed, the reviewer reread the final root READMEs
in both languages, route README, formalization status, AI disclosure,
readable supplement and new audit index, and the appended final checkpoints
in the plan and logs. Their final claims match the accepted seven-input
scope, fresh-build evidence and disclosed far-method change. One stale
Chinese sentence in the route README still said that the rebuild awaited
acceptance. The reviewer reported it to the root, the root corrected it,
and the reviewer read the correction and checked for that pending-status
wording again. No such unresolved final-status statement remains in the
current entry points checked. Historical pending statements remain in
dated logs and earlier review checkpoints with explicit final updates.
Release checkpoint and manifest generation is handled separately by the
root; this reviewer made no further mathematical-source changes.
