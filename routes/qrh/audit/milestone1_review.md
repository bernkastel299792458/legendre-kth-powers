# Milestone 1 mathematical-interface review

Date: 2026-11-06. Reviewer: Codex sub-agent `lean_prime_power_budget`.

**Final disposition: PASS for milestone 1, relative to the explicitly named
QRH, CS v2, Rosser, and CHJII inputs. Source-level review, final-theorem kernel,
parameter and proof-dependency audits, and the recorded 58-module full build
have passed. This is not a full k=6 formalization certificate.**

## Independence and scope

This reviewer did not implement `ZetaZeros`, `DensityInput`, `LiteratureInputs`,
`CpowInterval`, `FiniteZeroLayer`, `TailDensity`, `TailZeroSum`, `TailFromInputs`,
or `AssemblyWithTail`. Review of those modules is an additional AI cross-check
by an agent distinct from their implementers. This reviewer did implement
`PrimePowerBudget`, `TailDomains`, and `TailErrorBudgets`; assessment of those
three modules is self-review, not independent review. The entire milestone
must therefore not be described as wholly independently reviewed by this agent.
This report is not human expert peer review.

The review read the current source definitions and theorem arguments, rather
than inferring scope from module counts or the absence of custom axioms. The
reviewer independently compiled the three modules they implemented and checked
the signatures and standard-axiom dependencies of their principal theorems.
The final assembled tail and replacement assembly were not yet reported as
compiled when this report was first written. They have since compiled, and
the reviewer has inspected the resulting audit output as recorded below.
No full rebuild was run by this reviewer for the present review.

## External-input translation

### QRH and CS v2

`QRHSevenEighths` is a proposition about the real parts of actual nontrivial
zeros of Mathlib's `riemannZeta`. It does not include a prime conclusion or a
weighted-zero estimate.

The reviewer directly checked [CS v2, Corollary 1 and Table 1][cs]. All 36
constants in the first twelve rows match the source. The threshold
`T >= 3 * 10^12`, both real-power exponents, the closed sigma intervals, the
closed upper height cutoff, and multiplicity counting match the stated upper
bound. `cs_tail_density` derives the coarser tail envelope; it is not an input
disguised as the CS statement. The chosen coarse coefficient `561/25 = 22.44`
is larger than the maximum first coefficient `21.77` in the selected tail rows.

The source permits the closed critical strip, whereas the project's count
restricts to its open strip. Restricting the counted set weakens the source's
upper-bound assertion; it does not strengthen the hypothesis or omit a term
from a claimed equality. Thus the CS interface is a restricted consequence of
the source statement, not literally the same set definition. If exact set
identity is desired, it can additionally be recorded using the existing zeta
nonvanishing results on the strip boundaries.

### CHJII

The reviewer directly checked [CHJII v3, Theorem 1.3 and Table 1][chj]. The
chosen row is `log(x_M)=40`, `alpha=1/2`, `omega=0`, `M=2.894`.
`CHJIIShortInterval` preserves the strict T inequalities, nonnegative interval
length, a **single shared** `Tstar` in `[T,2*T]`, the correct sign of the zero
sum, and the sum of the two endpoint error bounds. For positive x,
`40 <= log x` is the threshold `x >= exp 40`; `sqrt x` expresses the chosen
exponent one half. The complex norm gives the stated absolute error bound.
The zeta sum has the actual analytic multiplicities and the closed absolute
height cutoff. No project-specific bound on that sum is part of this input.

### Rosser

`RosserZeroCount` retains the full counting formula and the closed rectangle
used in the quoted source. `totalZeroCount_le_rosserCount` proves the subset
comparison, and `totalZeroCount_le_mul_log` derives the deliberately weaker
bound needed by the tail. Neither a weighted-zero bound nor the derived
`N(T) <= T log T` estimate is assumed as an additional literature input.

The root agent checked Dusart's HDR, printed page 82, Theorem 86, and page 34,
(2.2)--(2.3). This reviewer checked the source code and the stated provenance,
but did **not** independently inspect those PDF pages. Consequently this report
does not independently certify the Rosser transcription against its original
page. The two arXiv statement checks above concern their stated results and
constants, not an audit of the upstream proofs of those results.

## Actual objects and discharged local parameters

| Component | Source-level finding |
|---|---|
| `ZetaZeros` | The zero sets use actual `riemannZeta`; multiplicity is `analyticOrderNatAt`. Finiteness and strictly positive multiplicity at zeros are proved. Infinite analytic order is excluded before its natural-number representation is used. |
| Real-axis case | The initial sets retain imaginary part zero. `riemannZeta_ne_zero_real_strip` proves absence of real zeros in `(0,1)` from Mathlib's completed-zeta/kernel definitions, without a new literature hypothesis. The final factor-of-two theorem invokes this proof; the earlier helper taking `hreal` is not left as an input of the tail. |
| Conjugation | The proof establishes both zero-set symmetry and invariance of analytic multiplicity. The positive/negative-height factor of two therefore counts repeated zeros correctly. |
| `CpowInterval` | Bounds the actual complex increment `(y^rho-x^rho)/rho` using its derivative. Nonzero rho and positive real endpoints are explicit and later discharged from zero membership and the actual tail parameters. |
| `FiniteZeroLayer` | Proves the finite multiplicity-weighted layer inequality, including the closed upper real-part endpoint. Interval integrability and finite sum/integral interchange are proved. |
| `TailDensity` | Instantiates the layer theorem with actual zeros and derives the integral envelope from `CSv2`. The intermediate scalar total-count hypothesis is visible here, but is discharged from `RosserZeroCount` in `TailZeroSum`. |
| `PrimePowerBudget` | Proves actual von Mangoldt/Chebyshev bounds and the strict-open-interval prime criterion. It reserves the possible right-endpoint contribution `log y`. This module was implemented by this reviewer. |
| `TailDomains` | Proves the real parameter substitutions and the required domains throughout `L >= 700`. `tailHeight` means `2*T`; `tailU` means `log(2*T)`. This module was implemented by this reviewer. |
| `TailErrorBudgets` | Connects actual `psi(y)-theta(y)` and `log y`, plus the displayed CHJII remainder expression, to the last three scalar tail terms. Its prime-power step uses an already formalized unconditional Chebyshev bound. This module was implemented by this reviewer. |
| `TailZeroSum` | Derives the actual truncated zero-sum norm bound from QRH, CS, and Rosser, increasing the cutoff only in a nonnegative real sum. The actual CHJII truncation is used and bounded by `2*T`. No local weighted-zero bound remains as its input. Final compilation was pending at initial review. |
| `TailFromInputs` | Connects the actual CHJII residual, zero norm bound, nonprime contribution and endpoint budget to an actual `Nat.Prime` strictly inside `(x,x+4*x^(3/4))`. Its source signature has only QRH, CS, Rosser, CHJII and the numerical domain conditions. Final compilation was pending at initial review. |
| `AssemblyWithTail` | The replacement assembly accepts only the two finite-range conclusions in `FiniteAnalyticSegmentInputs`; it constructs the tail field using the new tail theorem. It still does not establish the middle and far analytic ranges. Final compilation was pending at initial review. |

No source-level occurrence was found in the final tail signature of a prime
interval conclusion, an arbitrary weighted-error budget, a blanket certificate
soundness statement, or a real-axis nonvanishing assumption supplied in place
of the corresponding project proof. Generic intermediate lemmas do accept
appropriate bounds as parameters, but the reviewed final proof explicitly
supplies those bounds from the stated mathematical inputs and proved lemmas.

## Acceptance condition and verified scope

The current tail dependency chain has compiled, and its complete final theorem
type and kernel dependencies have now been checked. The observed tail type is:

```text
QRHSevenEighths -> CSv2 -> RosserZeroCount -> CHJIIShortInterval ->
  forall x, 0 < x -> 700 <= log x -> ShortInterval4 x
```

The replacement global assembly retains only `middle` and `far` as local
analytic conclusion inputs. No equivalent `tail` input was found under another
name. The old, more general conditional assembly theorem remains as a lemma;
its `tail` argument is supplied by the proved new tail theorem in the replacement
assembly, rather than by an additional argument of that new theorem.

## Kernel, parameter and dependency follow-up

After the source-level review, the root agent reported that the current full
build had passed 56 of 58 modules, including `TailFromInputs`,
`AssemblyWithTail`, and `Audit`. This reviewer then read both
[`kernel_axioms.txt`](kernel_axioms.txt) and
[`milestone1_dependencies.txt`](milestone1_dependencies.txt).

The full printed signature of `tail_short_interval_from_inputs` has exactly
the four named mathematical inputs `QRHSevenEighths`, `CSv2`,
`RosserZeroCount`, and `CHJIIShortInterval`, followed by `x`, `0 < x`, and
`700 <= log x`. It concludes `ShortInterval4 x`. The accepted input definitions
are also printed in the audit output and match the definitions reviewed above.
No local prime conclusion, total-count estimate `hN`, real-axis assumption
`hreal`, or unexplained zero-sum budget appears among its parameters.

The full printed type of `sixth_powers_of_finite_segment_inputs` adds
`CHLRows` and `FiniteAnalyticSegmentInputs` to those four named inputs.
The printed structure has **exactly two fields**, `middle` and `far`.
The conclusion is `SixthPowerConclusion`. This confirms removal of the tail
as a local conclusion premise, while making the two remaining finite-range
obligations explicit.

Both new final theorems report only `[propext, Classical.choice, Quot.sound]`
as kernel axioms. This finding is used together with the inspected complete
signatures, not as a substitute for checking their parameters.

The dependency diagnostic reports
`MILESTONE1_REQUIRED_PROOF_DEPENDENCIES_PRESENT`. Its enumerated tail proof
dependencies include the actual zero-count objects, analytic multiplicity and
its conjugation proof, `riemannZeta_ne_zero_real_strip`,
`sum_allZetaZeros_eq_twice`, the complex-power increment bound, the finite
layer integration theorem, CS envelope derivation, Rosser coarse-count
derivation, all three actual error budgets, `tail_bound_all`, and the strict
theta-to-prime extraction theorem. It also verifies occurrence of the actual
strict prime-interval predicate in the tail theorem. These are proof
dependencies, rather than merely modules imported alongside an unrelated
assembly theorem.

The reviewer found no remaining blocker in the inspected final tail signature
or its reported dependency chain.

## Final full-build follow-up

The reviewer subsequently inspected [`lean_build_report.json`](lean_build_report.json).
The report records `ALL_PRESENT_LEAN_MODULES_COMPILED`, 58 module entries with
exit code zero, and no failing module. Its completion timestamp is
`2026-11-06T12:36:57.492538+08:00`; the native toolchain is Lean `4.36.0-rc2`,
commit `b35cb10cf2ced51a2fd1880cfdbf75c71ab7a35a`, and recorded elapsed time is
1298.034 seconds. The reviewer also compared all 58 recorded source SHA256
values with the present source files and found zero mismatches.

`TailFromInputs`, `AssemblyWithTail`, the root library, and `Audit` all have
successful module entries. The final two entries, `CoreAudit` and `FiniteAudit`,
also succeeded. The previously inspected signature/axiom and dependency
diagnostics remain present. This closes the full-build verification item for
the milestone. **The aggregate build was run by the root agent; this reviewer
inspected its evidence and source hashes but did not personally rerun it.**

The report correctly retains `end_to_end_H1_H2_formalization: false`.
The successful milestone establishes the real-variable infinite tail and
removes its local-conclusion premise from the replacement global assembly;
it does not establish the two finite analytic segments.

With that final build verification, the result closes the infinite tail
**relative to the explicitly named literature inputs**. The full k=6 theorem
will still require the two finite analytic ranges, the complete numerical
expression certificates, and their final connection. Successful milestone-1
compilation must not be reported as completing those remaining obligations.

[cs]: https://arxiv.org/html/2507.15184v2
[chj]: https://arxiv.org/html/2402.04272v3
