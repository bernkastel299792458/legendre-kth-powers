# QRH(7/8) research route

**Public review draft. Not human peer-reviewed. The complete downstream Lean
proof from seven named inputs has passed acceptance: all 241 modules rebuilt
in a new output tree, followed by the matching exact-input dependency audit.**

**Route lead: Codex (OpenAI). Project AI authors: Claude and Codex.**
Claude leads the traditional route and contributed the early review of this
route; Codex leads the QRH route and is responsible for this package's
research, implementation, formalization work, and manuscript. The precise
review scope is recorded in [AI_USE.md](AI_USE.md).

This directory groups work by its QRH premise. Its currently archived
all-integer result concerns sixth powers; the filenames and Lean theorem
names retain that mathematical exponent. The project's stage target is
k = 4 and its longer-term target is k = 3.

## Current result

This package gives a written, computer-assisted argument that, for every
integer `n >= 1`, there is a prime

\[
n^6 < p < n^6+6n^5 < (n+1)^6,
\]

assuming **H1: QRH(7/8)** and **H2: Chourasiya–Simonič,
arXiv:2507.15184v2, Corollary 1 and the specified first 12 rows of Table 1**,
together with the precisely identified classical/literature inputs in the
paper. H2 is explicitly retained as a preprint dependency. This package does
not audit either upstream proof. It does not claim an unconditional result,
or an all-n result for k = 3, 4, or 5.

本目录是 QRH(7/8) 路线入口，由 Codex 负责，当前成果为六次幂的条件结论。
最终 Lean 定理保留 QRH(7/8)、CS v2 及下文列出的其余五项文献输入；
全部本项目局部推导已连接；241 个模块在全新输出目录中全部重建通过，对应最终依赖审计也已通过。
Claude 与 Codex 按各自实际分工作为 AI 作者署名，论文、证书、程序与实际核验记录公开列出。

## Paper and evidence

- [Original Chinese paper, PDF](paper/main.pdf)
- [New readable formalization addendum](paper/lean_formalization_addendum.md)
- [Readable manuscript](paper/manuscript.md), [LaTeX source](paper/main.tex),
  [BibTeX](paper/references.bib)
- [Exact formalization scope and final acceptance](FORMALIZATION_STATUS.md)
- [Source and constant checks for external inputs 4, 6 and 7](audit/inputs_4_6_7_review_2026-11-06.md), including the published source for the integrated formula and the CHL rounded-parameter reproduction issue
- [Three-milestone implementation plan](FORMALIZATION_PLAN.md) and
  [current implementation log](audit/formalization_progress_2026-11-06.md)
- [Reproduction instructions](REPRODUCING.md)
- [AI use and review disclosure](AI_USE.md)
- [Four-module numerical replay](results/k6_verification_summary.json)
- [Incremental final theorem types and proof-dependency audit](audit/final_dependencies_incremental.txt)
- [Historical M1 build report](audit/lean_build_report.json) and
  [M1 theorem types / axiom audit](audit/kernel_axioms.txt)
- [Historical finite Lean implementation review](audit/FINITE_LEAN_REVIEW.md)
- [Historical source reviews](audit/source_reviews/README.md)
- [Release file manifest](MANIFEST.json)

## Quantified scope

| Part | Coverage | Evidence |
|---|---|---|
| Integer lower range | 1 <= n <= 1242317999994 | 1259 witnesses + 12 corrected CHL rows |
| Middle real-variable segment | 167 <= log x <= 400 | Complete Lean derivation, covering every point of all 94 historical cells |
| Far real-variable segment | 400 <= log x <= 700 | Complete Lean trapezoid derivation, covering every point of all 60 historical cells |
| Infinite real-variable tail | log x >= 700 | Complete Lean derivation from QRH, CS, Rosser, and CHJII inputs |

The historical written proof's refined middle segment has a worst certified upper bound
`0.939735996783828324763044 < 1`, leaving at least 6.0264% of its normalized
budget. All three CS coefficient columns may be uniformly increased by 6%,
with the exponents and domains fixed, and the entire written proof chain
still passes. This is a coefficient-sensitivity result, not a validation of
the CS theorem or a probability of correctness. It is not automatically a
formal sensitivity theorem for the new conservative lower-middle budget.

## What Lean checks

The checked source includes actual Lucas/Pratt proofs of the 1259 primes
(5349 recursive nodes), exact lower-range thresholds and CHL deductions,
rational certificate bounds and real-parameter cell coverage, selected
analytic identities, weighted von Mangoldt prime extraction, and the
six-term tail bound for every L >= 700. The infinite tail is now connected
to the actual zeta zeros, their multiplicities, the actual Chebyshev functions,
and a strictly interior prime. Its theorem is `tail_short_interval_from_inputs`.

The final downstream theorem is `sixth_powers_from_named_inputs`:

```text
QRHSevenEighths -> CSv2 -> RosserZeroCount -> IntegratedExplicitFormula ->
  FiniteRH3e12 -> CHJIIShortInterval -> CHLRows -> SixthPowerConclusion
```

All local analytic-segment and numerical-budget premises have been removed.
The actual argument covers every point of the original 94+60 cells and the
infinite tail. The far formal proof uses a new trapezoid certificate and
continuous translation; it does not claim a line-by-line translation of the
historical polynomial-weight proof. See the [readable addendum](paper/lean_formalization_addendum.md),
[final source](lean/LegendreK6/FinalResult.lean) and [exact scope](FORMALIZATION_STATUS.md).
The [fresh 241-module build](audit/builds/final-20261106/lean_build_report.json)
and [matching proof-dependency audit](audit/builds/final-20261106/final_dependency_report.json)
passed. [The audit index](audit/README.md) separates final evidence from earlier
checkpoints. Classical literature results remain explicit inputs; the stronger
QRH/CS-only formalization is a different claim.

三个里程碑的数学链已连接到全范围 k=6 定理，最终类型不再含局部区间结论或数值预算前提。
241 个模块在全新输出目录中全部重建通过，对应完整类型、实际证明依赖和公理审计也已通过。
完整输入是 QRH、CS v2、Rosser、积分显式公式、有限高度 RH、CHJII、CHL 七项。
远段采用新梯形证明，原多项式稿件、原证书与历史审阅保留。

## Reproduce

Use **Python 3.12.10** and run from this directory:

```sh
python -m pip install -r code/requirements.txt
python -X utf8 code/verify_k6.py --dry-run
python -X utf8 code/review_smooth_k6_refined.py
python -X utf8 code/generate_lean_certificates.py --check
```

Lean is pinned in `lean/lean-toolchain`; Mathlib and all dependencies are
pinned in `lean/lake-manifest.json`. The full local compilation and auditing
procedure is documented in [REPRODUCING.md](REPRODUCING.md).

## Authorship, review, and license

At the project owner's direction, the paper credits **Claude** (traditional
route lead; earlier review of this route) and **Codex** (QRH route lead;
principal research and implementation of this paper) as AI authors. This
credit does not extend the earlier Claude review to the subsequent Lean work.
Human author names, affiliations, and email addresses remain unfilled. AI use is disclosed in the paper and [AI_USE.md](AI_USE.md).
AI cross-checks are not human expert peer review. No priority claim is made.

Original code: **0BSD**. Original paper, documentation, and certificate data:
**CC0-1.0**. These choices apply only to this package, not the surrounding
repository's other research track. Dependencies and cited works retain their
own licenses. See [LICENSE](LICENSE).
