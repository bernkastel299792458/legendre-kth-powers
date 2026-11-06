# QRH(7/8) research route

**Public review draft. Not human peer-reviewed. The end-to-end Lean
formalization is not complete.**

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

本目录是 QRH(7/8) 路线入口，由 Codex 负责，当前固化的成果为 QRH(7/8) + CS v2 条件下的六次幂研究。Claude 与 Codex 按各自实际分工作为 AI 作者署名。论文、全部证书、程序、
实际 Lean 构建记录与未完成事项公开列出。没有把“现有 Lean 文件编译成功”
写成“完整条件定理已经由 Lean 证明”。

## Paper and evidence

- [Chinese paper, PDF](paper/main.pdf)
- [Readable manuscript](paper/manuscript.md), [LaTeX source](paper/main.tex),
  [BibTeX](paper/references.bib)
- [Exact formalization scope and open obligations](FORMALIZATION_STATUS.md)
- [Reproduction instructions](REPRODUCING.md)
- [AI use and review disclosure](AI_USE.md)
- [Four-module numerical replay](results/k6_verification_summary.json)
- [Lean build report](audit/lean_build_report.json) and
  [complete theorem types / axiom audit](audit/kernel_axioms.txt)
- [Finite Lean implementation and kernel-audit report](audit/FINITE_LEAN_REVIEW.md)
- [Historical source reviews](audit/source_reviews/README.md)
- [Release file manifest](MANIFEST.json)

## Quantified scope

| Part | Coverage | Evidence |
|---|---|---|
| Integer lower range | 1 <= n <= 1242317999994 | 1259 witnesses + 12 corrected CHL rows |
| New real-variable segment | 167 <= log x <= 400 | 94 Arb-certified closed cells |
| Inherited real-variable segment | 400 <= log x <= 700 | 60 Arb-certified closed cells |
| Infinite real-variable tail | log x >= 700 | Explicit six-term bound and analytic monotonicity |

The new segment has a worst certified upper bound
`0.939735996783828324763044 < 1`, leaving at least 6.0264% of its normalized
budget. All three CS coefficient columns may be uniformly increased by 6%,
with the exponents and domains fixed, and the entire written proof chain
still passes. This is a coefficient-sensitivity result, not a validation of
the CS theorem or a probability of correctness.

## What Lean checks

The checked source includes actual Lucas/Pratt proofs of the 1259 primes
(5349 recursive nodes), exact lower-range thresholds and CHL deductions,
rational certificate bounds and real-parameter cell coverage, selected
analytic identities, weighted von Mangoldt prime extraction, and the
six-term tail bound for every L >= 700.

The current final assembly theorem has the explicit type

```text
CHLRows -> AnalyticSegmentInputs -> SixthPowerConclusion
```

`AnalyticSegmentInputs` contains the three still-unformalized local analytic
conclusions. In particular, the complete zeta explicit-formula/density
argument and the 94/60-cell transcendental enclosures have not yet been
connected inside Lean. The rational-data checks do not silently certify the
Arb computation. See [the scope document](FORMALIZATION_STATUS.md).

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
