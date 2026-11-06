# QRH(7/8): primes between consecutive sixth powers

[中文版](README.zh-CN.md) · [Review this archival draft](REVIEW_THIS_RELEASE.md)

Assuming the seven precise inputs listed below, **every integer n ≥ 1** has a prime

\[
n^6 < p < n^6+6n^5 < (n+1)^6.
\]

The complete downstream Lean proof has passed a fresh 241-module build and its matching proof-dependency audit. The final theorem has no project-specific interval conclusion or numerical budget among its premises. See [formalization status](FORMALIZATION_STATUS.md).

**Route lead: Codex (OpenAI). AI authors: Codex and Claude (Anthropic).** Claude leads the traditional route and supplied the early 76-cell review of this route. Codex leads its research, implementation, formalization and manuscript preparation. Human author identity remains unfilled; [AI_USE.md](AI_USE.md) records actual contributions and review scope.

## Read the result

| Purpose | Entry point |
|---|---|
| Read the complete current proof | [Chinese paper PDF](paper/current/main.pdf), [twelve-chapter source and build instructions](paper/current/README.md) |
| Inspect the seven precise premises | [Input register](documentation/inputs.md), [machine-readable statements and provenance](documentation/inputs.json) |
| Navigate from the paper to Lean | [Proof guide](documentation/blueprint/README.md), [declaration map](documentation/blueprint/theorem_map.md) |
| Inspect the final formal theorem | [FinalResult.lean](lean/LegendreK6/FinalResult.lean) |
| Understand the research process | [Research archive](research-history/README.md), [decisions, unsuccessful approaches and iterations](research-history/chronological_review.md) |
| Reproduce calculations and kernel checks | [Reproduction instructions](REPRODUCING.md), [audit index](audit/README.md) |
| Review this reorganization | [Review entry point](REVIEW_THIS_RELEASE.md), [file manifest](MANIFEST.json) |

The new paper develops the actual accepted formal argument: zeta zeros, trapezoid smoothing, density layers, rational moment certificates, continuous propagation, finite-height RH reweighting, the infinite tail, and integer lower coverage. The [earlier paper and its polynomial far-range argument](paper/README.md) remain available as historical research.

## Seven named inputs

| Input | Mathematical statement | Source status |
|---|---|---|
| H1 | QRH(7/8) | Accepted as the research premise from OpenAI's official release; upstream proof not rebuilt here |
| H2 | CS v2 Corollary 1 with the specified twelve constant rows | Fixed preprint dependency; independent upstream review is separate |
| H3 | Rosser zero count | Published literature input |
| H4 | Integrated explicit formula | Exact specialization of a published formula; accepted manuscript checked |
| H5 | RH up to height 3×10¹² | Published rigorous computation |
| H6 | CHJII short-interval explicit formula | Published; used preprint statements checked, final journal-version comparison pending |
| H7 | Twelve CHL prime-interval rows | Published paper and corrigendum; revised table matched, rounded-witness issue recorded |

H1 is motivated by [OpenAI's official quasi-RH release](https://github.com/openai/math/tree/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026). The input register fixes the repository revision and the zeta statement used. Acceptance of a premise, publication, source comparison, and Lean verification are distinct evidence categories. All seven premises remain explicit in the final theorem:

```text
QRHSevenEighths → CSv2 → RosserZeroCount → IntegratedExplicitFormula →
  FiniteRH3e12 → CHJIIShortInterval → CHLRows → SixthPowerConclusion
```

## Coverage and numerical margins

For x=n⁶ and L=log x, the integer proof covers n≤1,242,317,999,994 and overlaps the analytic range L≥167. The analytic pieces are [167,178.75], [178.75,400], [400,700], and L≥700. The far segment and tail first prove the shorter fourth-power-scale interval, then embed it into the sixth-power interval.

The final difficult-pilot, lower-middle, and far normalized budgets are bounded by **0.939772, 0.966283, and 0.450022**, respectively. The historical 94-cell proof also has a recorded 6% uniform CS-coefficient sensitivity result; that result is not automatically a sensitivity theorem for the new lower-middle proof.

The stage target remains k=4 and the long-term target k=3. The current all-integer theorem is k=6; other-exponent explorations are archived with their own assumptions and verification status.

This reorganization is a local review draft, awaiting the owner's review before push. Original QRH code uses **0BSD**; original text and data use **CC0-1.0**, as specified in [LICENSE](LICENSE). Third-party material retains its own terms.
