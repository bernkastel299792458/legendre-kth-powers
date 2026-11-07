# Shared context for the v5 push (read this first)

## Project

The question is for which k there is a prime in (n^k, (n+1)^k) for **every** n ≥ 1.

Current results (manuscript v4, not peer-reviewed; `proof/manuscript.md`, `proof/README.md`):
- **k ≥ 70.** Zero-free constants Z₁ = 4.896 (classical), Z₂ = 21.233 (Littlewood), Z₃ = 54.004 (VK).
- **k ≥ 74.** Refereed inputs only (Z₁ = 5.558691).

Published record: k ≥ 86 (E. S. Lee, Acta Arith. 2026).

**Goal of v5:** a smaller k, using the same kind of argument — classical explicit estimates plus rigorous interval certificates in Arb (python-flint 0.9.0).

## Method in one paragraph

We need θ(x+h) − θ(x) > 0 with h = k x^{1−1/k}, for all x ≥ 4·10^18. Write L = log x. The range of L is split into four parts:
- **L ≤ L₁(k) ≈ k·log(k·2.52·10^11).** Cully-Hugill–Lee interval estimates.
- **[L₁, L₂].** Proposition S: a smoothed explicit formula with weight y^M(1−y)^M, using `proof/code/rigorous_smooth.py`.
- **[L₂, 10^8].** Proposition H: a sharp truncated explicit formula with a hybrid zero-density bound, using `rigorous_hyb.py`.
- **[10^8, ∞).** Lemma T (`tail.py`).

Zeros enter through Φ(t) ≥ Σ_{H_R<γ<t} x^{β−1}, which is bounded in Lemma 5 (`Phi_upper` in `rigorous_smooth.py`). It combines:
- N(t) for β ≤ 0.98;
- a Kadiri–Lumley–Ng-type bound (Johnston–Yang 17.418 (log T)^{5−2σ} T^{8(1−σ)/3} + 2.231 log² T) for σ ∈ [0.98, σ*];
- a Bellotti log-free row C·T^{B(1−σ)} (valid for σ ≥ α₀) on [σ*, 1−η].

Here η(t) is the width of the zero-free region, η(t) = max(1/(Z₁ v), log v/(Z₂ v), 1/(Z₃ v^{2/3}(log v)^{1/3})) with v = log t.

## Lever analysis (2026-11-06; `results/levers_2026-11-06.md`, `code/explore/levers.py`)

The numbers below are smallest-k values from sampled scans. Baseline is 70.
- **Chourasiya–Simonič (CS) Cor. 1** (arXiv:2507.15184v2, a preprint). Adding it as an extra Lemma 5 option gives **68**.
- **Littlewood Z₂.** 20.08 → 68; 19.5 → 67.
- **Classical Z₁.** 4.7 → 68; 4.5 → 66.
- **Bellotti C.** ×0.5 → 66. Any further scaling saturates at **64**. Scaling only the rows e^70–e^110 by ×0.1 → 68.
- **No effect:** raising the RH height, higher M, and Johnston–Yang ×0.5.
- **Combinations.** CS + C×0.5 + Z₂ = 20.08 → **65**. CS + C×0.2 + Z₂ = 19 + Z₁ = 4.7 + JY×0.5 → **58**.

**Where the bottlenecks are.**
- **k ≈ 64–70:** zeros at heights log t ≈ 75–110, where the classical and Littlewood regions cross and η is smallest.
- **k ≲ 64:** zeros just above the RH height (log t ≈ 29–35) with β ∈ [0.98, 0.99). Bellotti's low rows have α₀ ≈ 0.99, so only JY or CS cover this band.

## Open problem in an input

Bellotti's paper (arXiv:2405.12545v2; J. Number Theory 269 (2025)) may have a counting gap in §4. It claims that for each γ_r there is a *unique* representative zero with |γ_r − γ_s| < δ, and one per band nδ ≤ |γ_r − γ_s| ≤ (n+1)δ. Neighbouring boxes and both sides can contribute. If this is real, C is about ×1.5–2, and the v4 results become 71–73 / 76–78.

## Files

**References** (`work/ref/`):
- `bel_v2.txt` — Bellotti, clean text;
- `bellotti_constants.py.txt` — her code, from github.com/ChiaraBellotti/Log-free-zero-density-estimates-for-zeta;
- `belmodel.py` — an independent float model that reproduces her Table 2;
- `bv.py`, `lp.py`, `opt*.py`, `exp*.py` — earlier experiments;
- `chourasiya_simonic_2507.15184v2.txt`;
- `thorner_zaman_2208.11123.txt`;
- `ramare_zuniga_alterman_2405.12662.txt`;
- `fiori_jaskari_2609.23222.txt`.

**Papers and earlier audits:**
- `papers/` has the PDFs and texts; `proof/input_verification/` has the source-check reports.
- `proof/zfr_audit/` is the earlier audit of 4.896 (verified) and of the thesis constant 19.62 (an error in Lemma 3.8; the repaired value is about 19.90–20.08). It includes requirement curves.

## Rules for every workstream

1. **Never modify `proof/`, `code/`, `results/` or `papers/`.** Write only inside your own folder `work/<your folder>/`. You may read anything.
2. **Every claimed bound must be rigorous.**
   - Use Arb balls (python-flint) or exact rationals, never floats, in anything that is claimed.
   - Floats are fine for exploration, and for choosing parameters.
3. **For every external input, record** the exact statement, its source (paper, theorem, page), its status (refereed / preprint / thesis / our own proof) and its conventions (β ≥ σ vs > σ, 0 < γ ≤ T vs < T, range of T).
4. **Separate "the paper states" from "we infer".** Flag anything uncertain as UNSURE rather than guessing.
5. **Write a `REPORT.md`** in your folder with:
   - the verdicts;
   - a list of deliverables and how to re-run them;
   - the exact interface files described in your brief.
6. **Tag every result by input status,** so that tiered claims can be made later:
   - only refereed inputs;
   - plus audited preprints;
   - plus our own new lemmas.
