# Lean: zero-free-region audit (BTY 4.896)

Two standalone Lean 4 files. They are compiled against the Mathlib of the existing project `../../lean` (Lean 4.36.0-rc2, Mathlib v4.36.0-rc2) **without modifying that project**:

```bash
cd ../../lean
lake env lean ../zfr_audit/lean/BTYParams.lean
lake env lean ../zfr_audit/lean/BTYSkeleton.lean
```

Each file ends with `#print axioms`. Every listed theorem depends only on `propext`, `Classical.choice` and `Quot.sound`: no `sorry`, no `native_decide`, no custom axiom. Compile time is about 15 s and 30 s.

The files are generated from exact rationals by `gen_bty_params.py` and `gen_bty_skeleton.py` (with `bty_skeleton_partD.lean.in`). Regenerate with `python -I gen_*.py`.

## What is formalised

**`BTYParams.lean`** — exact facts of Bellotti–Trudgian–Yang (arXiv:2603.21490):

| Theorem | Content |
|---|---|
| `kappa_sum`, `kappa_abs_sum`, `kappa_msum`, `b_msum` | Σκ_m = 433/859, Σ\|κ_m\| = 3243/859, Σmκ_m = −216/859, Σ m b_m = 1/859 (the sign needed on Im z = T in Lemma 5) |
| `S1_val`, `S2_val` | S₁, S₂ of Lemma 14 |
| `a_zero`, `a_one`, `a_sum`, `a_nonneg` | the a_k of P(x) = \|Σc_k e^{ikx}\|²/14912370, computed from the c_k: a₀ = 1, a₁ = 865534/497079, Σ_{k≥1} a_k = 2919857/828465, all a_k ≥ 0 |
| `lemma3` | **BTY Lemma 3**: Σκ_m x^m > 0 on [0,1] (Bernstein certificate) |
| `N_pos`, `B_pos` | **BTY Lemma 5, polynomial step**: B(y) > 0 for every real y. The paper checked this by isolating roots numerically; here it is a Bernstein certificate on 6 cells after Y = y², s = Y/(1+Y) |
| `paper_p_eq` | the paper's printed degree-12 numerator equals 4012454647232553285540000·N(y²) |

**`BTYSkeleton.lean`** — the logical skeleton of the proof of the classical region:

| Theorem | Content |
|---|---|
| `region_of_iteration` | iteration lemma on [H, T₁] + Littlewood region beyond T₁ + starting region ⇒ region A₀/log t for t ≥ H. This is an induction in steps ≤ ε, with a final partial step so that A + ε ≤ A₀ always holds (BTY issue I14) |
| `region_from_three` | extension to t ≥ 3 by RH up to H |
| `cross_1962`, `cross_21233`, `logH_ge`, `logK_le`, `log3_ge` | the numerical facts about exp/log, proved from `Real.exp_one_lt_d9` and Taylor bounds: 19.62/4.896 ≤ log 55.01; 21.233/4.896 ≤ log 76.47; log(3·10¹²) ≥ 28.72; log(16 + 10¹⁰/(3·10¹²)) ≤ 2.78 |
| `final_contradiction_55`, `final_contradiction_76` | **the numerical end of BTY Lemma 15**, with our corrected constants (Lemma 14: b₁, b₂, b₃, C₁; (48) with the log k correction). Valid for every log t in [28.72, 55.01] resp. [28.72, 76.47], by 7 resp. 12 cells checked in exact rational arithmetic, plus monotonicity lemmas `Φ_mono_eta`, `C1_mono` |
| `iteration_of_chain` | BTY's iteration lemma, derived from the hypothesis `AnalyticChain` and the final contradiction. This includes the bounds μ ≤ 1 and μ ≥ log t/(log t + 2.78) − 10⁻⁹ for μ = (1−σ)/η |
| `classical_region_4896_BTY` | **BTY Theorem 1 as published**: `AnalyticChain` on [H, e^76.47] + Littlewood 21.233 (Yang, JMAA 2024, refereed) + RH(3·10¹²) + a starting region c > 1/6 (`kadiri_start_ok`: Kadiri's 1/5.69693) ⇒ ζ ≠ 0 for σ > 1 − 1/(4.896 log t), t ≥ 3 |
| `classical_region_4896_from_thesis` | the same with the chain only on [H, e^55.01] and Littlewood 19.62. This variant is **only as good as the thesis constant**, which is doubtful (`../thesis_19.62/REPORT.md`); use the BTY variant |

## What is NOT formalised (explicit hypotheses)

- **`AnalyticChain`** — the analytic part of BTY: the explicit formula (Kadiri Prop. 2.1), Ford's W₀ bound, the Lemmas 5–14 estimates, and the bound w(0) ∈ [5.6727875988, 5.6727875989]. In Lean it is a single hypothesis: for a putative zero violating the iteration step, Φ(η, μ) ≤ Kq·η·log t. Its ingredients are checked numerically, not in Lean, by `../bty_4.896/check_part*.py`.
- The zero-free regions used as inputs (Littlewood 21.233 or 19.62, Kadiri's start, RH to 3·10¹²) are hypotheses about an abstract zero set Z ⊆ ℝ×ℝ. Lean knows nothing about ζ.
- The k = 67 certificates (`proof/certificates/*.csv`) are not re-verified in Lean. The link from "zero-free region with constants (Z₁, Z₂, Z₃)" to "certificate δ < 1" is the arb computation in `proof/code/`.

So Lean confirms that the *logic* and the *final arithmetic* of BTY's argument are sound once the analytic estimates are granted, and it confirms several exact facts that the paper only checked numerically. It does not establish the analytic estimates.
