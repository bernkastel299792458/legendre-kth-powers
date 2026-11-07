# Audit of Chourasiya–Simonič, arXiv:2507.15184v2 (Phase 1a)

*Written by the Phase 1a sub-agent. The sub-agent could not write report files, so the main session saved this report. Every script here runs with `python -I run_all.py` (about 35 s; result ALL OK).*

**Source.** arXiv LaTeX `src/v2/InghamPostArXiv.tex`, dated 30 Sep 2025; v1 is in `src/v1`. Only v1 and v2 exist, and there is no journal version.

## 1. Verdicts

| Statement | Verdict | Corrected constants |
|---|---|---|
| (A) Cor. 1, σ ∈ [0.96875, 1], T ≥ 3·10¹² | VERIFIED WITH CORRECTIONS (the printed values rely on I1) | B₁ = 50.58, B₂ = 4.822, B₃ = 85.51 (d .2946, κ .0737, δ .3033, log₁₀A₀ 11.45). The paper prints 46.06 / 4.897 / 86.84. |
| (A) σ ∈ [0.9375, 0.96875] | VERIFIED WITH CORRECTIONS | 38.51 / 5.178 / 91.82 |
| (B) eq. (119) / Table 4, σ ≥ 0.96875 | VERIFIED WITH CORRECTIONS (I1, I2) | see §2.2 |
| **Exact form of (119)** | **N(σ,T) ≤ A·T^{8(1−σ)/3}(log T)^{6−4σ} + B·log²T, for T ≥ 3·10¹²**. The log exponent is 6−4σ, not 5−2σ as in KLN/JY. | — |
| Theorem 1 and its proof | VERIFIED line by line, given the inputs | Lemma 7 with b₄ = 0.5936 for X ≥ 10¹², δ ≤ 0.368 |
| Fourth moment (Thm 2, Cor. 2 row 10¹⁰, Cor. 4) | VERIFIED (sub-audit, §6) | a₁ = 1.9072538e17, a₂ = 1.3325889 |
| Johnston–Yang Table 3, σ → 1 | printed 17.418; recomputed 17.41921 with JY's own method | **use 17.4193** |

**Conventions.** N(σ,T) = #{ρ : β ≥ σ, 0 < γ ≤ T}, counted with multiplicity. H_RH = 3·10¹² (Platt–Trudgian). All statements hold for T ≥ 3·10¹².

**Tiers.**
- The corrected (A) and (B) rest on refereed results, plus CS itself (audited here), plus **RZA arXiv:2603.25961v3 Thm 1.2** (a preprint; its statement was checked, its proof was not audited).
- (A) also uses the CS fourth moment (a preprint, audited here).
- Without RZA:
  - (B) falls back to JY/KLN with (log T)^{5−2σ};
  - (A) falls back to the v1 form with log³T.

**What this means for the project.**
- On σ ≥ 0.9375, the corrected (B) is smaller than (A) everywhere.
- The corrected (B) is about 25× smaller than JY. The ratio B/JY is 0.041 at log T = 30, 0.035 at log T = 35 and 0.013 at log T = 100.

## 2. Corrected tables (rigorous Arb, rounded up, T ≥ 3·10¹²)

### 2.1 (A)

Parameters: T₀ = H₀ = H = 3·10¹², h = 1, b₄ = 0.5936.

| σ₁ | σ₂ | B₁ | B₂ | B₃ | d | κ | δ | log₁₀A₀ |
|---|---|---|---|---|---|---|---|---|
| 0.9375 | 0.96875 | 38.51 | 5.178 | 91.82 | .2901 | .0906 | .2700 | 11.42 |
| 0.96875 | 1 | 50.58 | 4.822 | 85.51 | .2946 | .0737 | .3033 | 11.45 |

For the row [0.96875, 1] with a larger starting height T₀ (valid for T ≥ T₀):

| T₀ | B₁ | Note |
|---|---|---|
| e³⁰ | 49.99 | |
| e³² | 49.21 | |
| e³⁵ | 48.26 | |
| e³⁷ | 41.05 | uses b₄ = 0.5103 |

### 2.2 (B)

Parameters: k = 1, H = H₀ − 1, H₀ = 3·10¹², η = .25345, μ = 1.2363, a₁ = .618, a₂ = 2.8245, b₄ = .5936, corrected log factor.

| σ₁ | σ₂ | A | B (CT19) | B (KLN 3.13) |
|---|---|---|---|---|
| .9375 | .96875 | 17.370 | 2.750 | 2.785 |
| .96875 | .975 | 17.875 | 2.474 | 2.509 |
| .975 | .98125 | 18.388 | 2.420 | 2.455 |
| .98125 | .9875 | 18.909 | 2.366 | 2.401 |
| .9875 | .99375 | 19.438 | 2.312 | 2.347 |
| .99375 | 1 | 19.975 | 2.258 | 2.293 |

Rows for the project's bottleneck, σ ∈ [.98, .99]:

| T ≥ | A | B |
|---|---|---|
| 3·10¹² | 19.120 | 2.378 |
| e³⁰ | 18.890 | 2.351 |
| e³² | 18.564 | 2.313 |
| e³⁵ | 18.140 | 2.264 |
| 10¹⁶ | 15.458 | 2.238 |

## 3. Issues

**I1 (fixable).** The value b₄ = 0.54 in Lemma 7 comes from a private communication.
- RZA v3 Thm 1.2 proves only the following:

  | Range of X | Condition | b₄ |
  |---|---|---|
  | 10⁸ ≤ X < 10¹² | ε ≤ 1/100 | 0.689 |
  | 10¹² ≤ X < 10¹⁶ | ε ≤ 1/25 | 0.5936 |
  | 10¹² ≤ X < 10¹⁶ | ε ≤ 1/50 | 0.5501 |
  | 10¹⁶ ≤ X < 10³³ | ε ≤ 1/50 | 0.5103 |
  | X ≥ 10³³ | — | 0.51 |

- So Lemma 7 as stated (X ≥ 3·10¹⁰) is not covered.
- Effect of using the proved values: (A) B₁ +9.8%, (B) A +9.6%.

**I2 (fixable).** In (119) the paper keeps KLN's log factor e^{2d(2llH₀ − ll kH₀)/log H₀}. That saving belonged to a (log kT)^{2σ′} term which no longer appears.
- The correct factor is e^{4d·llH₀/log H₀}, which multiplies A by 1.082.
- Table 4 reproduces only with the uncorrected factor.

**I3–I11 (cosmetic or harmless).**
- I3: the text says H₀ = 3.06·10¹⁰, but the table uses 3·10¹².
- I4: a₁ and a₂ are unstated; the table uses 0.63 and 2.851. These are valid by Hiary–Patel–Yang's 0.618 and the rigorous bound max|ζ(½+it)| ≤ 1.46036 on |t| ≤ 3.
- I5: the B term uses Cully-Hugill–Trudgian for (3.13), which the text does not mention.
- I6: C₆ = 220 is conservative; the cited argument gives 38.93.
- I7: extending KLN Cor. 4.11 to η = ½ is valid.
- I8: K₂ needs the unstated step 1 − e^{−u₀} ≤ u₀.
- I9: the exponent bookkeeping is OK.
- I10: a CHT21 +0.73x^{1/2} term is omitted (it affects only rows 10⁴–10⁹ of the fourth moment).
- I11: JY's 17.418 should be 17.4193.

## 4. What was checked

- Gabriel's theorem (Thm 3) and Cor. 6.
- Lemmas 5 (KLN 4.1), 7, 8, 9 and 10.
- The proof of Theorem 1 and the assembly of Corollary 1.
- Reproduction of the paper's rows: 35.3457 / 5.17954 / 91.8509 and 46.0545 / 4.89686 / 86.8380.
- KLN Table 1, JY Table 3 and CS Table 4, each reproduced to rounding.

## 5. Dependencies

| Input | Status |
|---|---|
| Platt–Trudgian 2021 | refereed |
| Littlewood's lemma | classical |
| Gabriel / Karatsuba–Voronin | refereed / book |
| KLN18 | refereed |
| Ramaré 2016 | refereed |
| **RZA arXiv:2603.25961v3** | **preprint, not audited** |
| Hiary–Patel–Yang 2024 | refereed |
| CHT21 | refereed |
| CS fourth moment | preprint, audited |

## 6. Fourth-moment sub-audit (`fourth_moment/`)

- Theorem 2: VERIFIED. Row 10¹⁰: 𝔐₁ = 34.841167. Corollary 4: VERIFIED.
- Only issue: X1 (the CHT21 +0.73x^{1/2} term), which leaves row 10¹⁰ unaffected.
- Sensitivity: multiplying a₂ by 10 changes B₁ by a factor 1.072.

## 7. Interface

`cs_bounds.py` provides:
- `N_upper_A(sig_lo, sig_hi, T, tier)` and `N_upper_B(...)`: rigorous upper bounds for every σ in the interval and every T in the ball.
- `N_upper_JY(...)`: the Johnston–Yang bound, for comparison.
- `B_row` and `A_row`: corrected constants for any row and any T₀ ≥ 3·10¹².

`tier="paper"` reproduces the printed constants for comparison only; it is not a proved bound.
