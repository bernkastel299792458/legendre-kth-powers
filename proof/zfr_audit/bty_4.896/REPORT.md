# Audit of the classical constant 4.896 (Bellotti–Trudgian–Yang, arXiv:2603.21490v1, Thm 1 / Lemma 1)

Source: the arXiv LaTeX source `source/Bellotti_Trudgian_Yang_v1.tex` (downloaded 2026-11-06, sha256 `b162c073…8a3c`; printed by `run_all.py`). The PDF text `papers/2603.21490.txt` loses the Greek letters, so all formulas were read from the LaTeX. Lemma numbers follow the paper.

## 摘要（中文）

- **结论：已核实（需修正若干处）。** Theorem 1（t ≥ 3 时 ζ 在 σ > 1 − 1/(4.896 log t) 内无零点）成立。
  - 我们逐条检查了全部推理，并用 arb 复算了文中所有数值条件。
  - 共发现 15 处问题：笔误、陈述错误、两处符号/适用范围错误，以及 Table 1 中一个不成立的下界。**没有一处是致命的。**
  - 全部修正之后：
    - 论文自己的收尾路线在 log t ≤ 78.16 内仍然闭合（需要的是 76.47）；76.47 处的余量为 4.7·10⁻⁴（相对 0.05%）。按论文原数字算，余量只有 6·10⁻⁵。
    - 若利用 η 与 A 的耦合（见 §4），76.47 处的余量为 0.66%。
- **对 k = 67 的意义。** 证明只在 Littlewood 区域接管之前用到 4.896：
  - Z₂ = 19.62 时，到 log t = e^{19.62/4.896} = 55.0 为止；
  - Z₂ ≈ 20.08 时，到 60.4 为止。

  在 log t ≤ 55.01 上，修正后的余量为 0.9%（耦合后 1.7%）。所以 4.896 本身相当稳健。它只依赖已发表的 21.233，不依赖博士论文。
- **Lean。** 证明骨架已形式化（`../lean/BTYSkeleton.lean`，无 sorry），内容包括：
  - 迭代 ⇒ 区域；
  - 与 Littlewood 区域的交接；
  - Lemma 15 的最后一步：用修正后的常数，在有理数上做严格的分块验证。

  Lemma 3、Lemma 5 的多项式正性和 a_k 的精确值，见 `../lean/BTYParams.lean`。各解析估计以显式假设 `AnalyticChain` 的形式进入。

## 1. Verdicts

| Claim | Verdict | Evidence |
|---|---|---|
| Thm 1 (4.896, t ≥ 3) | **VERIFIED** after corrections. Margin with corrected constants: 4.7·10⁻⁴ at log t = 76.47 (paper's route); the range extends to log t ≤ 78.16 | part 5; Lean `classical_region_4896_BTY` |
| Lemma 1 restricted to log t ≤ 55.01 (all the k = 67 proof needs if Z₂ ≤ 19.62; ≤ 60.4 if Z₂ ≤ 20.08) | **VERIFIED**, margin 9.2·10⁻³ (0.9%) | part 5; Lean `classical_region_4896_from_thesis`, `final_contradiction_55` |
| Lemma 3 (f ≥ 0) | VERIFIED (exact Sturm count; Lean Bernstein proof) | part 1; Lean `lemma3` |
| Lemma 4 (Ford's W₀ bound) | printed c₀ WRONG (typo, I2); the bound with Ford's c₀ = 1/(sin θ cos³θ) VERIFIED numerically at 40 points; all derived numbers use the correct c₀ | part 1 |
| Lemma 5 (non-negativity) | VERIFIED; the polynomial p(y) is reproduced exactly; B(y) > 0 by Sturm and in Lean (`B_pos`); one wrong justification (I3) and one overstatement (I4), both harmless | part 1 |
| Lemma 6 (far zeros) | VERIFIED (−10⁻⁸ holds with margin; one false intermediate constant, I5) | part 2 |
| Lemma 8 / 9 (error term) | VERIFIED after corrections I6–I8; (32) is false as stated, but the integral actually needed is 23.60 < 24 | part 2 |
| Lemma 10 / 11 (0.1186) | VERIFIED after replacing the invalid m₅ (I11); Σ log p·m_p = 0.2354513 > 0.23545 | part 3 |
| Lemma 12 (−1.568) | VERIFIED: −1.56888 | part 2 |
| Lemma 13 | VERIFIED | part 2 |
| Lemma 14 | the printed proof has a sign error and an invalid use of Lemma 4 (I13); the printed inequality is nevertheless true on a test grid (direct quadrature, min gap 5.8·10⁻⁴). A corrected rigorous version, C₁′(μ) + 3.9098η + 20.153η² − 568.1η³, is VERIFIED | part 4 |
| Lemma 15 (iteration) + final numbers | VERIFIED with corrected constants (rigorous cover of all log t ∈ [log H, 76.47] by 4000 L-balls; Lean on 7 / 12 rational cells) | part 5; Lean `final_contradiction_*`, `iteration_of_chain` |

## 2. Issues found (severity: F = fatal, X = fixable, C = cosmetic)

| # | Where | Issue | Sev. | Effect after fixing |
|---|---|---|---|---|
| I1 | §3 parameter table | A₀ for Lemma 1 printed as (4.8596)⁻¹; the printed η₀ = 0.0071093, σ₀ = 0.9935164 correspond to (4.896)⁻¹. With 4.8596 the final step would fail (needs 1.0369 > 1.0293) | C | none |
| I2 | Lemma 4 | c₀ printed as csc θ sec²θ; Ford (arXiv:1910.08205v4) and MTY have 1/(sin θ cos³θ). The printed formula cannot hold: C → c₀c₃ = 21.19 < \|w″(0)\| = 50.07 = lim\|z³W₀(z)\|. All constants BTY derive from C (ε₀ test 4.66·10⁻⁴ < 5·10⁻⁴, 52, 51, 424) are correct only with Ford's c₀ | C | none |
| I3 | Lemma 5, line Im z = T | "Re F(x+iT) = ηw(0)(κ+o(1))/T²" is false (the true coefficient is κx + (2σ−1)Σmκ_m, which is < 0 for small x). What is needed is the sum F(z)+F(2σ−1−z), whose coefficient is (2σ−1)Σ m b_m = (2σ−1)/859 > 0 | C | none |
| I4 | Lemma 5 (22) | stated for −η ≤ Re z ≤ 1, proved only for Re z ≤ 2σ−1+η. Lemma 6 needs only Re z ∈ (σ−1, σ), which is covered | C | none |
| I5 | Lemma 6 | the far-zero sum must pair ρ with 1−ρ̄ (not ρ̄) to apply (22). This gives −22η, so the printed −44η is conservative. (25) has F(2σ−1+β₀) for F(σ−1+β₀); (47) omits the factor a₁. (27): the derived constant is 1.0778, not ≤ 1 (1.0010 if the dropped term is kept). The final bound is 1.5·10⁻¹⁰ < 10⁻⁸ | C | none |
| I6 | Lemma 8 | "U(x) < log(100−x) for x ≤ 2" is false for \|x\| ≲ 0.33 (U(0) = 5.386 > 4.605). With U ≤ 6 + log(1+\|x\|), I₁ < 4·10⁻²⁴ | C | none |
| I7 | Lemma 8 (32) | ∫U(y)/(x₀²+y²)^{3/2} dy = 34.58, not < 24. But T₁ involves \|Re ψ\| itself, and ∫\|Re ψ(¼+iy/2)\|/(x₀²+y²)^{3/2} dy ≤ 23.600 < 24 (rigorous, using monotonicity of Re ψ in \|y\|). So 199η³ and 623η³ stand. (The thesis's version of the same lemma says < 36, which is correct for U) | C | none |
| I8 | Lemma 8 used in Lemma 15 | applied at s_k + δ_m with Im = kt (k ≤ 16), but the hypothesis η ≤ A₀/log(Im s) is known only with log t. Correct: T₁ ≤ 14η² + 67.96·log k·η³, so the η³ coefficient of (48) becomes 8396 instead of 8013 | X | −8·10⁻⁶ at log t = 76.47 |
| I9 | Lemma 9 | proof says "apply Lemma 9" (should be Lemma 7); "g(d) = g′(0) = g′(d) = g″(d)" is missing "= 0" | C | none |
| I10 | Lemmas 9–15 | the symbol f(0) is used for ηw(0), although f(0) = κηw(0) by Definition 2. Read consistently as ηw(0), every step is correct (Lemma 11's proof gives f(u) ≥ κηw(0)) | C | none |
| I11 | Lemma 10, Table 1 | **m₅ = 0.00735709 is not a lower bound**: G₅(1, 1.649524…) = 0.0073564919 (rigorous point value). A certified replacement is 0.00735649. For p ≥ 53 the paper keeps m ≤ 15 although p^m > e⁵⁹ for m > ⌊59/log p⌋ (we use the correct ranges). The Mathematica check ∂G/∂σ < 0 is unnecessary: ∂G/∂σ = −log p Σ m p^{−mσ} P(mx) ≤ 0 because P ≥ 0. Result: Σ log p·m_p = 0.2354513 > 0.23545 (margin 1.3·10⁻⁶) | X | none (0.1186 stands) |
| I12 | Lemma 12 | the O\*(10⁻¹⁰) error multiplies Σ\|κ_m\|, not κ | C | none (−1.56888) |
| I13 | Lemma 14 | (a) **sign error**: the η² term of (41) should be −(a₁(1−μ)+a₀μ)w(0)S₂/(2σ−1)² (worst case +4.64η²), not −((a₁−a₀)μ+a₁)w(0)S₂ (≥ 11η²). (b) C(x₁,x₁) is used with x₁ < tan θ = 2.14 for m = 1, 2, where Lemma 4 does not apply; x₀ should be 1, not μ₀. The valid constants (using \|z\| ≥ x₁/η₀) are 67.8 and 59.9 instead of 1126 and 1188. (c) The exponential remainder is stated as x⁴/18 but used with ∫u³; both e^x − T₃ < x³/18 and < x⁴/18 hold on [0, 1.0592], and the printed C₁ (cubic −0.00073) is valid via (μu)⁴/18 ≤ μ³u⁴/18 (cubic −0.000503). (d) Arithmetic: a₀·1126 + a₁·1188 = 3194.6 > 3193; 3193 + 708 = 3901 ≠ 3897; the E₁ bound has a spurious "/m" and uses (1+μ₀)η₀ instead of 2η₀. **Corrected:** LHS ≥ C₁′(μ) + 3.9098η + 20.153η² − 568.1η³ (printed: C₁(μ) + 3.909η + 26η² − 3897η³) | X | net gain at η ~ 0.002 |
| I14 | Lemma 15 | C₂'s η³ coefficient 11896 < 11910 (compensated by the linear slack 0.0067η). The hypotheses η ≤ A₀/log t of Lemmas 6, 8, 9 need A + ε ≤ A₀, so the iteration must end with a partial step (done in Lean `region_of_iteration`) | C | none |
| I15 | §1 | "Lemma 1 establishes Theorem 1 for 2 ≤ t ≤ exp(76.47)", but Lemma 1 is stated for 3 ≤ t | C | none |

No issue invalidates Theorem 1.

## 3. Final step, with margins

The contradiction in Lemma 15 is Φ(η, μ) > (aκw(0)/2)(A₀+ε), where Φ collects Lemma 14 + (0.1186+1.568)w(0)η − 10⁻¹⁰η − 10⁻⁷ − (48), and aκw(0)/2 = 5.03905.

| Range of log t | printed constants (paper's route) | corrected constants, paper's route (η ≥ 1/(6 log t)) | corrected, coupled (η ≥ A/log t, worst case A = A₀) |
|---|---|---|---|
| [log H, 55.01] | — | min margin 9.2·10⁻³ (0.90%) | 1.75·10⁻² (1.7%) |
| [log H, 76.47] | 5.97·10⁻⁵ (5.8·10⁻⁵ relative) at 76.47 | 4.7·10⁻⁴ (0.046%) | 6.6·10⁻³ (0.64%) |
| largest top of range that still closes | 76.47+ | 78.16 | 99.41 |

All corrected-constant entries are rigorous covers by 4000 L-balls (`check_part5_lemma15_final.py`), and also Lean-checked on rational cells (`final_contradiction_55`, `final_contradiction_76`).

## 4. Can 4.896 be tightened? (task 5)

- **Coupling.** The paper's final step decouples η ≥ 1/(6 log t) from A ≤ A₀. Since the requirement is (aκw(0)/2)(A+ε) and Φ grows only like 13.5·A/log t, the worst case is A = A₀ with η = A₀/log t. This raises the margin at e^76.47 from 0.05% to 0.64%.
- **Indicative constants.** With the corrected constants, the same method gives 1/A₀ ≈ 4.852 (paper's route) or ≈ 4.811 (coupled) on t ≤ e^55.01, and ≈ 4.894 / 4.864 up to e^76.47.
  - These are *indicative*: η₀, σ₀ and hence the Lemma 5–14 constants depend on A₀ and were not recomputed for the smaller A₀.
  - Further gains: Lemma 10 using all certified m_p (p = 2 alone has slack 3.8·10⁻⁵), and a better digamma bound.
- **For BTY's own Theorem 1 none of this is needed.** 4.896 already has 0.9% slack where it is used.
- **For k = 67 it could matter.** The thesis's 19.62 fails (`../thesis_19.62/`). With a uniform repaired Littlewood constant of 19.90, k = 67 needs Z₁ ≤ 4.835 up to e^61.3 (`../requirement/REPORT.md` §4b). `check_part6_combo.py` (output `part6_output.txt`) shows that the coupled route gives about 4.830 there, while the paper's route gives only 4.867. With 20.08, k = 67 needs Z₁ ≤ 4.825, and the coupled route reaches only 4.837.

## 5. Upstream dependencies of BTY Theorem 1

| Input | Used in | Status | Our check |
|---|---|---|---|
| Platt–Trudgian, Bull. LMS 53 (2021): RH for 0 < γ ≤ 3·10¹² | Lemma 6, Lemma 1 for t < H | refereed | — |
| Heath-Brown, Proc. LMS 64 (1992), Lemma 7.1: w, Re W(z) ≥ 0 for Re z ≥ 0 | Lemma 5 | refereed | w ≥ 0, w′ ≤ 0, boundary conditions rigorous; Re W(iy) ≥ 0 spot-checked |
| Ford, *Number Theory for the Millennium II* (2002) §7, corrected arXiv:1910.08205v4: closed form of W₀ and the bound C(ν, r) | Lemmas 5, 8, 13, 14 | refereed (constants corrected on arXiv) | closed form matches quadrature; bound holds at 40 test points with Ford's c₀ |
| Kadiri, Acta Arith. 117 (2005): Prop. 2.1 (explicit formula), (24) (Γ′/Γ), Lemma 3.6 (digamma bound U), region 1/(5.69693 log t) | Lemmas 7, 8, 12; start of the iteration | refereed | U-bound rigorous on [0, 1000] + asymptotic argument; Prop. 2.1 not re-derived |
| Lehman, Acta Arith. 11 (1966), Lemmas 1, 2 | Lemma 6 | refereed | — |
| Mossinghoff–Trudgian, JNT 157 (2015), Table 5 (source of the c_k only; P ≥ 0 is trivial) | §4 | refereed | a_k exact (Lean `a_zero`, `a_one`, `a_sum`, `a_nonneg`) |
| Yang, JMAA 534 (2024): Littlewood region with 21.233 | Thm 1 for t > e^76.463 | refereed | crossover e^{21.233/4.896} = 76.4629 (Lean `cross_21233`) |
| (variant) Yang thesis 19.62 | our `classical_region_4896_from_thesis` only | thesis only, **doubtful** (see `../thesis_19.62/REPORT.md`) | the published route above does not need it |

## 6. Files

| File | Content |
|---|---|
| `source/Bellotti_Trudgian_Yang_v1.tex` | arXiv source used for the audit |
| `bty_common.py`, `polyq.py` | shared definitions (w, W, Ford's C, parameters); exact polynomial/Sturm tools |
| `check_part1_sec3_lemma5.py` | §3, Lemmas 3–5 |
| `check_part2_lemmas6_8_9_12_13.py` | Lemmas 6, 8, 9, 12, 13 |
| `check_part3_lemmas10_11.py` | Lemmas 10, 11 (certified m_p) |
| `check_part4_lemma14.py` | Lemma 14: printed vs corrected constants, direct quadrature test; writes `lemma14_corrected.json` |
| `check_part5_lemma15_final.py` | Lemma 15, final step, margins, rigorous L-cover, Theorem 1 assembly |
| `run_all.py` → `run_all_output.txt`, `part*_output.txt` | one-shot run of parts 1–5 (about 5 min) |
| `check_part6_combo.py` → `part6_output.txt` | indicative best 1/A₀ at the crossovers needed for k = 67 with Z₂ = 19.90 / 20.08 (not part of `run_all.py`) |

Output tags: `OK` = verified; `ISSUE` = a statement of the paper that is false as written but whose downstream use is verified separately; `INFO` = context. A real failure is tagged `FAIL` and makes the script exit non-zero.
