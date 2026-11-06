# Audit of the Littlewood constant 19.62 (A. Yang, PhD thesis, UNSW 2025, Thm 1.2 / Lemma 3.1)

Source: `proof/input_verification/sources_zfr/yang_thesis.pdf` (doi:10.26190/unsworks/31825). Page numbers are the thesis's printed page labels (Ch. 3 = pp. 45–78; PDF page = printed + 8). The text was re-extracted with pypdf; formulas were checked against the `pdftotext -layout` extraction. Ford's source (arXiv:1910.08205) and the BTY source (arXiv:2603.21490) were used for cross-checks.

*Audit by fork A of the zfr_audit session. The main thread independently re-read p. 59 and confirms the arithmetic slip F1: 3.53·(1.66 − 4.27λ\*) + 0.07 gives the constant 5.93 together with the −7.24 term; the thesis prints 1.73.*

## 摘要（中文）

- **结论：19.62 无法核实——论文的证明按原文不成立。** 引理 3.8（H₁ ≤ t ≤ H₂ 的主项估计）在 n = 3 情形有一处算术错误（第 59 页）：E(t) 分子里的常数应为 3.53·1.66 + 0.07 = 5.93，论文写成 1.73（1.66 漏乘了 3.53；同一行里 4.27λ\* 那一项却乘了）。用论文自己的引理 3.6、3.7 和 (3.19)、(3.20) 不做任何舍入地重算，在论文选定的 λ\* 下，log t/loglog t 的系数在 log t ≈ 95 处达到 **3.528**；log t ∈ [64, 160] 内都超过论文声称的 3.4431。而第 78 页的最后一步只能容忍约 3.446。
- 沿用同一方法修复：如果保持论文的 λ\*，常数约为 **20.08**；如果在每个高度重新优化 λ，常数约为 **19.90**。两个数都是网格估计，不是证明。t ≥ H₂ 的部分（引理 3.9）没有问题。
- 另有若干可修复的逻辑问题。最主要的是循环依赖：引理 3.1 在高度 [H₁−10¹⁰, H₁) 需要一个常数小于 5.042 的经典零点自由区域，而论文中提供它的引理 2.1 又反过来用到引理 3.1。用 BTY 的 4.896 可以打破这个循环。此外还有十余处笔误或舍入方向错误，它们对数值的影响都小于 10⁻⁵。
- 上游依赖：Yang JMAA 2024（1.546，已评审）、Hiary–Patel–Yang JNT 2024（0.618，已评审，是 Hiary 2016 那个"不可靠"界的修正版；本链条没有直接用 Hiary 2016）、Fiori arXiv:2502.13282（Phragmén–Lindelöf，仅预印本，风险低），其余均为经典的已发表结果。

## 1. Verdicts

| # | Claim | Verdict | Evidence |
|---|---|---|---|
| 1 | Thm 1.2: ζ ≠ 0 for σ > 1 − loglog t/(19.62 log t), t ≥ 3 | **CANNOT VERIFY — proof as written fails** | §3 F1; `check_main_term_output.txt` |
| 2 | Lemma 3.8: main term ≤ 3.4431 log t/loglog t on [H₁, H₂] | **WRONG** (arithmetic slip; correct bound reaches 3.528) | §3 F1 |
| 3 | Lemma 3.9: same bound for t ≥ H₂ | VERIFIED (conclusion), despite a sign slip in its proof (F4) | direct max 3.358 over log t ∈ [225.4, 10⁷], arb cells |
| 4 | Final inequality (p. 78) given 3.4431 | VERIFIED (slack 0.04%: coefficient may be at most ≈ 3.446) | `check_constants_output.txt` |
| 5 | Lemma 3.1 induction set-up (Prop. 3.1, Assumption 3.1) | DOUBTFUL as written (circularity with Lemma 2.1, F2); repairable | §3 F2 |
| 6 | Zero-sum lemmas 3.10–3.17 (constants 0.355, 0.71, 18.6, 2.56, 0.75, 1.2532, 0.2, 0.71) | VERIFIED (several cosmetic slips, F7) | `check_constants_output.txt`, `check_error_terms_output.txt` |
| 7 | Error-term lemmas 3.18–3.20 | VERIFIED up to negligible corrections (F6, F7) | `check_error_terms_output.txt` |
| 8 | c₀…c₃, c\*, μ₀ (p. 78) | VERIFIED to all printed digits; but C₄(μ₀) = 0.93737 < 0.9376 as printed. The exact integral, 0.938124, is > 0.9376 | `check_constants_output.txt` |
| 9 | Lemma 2.3 (Ford's bound on W₀) | Printed formula WRONG (typo in c₀); the values actually used are correct | `check_ford_W0_output.txt` |

## 2. Where 19.62 is proved and what is new

- Thm 1.2 = Lemma 2.1 (classical region 1/(4.862 log t) for 2 ≤ t ≤ e^56.6) + Lemma 3.1 (19.62 for t ≥ H₁ = e^56.5). The two regions agree in strength at log t = e^{19.62/4.862} = 56.56.
- Lemma 3.1 is proved by induction (Prop. 3.1: H(A) ⇒ H(A+10⁻¹⁰⁰) for A ≤ A₁ = 1/19.62), starting from any Vinogradov–Korobov region. The proof is by contradiction against an assumed zero ρ₀.
- **Unchanged relative to the published 21.233 paper** (Yang, JMAA 534 (2024)): the ζ-bound in the strip, Lemma 3.2 = Yang 2024 Thm 1.1, |ζ(σ_k+it)| ≤ 1.546 t^{1/(2^k−2)} log t.
- **New in the thesis** (all in the zero detector):
  - Ford's two-line detector (Ford 2002, Lemma 2.2) applied to ζ′/ζ smoothed with Heath-Brown's weight w (θ = 1.1272);
  - s placed inside the strip at σ\* = 1 − A loglog(Kt+T₀)/log(Kt+T₀), with the Kadiri-type iteration;
  - |z|⁻³ tail bounds for W₀;
  - Phragmén–Lindelöf interpolation between the lines σ_n (Fiori; Hiary–Patel–Yang 0.618 on σ = ½);
  - a local zero-density estimate (Lemma 3.11) for t ≥ H₂ = e^225.4;
  - the degree-16 polynomial of BTY.
- The final constant is (C₄(μ₀) − …)/(c·w(0)) with c = 3.4431 the main-term coefficient. So 19.62 depends linearly on c.

## 3. Findings (most severe first)

**F1 — Lemma 3.8 arithmetic error (severity: fatal for the constant 19.62; fixable with a weaker constant).**

- *The error.* On p. 59 the thesis bounds log C₃ < 1.66 − 4.27λ\* and writes
  E(t) = (3.53 loglog t − log(λ\*−0.004) + **1.73**)/(2λ\*) − 7.24.
  Substituting into its own general form E(t) = (3.53(loglog t + log C_n) − log(λ\*−0.004) + 0.07)/(2λ\*) + γ/2 gives **+5.93** (= 3.53·1.66 + 0.07). The −7.24 shows that the λ\* part was multiplied by 3.53, but 1.66 was not.
- *Confirming the slip.* With the printed formula we reproduce the thesis's max 0.871536 at log t = 111.12 exactly. With the corrected formula the max is 1.1335 (log t = 96.6), and the total is 3.5458 > 3.4431.
- *Direct bound, no reductions.* Computing the bound from Lemma 3.6 + Lemma 3.7 + (3.19) + (3.20) with exact a_k gives the coefficient
  c(t) = (L₂/L₁)·[Σ_k a_k(μ(σ\*−λ\*) log kt + loglog kt + log C) + a₀(γx − log x)]/(2λ\*), x = σ\*+λ\*−1.
  - This is computed at A = A₁, the worst case, and choices favourable to the thesis are made throughout.
  - c = 3.52798 at log t = 95.5 (arb point evaluation).
  - c > 3.4431 for log t ∈ [63.9, 159.6].
  - Rigorous cell sup: 3.5347.
- *Repair.* Re-optimising λ separately at each height, using the same ingredients and constraints, lowers the sup only to ≈ 3.495, at log t ≈ 129.
  - Feeding c into the thesis's final step (with the small corrections of F6/F7) gives **1/A ≈ 20.08** (thesis λ\*) or **≈ 19.90** (optimised λ). See `check_corrected_constant_output.txt`.
  - Re-optimising θ gains < 0.02%.
  - For comparison, the same final step with c = 3.4431 gives 19.601.
  - The output also contains a per-height "local constant" table. It is a sensitivity guide only, not a theorem: the thesis's induction uses one A for all t ≥ H₁.

  | log t | 60 | 80 | 95.5 | 129 | 160 | 216 | ≥ 225 |
  |---|---|---|---|---|---|---|---|
  | 1/A, thesis λ\* | 19.42 | 20.00 | **20.08** | 19.89 | 19.59 | 19.04 | ≤ 19.09 |
  | 1/A, optimised λ | 19.26 | 19.44 | 19.59 | **19.89** | 19.46 | 19.02 | ≤ 19.09 |

**F2 — Circular dependency and a missing height range (fixable).**

- *What Lemma 3.1 needs.* Its proof (Lemmas 3.15–3.17, and the first sum in (3.26)) needs ζ ≠ 0 for Re s ≥ σ\* at all heights in [t − T₀, Kt + T₀]. For t near H₁ this includes [H₁ − 10¹⁰, H₁), which H(A) (stated for t ≥ H₁ only) does not cover.
- *What that requires.* A classical region with constant < 5.042 at height e^56.5, because σ₁ = 0.996490.
- *Why it is circular.* Inside the thesis only Lemma 2.1 (4.862) provides this. But Lemma 2.1's iteration (Lemma 2.15) needs a zero-free region of classical strength at heights up to 16·e^56.6. Above e^56.6 only Lemma 3.1 supplies it. So the two lemmas use each other.
- *Repair.* Either a joint induction, or BTY Lemma 1 (4.896 up to e^76.47). BTY's proof uses only the published 21.233, so it is non-circular.
- *Consequence for heights log t ∈ [55.0, 56.5].* 4.896 does not imply the 19.62 region there (they cross at log t = e^{19.62/4.896} = 55.0). On that range the 19.62 region rests on thesis Lemma 2.1 (4.862), whose final margin is 3·10⁻⁷ (p. 44). We did not audit Lemma 2.1.

**F3 — Lemma 3.6 used outside its range (fixable, harmless).** The thesis states that E_n is chosen so that σ\*±λ\* ∈ [σ_n, σ_{n+1}]. In fact:
- σ\* − λ\* < ½ for log t ∈ [56.5, 57.0];
- σ\* − λ\* < 5/7 on [216, 217.45], where the n = 4 formula is used.

The direct coefficient is 3.37–3.38 near H₁ (with λ = σ\* − ½) and 3.345 near e^216, so neither matters.

**F4 — Lemma 3.9 proof sign slip (cosmetic).** "Using σ\* < 1" drops the positive term δ_n2^n(1−σ\*) log T from the exponent μ. Including it, the coefficient is at most 3.358 on log t ∈ [225.4, 10⁷] (arb cells), still < 3.4431.

**F5 — Lemma 2.3 typo (cosmetic; the same typo is in BTY Lemma 4).**
- The printed c₀ = csc θ sec²θ; Ford's (arXiv:1910.08205, §7) is c₀ = 1/(sin θ cos³θ).
- The printed formula is impossible: its limit c₀c₃ = 19.69 is below lim |z|³|W₀(z)| = |w″(0)| = 45.87 (θ = 1.1272), which we verify by computing W(z) numerically.
- All constants the thesis uses (46, 52, 425, 2.56) match Ford's c₀. BTY's 51, 52 and 424 do as well.
- Ford's arXiv version also corrects c₁ and c₃ relative to the 2002 print; the thesis uses the corrected ones.

**F6 — Lemma 3.19 applies Lemma 2.7 outside its hypotheses (cosmetic).**
- Lemma 2.7 is proved for θ = 1.1338 and η ≤ A₀/log t. In Ch. 3, θ = 1.1272 and only η ≤ (A₁+ε)loglog t/log t holds.
- Redone: Σa_k|E(s_k)| ≤ (0.552 L₂ + 0.247)·ηL₂/L₁, instead of 2.9·ηL₂/L₁. This exceeds the claimed bound for log t > 122.
- Effect on C₃max (3.50): 0.0045238 → 0.0045262.

**F7 — Other slips (all cosmetic; effect < 10⁻⁵ on the final step unless stated):**
- p. 78: C₄(μ₀) = 0.937374 < 0.9376 as printed. The Taylor step uses x⁴ ≤ x³ for x ≤ 1.07. The exact integral is 0.938124, which is fine.
- (3.51): the printed bound for x = π(σ\*−β₀)/(2λ\*) uses a difference with the wrong sign. The true x is up to 4.06·10⁻⁴ (claimed < 7·10⁻⁵), so the loss is 8.2·10⁻⁶ rather than < 10⁻⁶.
- Lemma 3.6:
  - ε₂ = (π/log(H₁/2))² = 3.17·10⁻³, not < 2.5·10⁻³. Hence C₃ = 0.0728·2.50214^{14σ/3} is too small by ≤ 3.5·10⁻⁴ relative; the effect on c is < 10⁻⁴.
  - The base-case argument for |t| ≤ 3 ("c_j > ½") does not imply the claim. A direct grid check confirms it with ratio ≥ 3.78.
- (3.32): the minimum is 0.19323 (at the corners ξ = α ± 1.01i), not ≥ 0.1933. The rounded constants 7.6, 1.7 and 16 of Lemma 3.11 still hold.
- (3.27): the choice of k mixes floor and ceiling. A direct check shows a valid k exists for all δ ≤ λ₂.
- Lemma 3.15:
  - its hypothesis λ ≤ (log T)^{−1/2} is never satisfied, but it is not used;
  - its bound "≤ 10⁻¹⁰η" relies on η log T/(2λ) ≤ 1, which fails for large t, although the true term is exponentially small.
- Lemma 3.18 drops −Re(1/z) > 0. In fact Re F\*(s_k−1) = Re F₀(s_k−1) + (exponentially small) ≤ 10⁻⁷⁰, not ≤ 0.
- Lemma 3.20 omits the w(0)η·Re(1/(σ−ρ)) part for zeros with |γ| > H. It is ≤ 10⁻¹¹η².
- Lemma 3.14 rounds −17.1 to −17.09 (wrong direction); this is absorbed.
- p. 60: σ\*(H₂) − λ\*(H₂) is printed as 0.94475; the true value is 0.70603. The stated membership in [σ₃, σ₄] is correct for the true value.
- p. 72: the text says ν = λ₁/η₁ (= 137.3), but the value 76.36 = λ\*(H₂⁻)/η₁ is the one used, and it is the valid choice.

**Checked and correct:**
- the parameters (3.11);
- a_k (a = 2919857/828465);
- 1.7761, 0.0244, 0.0069 and the 0.133 bound;
- C(−1,76.36) = 51.59 > C(0,76.36) = 48.84;
- 18.6 C(−1,ν)(A₁+ε)²·1.012² = 2.553 < 2.56;
- max 2.56·a·L₂⁴/L₁² = 0.7486 < 0.75;
- Lemma 3.12 (53.16 < 56.5) and |S| < 0.71 log T (39.63 < 40.11) at H₁;
- Lemma 3.11 constants;
- (3.29), (3.39), J(λ₂)·0.71 = 15.18 < 15.4;
- C₂·L₂⁴/L₁³ max = 1.25323 at log T ≈ 912.5;
- 0.1755 < 0.2;
- C₃max = 0.004524 at log t ≈ 1144.8;
- C(−1, H/η₁) = 45.87 < 46;
- E(σ) ≤ 635η³ < 0.01η;
- the derivation of (3.19);
- Lemma 3.7;
- the identity w(u) = g∗g (Ford's definition), checked numerically.

## 4. Upstream dependencies of the 19.62 proof

| Input | Used in | Status | Remarks |
|---|---|---|---|
| Yang, JMAA 534 (2024) 128124, Thm 1.1: \|ζ(σ_k+it)\| ≤ 1.546 t^{1/(2^k−2)} log t, k ≥ 4 | Lemma 3.2, 3.6 | refereed | not re-derived here |
| Hiary–Patel–Yang, JNT 256 (2024) 195–217: \|ζ(½+it)\| ≤ 0.618 t^{1/6} log t | Lemma 3.6 (n = 3) | refereed | the corrected successor of Hiary 2016 (0.63), which relied on an error in Cheng–Graham and is the bound Johnston–Yang call unreliable. **The 19.62 chain does not use Hiary 2016.** |
| Fiori, arXiv:2502.13282, Cor. 3 (Phragmén–Lindelöf with log factors) | Lemma 3.5/3.6 | **arXiv preprint** (no journal ref on arXiv as of 2026-11-05) | low risk: a variant of the classical convexity principle |
| Ford, *Zero-free regions…*, Number Theory for the Millennium II (2002), Lemmas 2.2, 3.1, 3.4, 4.2–4.4, §7; corrected arXiv:1910.08205 | detector, (3.19), (3.44), W₀ bound | refereed; constants c₁, c₃ corrected on arXiv | the thesis uses the corrected constants (but mis-prints c₀, F5) |
| Kadiri, Acta Arith. 117 (2005): Prop. 2.1, Thm 3.1 (Weil explicit formula), Lemma 3.6 (digamma bound U) | Lemma 3.4, Lemma 2.6/2.7 | refereed | |
| Heath-Brown, Proc. LMS 64 (1992): weight w, Re W ≥ 0 | Def. 3.1 | refereed | |
| Ramaré, Math. Comp. 85 (2016), Lemma 5.4: ζ(σ) ≤ e^{γ(σ−1)}/(σ−1) | (3.12) | refereed | |
| Rosser, Amer. J. Math. 63 (1941), Thm 19 (N(T) error R₀) | Lemmas 3.10, 3.12, 3.13 | refereed | |
| Lehman, Acta Arith. 11 (1966), Lemma 2 | Lemma 3.20 | refereed | |
| Platt–Trudgian, Bull. LMS 53 (2021): RH to 3·10¹² | Lemma 3.20, Thm 1.2 for small t | refereed | |
| Abramowitz–Stegun 5.1.20 | (3.39) | standard | |
| any explicit VK region (e.g. Ford 2002, Bellotti JMAA 2024) | start of induction | refereed | |
| **thesis Lemma 2.1** (4.862, t ≤ e^56.6) | heights [H₁−10¹⁰, H₁) (F2); Thm 1.2 on [e^55.0, e^56.5] | **thesis only**, circular with Lemma 3.1 | replaceable by BTY Lemma 1 (arXiv only) for the first use only |

## 5. Thesis Thm 1.1 (4.862) vs BTY (4.896 / 4.8594) — short note

Thesis Ch. 2 and BTY §2–5 are the same argument, nearly verbatim (same θ = 1.1338, κ_m, polynomial, Lemmas 2.4–2.8 = BTY Lemmas 5–9). The differences:

1. **The positivity lemma.** Thesis Lemma 2.9 gives ≥ f(0)/12 using p = 2, 3. BTY Lemma 10 gives ≥ 0.1186 f(0) using all p < 100.
2. **The t = 0 error integral.** The thesis has ∫U/(x₀²+y²)^{3/2} < 36, which is correct (value 34.58). BTY has < 24, which is wrong. This is minor for BTY because the term is O(η³).
3. **The range and the large-height input.**
   - Thesis: A₀ = 1/4.862 up to e^56.6, closed above by Lemma 3.1 (19.62).
   - BTY Thm 1: 4.896 up to e^76.47, closed by the published 21.233.
   - BTY Thm 2 / Lemma 2: 4.8594 = BTY's stronger Lemma 10 plus the thesis's 19.62 above e^56.69. This is why 4.8594 < 4.862. Thm 2 therefore inherits F1.
4. Both print the c₀ typo (F5).

## 6. Bearing on the k = 67 argument

- The k = 67 certificates use log v/(19.62 v) wherever it is the largest of the three widths, i.e. for v = log t ≥ 55.0. This includes the window log t ∈ [64, 160], where the thesis's own method supports only ≈ 19.9–20.1.
- Whether k = 67 still closes with ≈ 19.90 or ≈ 20.08 (uniform), or with the per-height profile of §3 F1, has to be re-tested by the requirement-curve computation (`../requirement/`).
- Heights log t ∈ [55.0, 56.5] additionally rest on thesis Lemma 2.1 (F2).

## 7. Files

All scripts are deterministic and use python-flint 0.9.0 (160-bit arb) and mpmath. Run each with `python -I <script>.py` from this directory. Total run time is about 3 minutes.

| Script | Checks | Output |
|---|---|---|
| `common.py` | shared parameters, w, C(ν,r) (Ford's c₀; `printed=True` gives the thesis formula) | — |
| `check_main_term.py` | **F1**, F3, F4: Lemma 3.6 constants, domains, the thesis's E(t) reproduced and corrected, direct c(t) (point + cell scan), λ-optimisation, Lemma 3.9 | `check_main_term_output.txt` |
| `check_constants.py` | parameters (3.11), a_k, Ford constants, Lemma 3.17 numbers, c_n/C₄/exact integral, (3.50), (3.51), final inequality | `check_constants_output.txt` |
| `check_error_terms.py` | Lemma 2.7 integral (36 vs 24), F6, Lemmas 3.11–3.14, 3.18, 3.20, the base case of Lemma 3.6 | `check_error_terms_output.txt` |
| `check_ford_W0.py` | F5: W(z) by numerical integration, w = g∗g, printed vs Ford c₀ | `check_ford_W0_output.txt` |
| `check_corrected_constant.py` | indicative repaired constant (20.08 / 19.90) and the per-height table | `check_corrected_constant_output.txt` |
