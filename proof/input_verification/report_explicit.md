# Verification of explicit inputs taken from E. S. Lee, arXiv:2602.14340

*Produced by a verification sub-agent (2026-11-06); saved verbatim by the main session. Sources are in `sources_explicit/`.*

Lee's text was re-extracted as UTF-8 (`sources_explicit/lee_2602.14340_utf8.txt`), because the existing `.txt` lost its Greek letters.

## Summary table

| Input | Status | Verdict |
|---|---|---|
| I-CHJ (Lee 3.3) | **CONFIRMED WITH CAVEAT** | The bound, the constant 1.26, the exponent 8/10, x ≥ e^1000 and the common T\* are exactly CHJ II Thm 1.3. **Lee's T-range is mis-transcribed:** CHJ requires max{51, log² x} < T < (x^α−2)/4, whereas Lee writes max{51, log x} < 2T < (x^{1/10}−2)/4. This is harmless in Lee's Prop 3.1, because T ≥ H_R gives T > log² x for k < 58 869. The (1/85, 6.391, 1/10) remark matches CHJ II Table 1, but §5 of CHJ II says 6.555 (an internal inconsistency). That variant is not usable for k = 67. |
| I-PP (Lee 3.4) | **CONFIRMED WITH CAVEAT** | Upper bound: BKLNW Cor 5.1 with b = 300 (a₂ recomputed as 1+1.93517e-8 ≤ 1+1.936e-8). Lower bound: Costa Pereira **NOT ACCESSIBLE**, but independently confirmed from BKLNW Thm 1 / Table 14. |
| I-CHL (Lee Prop 3.3) | **CONFIRMED WITH CAVEAT** | All 14 pairs match CHL arXiv v3 (the corrected version); the printed corrigendum was not accessible. The algebra is correct. **The displayed step "e^615.2373 < e^{21 log(21·3.9097e7…)}" is false** (the right side is e^431.048). The statement is still true for k ≥ 21, but only via the full Table 4 chain, and 21 is the exact threshold. For k = 67 the two named pairs suffice: [42.83, 1452.98] ∪ [600, 2040.63]. |

## 0. Sources (all in `sources_explicit/`)

- **CHJ II**, arXiv:2402.04272: v1 (1 Feb 2024), v2 (11 Nov 2024), v3 (23 Feb 2026), plus the LaTeX source `src_2402.04272v3/main.tex`. Theorem 1.3 and the α = 1/10 row are identical in all three versions. The journal version (Funct. Approx. 73 (2025)) was not accessed.
- **CHJ I**, arXiv:2111.10001 v5.
- **CHL**, arXiv:2103.05986: v1, v2, and v3 (14 Sep 2022, "updated with corrections to the paper [Math. Comp. 91]").
- **CHL Corrigendum**, Math. Comp. 93 (2024) 1019–1025, doi 10.1090/mcom/3884: not accessible (AMS returned 403 or a bot check).
- **BKLNW**, arXiv:2002.11068 v2, with LaTeX source.
- **Costa Pereira** 1985: not accessible (AMS bot check). A Corrigendum exists, Math. Comp. 48 (1987) 447; Lee does not cite it and its content is unknown.
- **Dusart**, arXiv:1002.0442, as a secondary source.

## 1. I-CHJ

### 1.1 What Lee says (§3.1)

> "if x ≥ e^{1000} and max{51, log x} < 2T < (x^{1/10}−2)/4, then there exists a point T ≤ T\* ≤ 2T such that |ψ(x+h)−ψ(x)−h+Σ(T\*)| ≤ (1.26/T)[(x+h)(log(x+h))^{8/10} + x(log x)^{8/10}]"

> "The constants 1/10, 1.26, and 8/10 can be replaced with 1/85, 6.391, and 1/10 …"

### 1.2 What CHJ II proves (v3 `main.tex` l.178–185; same text in v1 and v2)

> "Theorem 1.3. Let h=h(x) be any nonnegative function. For any α∈(0,1/2] and ω∈[0,1] there exist constants M and x_M such that for some T\*∈[T,2T] with **max{51, log² x} < T < (x^α−2)/4**, ψ(x+h)−ψ(x) = h − Σ_{|γ|≤T\*}((x+h)^ρ−x^ρ)/ρ + O\*(M (x+h)/T (log(x+h))^{1−ω} + M x/T (log x)^{1−ω}) for all x ≥ x_M."

The LaTeX reads `\log^2 x`, i.e. log squared.

CHJ II Table 1:

| log x_M | α | ω | λ | M |
|---|---|---|---|---|
| 10³ | 1/10 | 0.2 | 0.07 | 1.260 |
| 10³ | 1/85 | 0.9 | 0.07 | 6.391 |
| 4·10³ | 1/85 | 0.9 | 0.05 | 5.462 |

So 1 − ω = 0.8 and M = 1.260 for x ≥ e^1000 ✓. Lee's 2.52 is 2·1.26, coming from 1/T = 2/x^α.

### 1.3 Critical question: is T\* the same for x and x+h?

Yes. T\* depends on (x, h, T); CHJ II proves the interval version directly.

> "Corollary 3.3 … For any nonnegative function h=h(x), Σ_{x<n≤x+h} a_n = (1/2πi)∫_{κ−iT\*}^{κ+iT\*} F(s)((x+h)^s−x^s)/s ds + O\*(R(x+h,T,κ)+R(x,T,κ))."

The authors flag the issue themselves:

> "simply applying Corollary 3.2 separately … is not sufficient … because we require T\*∈[T,2T] to be the same value in both the integrals."

- **The mean-value step.** It is applied to the single function G built from the difference. G is real for real a_n, by conjugate symmetry, and continuous in t. The weight w = 6(u−1)(2−u) ≥ 0 integrates to 1.
- **From Perron integral to zero sum.** CHJ I Thm 4.1 (= CHJ II Thm B.1) is applied at the same T\*. It holds for every T with max{51, log x} < T < x^α/2 − 1; ordinates are handled via a nearby zero-free height τ.
- **Consequence.** Lee immediately bounds |Σ(T\*)| ≤ h Σ_{|γ|≤2T} x^{β−1}, which does not depend on T\*. So (3.3)'s content follows rigorously.

### 1.4 Discrepancy in the T-range

- **Upper side:** Lee bounds 2T where CHJ bounds T. Lee's condition is stronger, so it is harmless.
- **Lower side:** Lee's 2T > max{51, log x} is much weaker than CHJ's T > max{51, log² x}.
- **The log² x condition is load-bearing.** The term 1.785e(log x)^ω/(2λ²T) in CHJ II (4.6) equals 0.00197 at log x = 1000 when T > log² x, but 3.94 when T ≈ (log x)/2. The latter would give M ≈ 5.20.
- **Why Lee's Prop 3.1 is unaffected.** There 2T = x^α, T ≥ H_R and α > 1/k. Put u = α log x ≥ 29.4228. The function e^{u/2}/u is increasing and equals 83 253.7 at that point, which exceeds √2·k. Hence T > log² x for all k < 58 869.
- **Upper condition.** CHJ needs 2x^α + 2 < x^{1/10}, which holds for α ≤ 0.0993 when x ≥ e^1000.
- **k = 67 checks (all with huge margins):**
  - α = 1.16001/67 at log x = 2040: log T = 34.63, against log(log² x) = 15.24 and log H_R = 28.73;
  - log x = 238050: log T = 3563;
  - log x = 3.74·10⁷: log T = 5.6·10⁵.
- **Recommendation:** cite CHJ II Thm 1.3 with its exact hypothesis.

### 1.5 Fine print

Cor 3.3 uses a single κ = 1 + 1/log x for both endpoints, while Thm B.1 at x+h is stated with ε = 1/log(x+h). The resulting perturbations have relative size about (h/x)/log x ≲ 10⁻⁸, far below the slack in M (1.25983 against 1.260).

### 1.6 Reconstruction of M

I evaluated CHJ II (4.6) at log x = 1000 with λ = 0.07, θ′ ≥ 0.8029, a₂ = 1.0432 and K = 1.215 (CHJ II Table 2; K itself not recomputed):

- M ≤ 1.215 + 0.00197 + 0.04286 = 1.25983 ✓. The bound decreases in x (1.2398 at log x = 2040).
- For the 1/85 row I get 6.381 ≤ 6.391 ✓.
- CHJ II §5 says "M = 6.555 … and M = 5.602". This contradicts its own Table 1, but only matters for k ≥ 86.

## 2. I-PP

### Upper bound: confirmed

BKLNW Cor 5.1:

> "Let b ≥ 7. Then for all x ≥ e^b, ψ(x)−θ(x) < a₁x^{1/2}+a₂x^{1/3} …"

The table that follows gives "b = 300: a₂ = 1 + 1.936·10⁻⁸".

- I recomputed a₂(300) = 1 + 1.93517·10⁻⁸ ✓.
- a₁(300) = 1 + ε(100) = 1 + 2.45299·10⁻¹² (Table 8). Independently, θ(x) ≤ (1+1.93378·10⁻⁸)x for all x ≥ 0 (BKLNW Cor 2.1). So Lee's α₁ is valid ✓.

### Lower bound

- Costa Pereira eqs (21), (31): **NOT ACCESSIBLE**.
- **Independent proof.** Use ψ−θ ≥ θ(x^{1/2}) + θ(x^{1/3}) and BKLNW Table 14: θ(x) > (1−m₀)x for x > X₀ with log X₀ = 90 and m₀ = 2.5213·10⁻¹². For log x ≥ 300:

  ψ(x) − θ(x) > (1 − 2.5213·10⁻¹²)(x^{1/2} + x^{1/3}) > 0.999x^{1/2} + 0.885x^{1/3} ✓

- **Recommendation:** cite BKLNW Table 14 instead of Costa Pereira.

## 3. I-CHL

### 3.1 The pairs

CHL v3 Theorem 1: "For each pair (Δ, x₀) in Table 2, there exists at least one prime in the interval (x(1−Δ⁻¹), x] for all x ≥ x₀."

Table 2, in order of log x₀ = log(4·10¹⁸), 43, 46, 50, 55, 60, 75, 90, 105, 120, 135, 150, 300, 600, gives Δ = 3.90970e7, 4.18168e7, 1.63940e8, 1.06120e9, 1.02884e10, 7.69184e10, 1.74043e11, 1.84304e11, 1.91886e11, 1.97917e11, 2.02553e11, 2.07053e11, 2.30126e11, 2.51949e11.

- This is **identical** to Lee's Table 4.
- v1 and v2 had very different, wrong values. Only the v3 / corrigendum values may be used.
- The printed corrigendum was not accessed. Indirect consistency checks:
  - CHJ II §5, citing the corrigendum, implies Δ(e⁶⁰⁰) ∈ [2.507, 2.536)·10¹¹, consistent with 2.51949·10¹¹;
  - Visser (arXiv:2508.18786) reproduces the same table.

### 3.2 The algebra

Apply CHL at y = x + h. The prime lies in (x, x+h] if kx^{−1/k} ≥ 1/(Δ−1) (exact).

Lee's bound Δ⁻¹(1−Δ⁻¹)⁻² is ≥ 1/(Δ−1), so it is valid and slightly conservative. This gives log x ≤ U(k,Δ) := k log(kΔ(1−Δ⁻¹)²) ✓.

### 3.3 Combining the pairs

Lee writes "4·10¹⁸ ≤ x ≤ e^{615.2373} < e^{21 log 21·3.90970·10⁷(1−…)²}". But U(21, 3.9097e7) = **431.048**, while 615.2373 = U(21, 2.51949e11). **The displayed inequality is false**: with only the two named pairs there is a gap (e^{431.05}, e^{600}) at k = 21.

- Chaining all 14 pairs closes the gap for every k ≥ 21, and 21 is exactly the minimal such k.
- **For k = 67:** U(67, 3.9097e7) = 1452.98 ≥ 600 and U(67, 2.51949e11) = 2040.6314. The two named pairs alone cover 4·10¹⁸ ≤ x ≤ e^{2040.63}.

## Appendix: numbers

- U(k,Δ) values:

  | k | U(k, 3.9097e7) | U(k, 2.51949e11) |
  |---|---|---|
  | 20 | 409.546 | 584.964 |
  | 21 | 431.048 | 615.237 |
  | 67 | 1452.979 | 2040.631 |
  | 86 | 1886.488 | 2640.788 |
  | 90 | 1978.323 | 2767.707 |

- CHJ II M-reconstruction:

  | log x | M |
  |---|---|
  | 1000 | 1.25983 |
  | 1500 | 1.24696 |
  | 2040 | 1.23980 |
  | 5000 | 1.22695 |

- H_R argument: log(2H_R) = 29.42284, and e^{u/2}/u = 83 253.7 there, so T > log² x for k < 58 869.
