# Phase 1b — a height-dependent Littlewood zero-free region (thesis method, our own proof)

**Date:** 2026-11-06. **Folder:** `work/phase1_littlewood/` (nothing outside it was modified).
**Interface file:** [`zfr_local.csv`](zfr_local.csv) (= v1, sha256 `45b22a982d005b823ad606c8b98d893d91a4764e28776154f920895fadf0584c`; snapshotted by the parent as `work/v5/inputs/zfr_local_v1.csv`). Later versions are written as new files `zfr_local_v2.csv`, … and v1 is never overwritten.
**Also in this report:**
- §11: v2 of the Littlewood profile, log t ∈ (28.73, 6.007·10⁶], file `zfr_local_v2.csv`.
- §12: Phase 1c, a local **classical** region by the BTY method, log t ∈ (28.73, 60], Z₁ = 4.614 at the bottom, file `zfr_classical_local.csv`.

## 中文摘要

- 得到了一个**随高度变化**的 Littlewood 型零点自由区域，覆盖 log t ∈ (30, 300]，共 161 个高度段，每段一个常数 Z₂。所有段都在 Arb 中严格验证，验证的是覆盖整个段的闭区间小格，而不是格点上的抽样。
- 常数：log t = 56 处 19.02，70 处 19.13，100 处 19.41，120 处 19.60；最大值 19.681 在 log t ≈ 130；然后下降，230 处为 18.76。都比论文声称的统一常数 19.62 好（只有 log t ∈ [123, 135] 这一段略高于 19.62），也明显好于修复后的统一常数 19.90。
- 方法是 Yang 博士论文第 3 章的方法，但**证明是我们自己的**。主要改动有三处：
  - 用逐高度的直接主项估计取代有错的引理 3.8；
  - 用对整个剖面的标量 s 归纳取代统一常数的归纳，并带高度窗口 [t − 10¹⁰, 16t + 10¹⁰]；
  - 取 λ = σ\* − σ_n，使 ζ 只需要在直线 σ_n 上有界，从而**不需要** Fiori 的 Phragmén–Lindelöf 预印本。
- **输入全部是已评审的结果：**
  - Hiary–Patel–Yang 2024（0.618）；Yang JMAA 2024（1.546，以及 log t > 300 时的 21.233）；
  - Ford 2002、Kadiri 2005、Heath-Brown 1992、Ramaré 2016、Rosser 1941、Platt–Trudgian 2021；
  - log t ≤ 30 时用 MTY 2024（5.558691）。
- **不依赖：** BTY、论文的引理 2.1、Fiori。论文本身未经评审，所以这一结果的等级是"我们自己的证明 + 已评审输入"。
- 存疑项见 §8；独立审阅见 §9。

## 1. Verdict and statement

**Theorem Z (ours).** For every row (a, b, Z₂) of `zfr_local.csv` and every real t with log|t| ∈ (a, b]:

  ζ(σ + it) ≠ 0 whenever σ ≥ 1 − log log|t| / (Z₂ · log|t|).

| Property | Value |
|---|---|
| Range | log t ∈ (30, 300]; 161 bands, widths 1 (v < 140), 2 (140–200), 5 (200–297), plus a last band (297, 300] |
| Constants | exact decimal strings with 3 decimals; min 18.593, max 19.681 |
| Status column | `proved` = certified by `cert_profile.py` (every band in round 0) |
| Input tier | **own proof (thesis method, unrefereed) + refereed inputs only** (§6) |
| Rigour | every band (a, b] is covered by closed cells of width ≤ 0.004; on each cell the final inequality is verified in arb ball arithmetic (128-bit) for **all** t in the cell |
| Re-run | `python -I cert_profile.py certify` (about 45 s) |

Selected values (full list in the CSV):

| log t band | 30–31 | 50–51 | 56–57 | 60–61 | 70–71 | 80–81 | 90–91 | 100–101 | 110–111 | 120–121 | 130–131 | 140–142 | 160–162 | 200–205 | 230–235 | 290–295 | 297–300 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Z₂ | 18.919 | 18.981 | 19.021 | 19.051 | 19.133 | 19.222 | 19.315 | 19.410 | 19.505 | 19.599 | **19.681** | 19.525 | 19.266 | 18.922 | 18.763 | 18.604 | 18.845 |

- The last band is worse because heights above 300 are handed to the published 21.233 (§5.2).
- Comparison: the thesis claims a uniform 19.62 (its proof fails, `proof/zfr_audit/thesis_19.62/`). The repaired uniform constant is ≈ 19.90; fork A's per-height grid estimates were 19.26 / 19.44 / 19.59 / 19.89 at log t = 60 / 80 / 95.5 / 129.
- **The new values are lower by 0.2–0.3**, for two reasons:
  - the error terms are evaluated at each height rather than at their worst case over all t (the thesis's C₃max = 0.0045 comes from log t ≈ 1145);
  - the zero-sum constant is (λ⁻³ + (2σ\*−1−λ)⁻³)/2 with λ ≈ ½, i.e. about 8.2, instead of the thesis's uniform 18.6/0.71.

## 2. The argument

Notation:

| Symbol | Meaning |
|---|---|
| v | log t |
| ℓ(t) | loglog t / log t, decreasing for log t > e |
| K | 16 |
| T₀ | 10¹⁰ |
| ε | 10⁻¹⁰⁰ |
| θ | 1.1272 (Heath-Brown weight; any θ would do) |
| w, W, W₀ | as in the thesis, Def. 3.1 |
| f, F, F₀ | Def. 3.2; f(u) = ηw(ηu), F(z) = W(z/η), F₀(z) = W₀(z/η) |
| a_k | the degree-16 polynomial P(x) = Σ a_k cos kx ≥ 0 of the thesis §2.4 / BTY: a₀ = 1, a₁ = 865534/497079, a := Σ_{k≥1} a_k = 2919857/828465 |

**Profile.**
- Z(v) is the piecewise-constant function given by the CSV on (V₀, V₁] = (30, 300], and A(v) = 1/Z(v).
- Below V₀ we use MTY: ζ ≠ 0 for σ ≥ 1 − 1/(5.558691 log|t|), |t| ≥ 2 (Res. Number Theory 10:11 (2024), Thm 1.3).
- Above V₁ we use Yang: ζ ≠ 0 for σ > 1 − ℓ(|t|)/21.233, |t| ≥ 3 (JMAA 534 (2024), Cor. 1.2).

**Hypothesis H(s)**, for s ∈ (0, 1]: no zero ρ = β + iγ has log|γ| ∈ (V₀, V₁] and β ≥ 1 − s·A(log|γ|)·ℓ(|γ|).

- **Base case.** H(S₀) holds with S₀ = 0.5 (the value in `zl_core.S0`; v1 was first certified with S₀ = 0.85, and both are valid): every Z_i ≥ 18.593 > 0.5·21.233 = 10.62, so S₀A(v)ℓ < ℓ/21.233, and Yang's region applies. S₀ enters the computation only through ε/S₀ = 2·10⁻¹⁰⁰.
- **Step (Proposition P).** For S₀ ≤ s < 1, H(s) ⇒ H(s′) with s′ = min(s + ε, 1).
- After ⌈(1 − S₀)/ε⌉ steps we reach H(1), which is Theorem Z.

**Proof of P.** Suppose H(s) holds and H(s′) fails. By symmetry there is a zero ρ₀ = β₀ + it with t > 0, v = log t ∈ (V₀, V₁] and 1 − s′A(v)ℓ(t) ≤ β₀ < 1 − sA(v)ℓ(t). Put η := 1 − β₀, so

  s·A ℓ(t) < η ≤ s′·A ℓ(t) ≤ (1 + ε/s)·s A ℓ(t),  A := A(v).

*Window.*
- Let Z_w be any upper bound for the profile over all heights in the window [t − T₀, Kt + T₀]. The classical region below V₀ counts as Z_eff := 5.558691·log V₀, and the region above V₁ counts as anything > 21.233.
- Put A_w := 1/Z_w, y := s·A_w·ℓ(Kt + T₀), σ\* := 1 − y.

**Claim W.** There is no zero with β ≥ σ\* and γ ∈ [t − T₀, Kt + T₀].

For such a γ = u (note u > e^e, so ℓ(u) ≥ ℓ(Kt + T₀)):
- **log u ∈ (V₀, V₁]:** H(s) gives β < 1 − sA(log u)ℓ(u) ≤ 1 − sA_wℓ(Kt+T₀) = σ\*.
- **log u ≤ V₀:** 1/(5.558691 log u) ≥ ℓ(u)/(5.558691·log V₀) (since loglog u ≤ log V₀) ≥ A_wℓ(Kt+T₀) ≥ y. So MTY gives β < σ\*.
- **log u > V₁:** Z_w > 21.233 gives ℓ(u)/21.233 > A_wℓ(Kt+T₀) ≥ y. So Yang gives β ≤ 1 − ℓ(u)/21.233 < σ\*. ∎

*Consequences.*
- **µ bounds.** 0 < y ≤ sA_wℓ(t) ≤ sAℓ(t) < η, so µ := y/η < 1. Also µ ≥ (A_w/A)·ℓ(Kt+T₀)/ℓ(t)·(1+ε/s)⁻¹ =: µ_low.
- **Range for Lemma 3.18 and the bound on y.** µ_low > ½ everywhere, so η/2 < 1 − σ\* < η. Moreover y ≤ A_wℓ(Kt+T₀) =: y₁ (the value at s = 1).
- **Choice of λ.** λ := σ\* − σ_n with σ₃ = ½ (or σ_n = 1 − n/(2ⁿ−2), n ≥ 4). One checks 1 − σ\* < λ < ½ and σ\* > ¾ (in code: `cell_terms`, `ok`).
- Then s_k := σ\* + ikt (k = 0..K), and everything proceeds as in the thesis, §3.3, with the replacements of §3–§4 below.

*Contradiction.* Under Claim W, the chain of §3 gives

  G(µ) ≤ η·Ψ(t; y, λ, η)  (★)

where G(µ) = ∫₀^d e^{µu}(a₁e^{−u} − a₀)w(u) du and Ψ is the explicit expression of §3.

Every term of ηΨ increases with η and with y (§4.1), and G increases on [0.85, 1] (§4.7). Hence (★) is impossible as soon as

  (C) η_max·Ψ(t; y₁, λ₁, η_max) < G(µ_low),  η_max := (1 + 2ε/S₀)·A·ℓ(t),  λ₁ := 1 − y₁ − σ_n.

The program verifies (C) for every t in every band (§5). ∎

**Why only the window matters.** This is the one place where the argument is not the thesis's. The thesis uses H(A) uniformly in t. The only facts its proof needs about zeros are:
- Claim W, used in Lemmas 3.15–3.17 and in the placement of s_k;
- "Re(z − ρ)/η ≥ −1 for every zero", which holds because y < η;
- RH below 3·10¹², used in Lemma 3.20.

Zeros above Kt + T₀ enter only through tail sums that are bounded unconditionally (Lemmas 3.12, 3.15, 3.20).

## 3. The inequality chain

From thesis (3.8) and Lemma 3.4 (Ford's detector; λ handled as in §4.2):

  0 ≤ Σ_{k≥1} a_k I(s_k, λ) + a₀ Q(σ\*),

  I(s_k, λ) = (f(0)/4λ)∫[log|ζ(s_k−λ+2λiu/π)| − log|ζ(s_k+λ+2λiu/π)|] sech²u du + Re F\*(s_k−1) − Σ_{β≥σ\*−λ} Re F\*(s_k−ρ) − Σ_{β<σ\*−λ} Re F₀(s_k−ρ) + E(s_k).

We re-derived the algebra combining Kadiri's formula (thesis (3.3)) with Ford's Lemma 2.2 (thesis (3.4)). In particular F₀ + f(0)(π/2λ)cot(πz/2λ) = F\*.

The bounds, with f(0) = ηw(0):

Page numbers are the thesis's printed page labels; Ch. 3 is pp. 45–78. "Code" means the matching lines of `zl_core.cell_terms`.

| Step | Term | Bound used here | Thesis place | How we treat it | Here (§) / code |
|---|---|---|---|---|---|
| S1 | positivity | 0 ≤ Σ_{k=0}^{K} a_k Re Σ_n Λ(n)f(log n)n^{−s_k}, from P ≥ 0 and f ≥ 0 | (3.7)–(3.8), pp. 50–51 | re-derived (one line) | — |
| S2 | k = 0 term | Q(σ\*) by Kadiri's Prop. 2.1 | Lemma 2.6 p. 30; (3.9) p. 51 | **statement taken from the thesis text**; hypotheses on w checked | §4.6 |
| S3 | k ≥ 1 terms | I(s_k, λ), from Kadiri's explicit formula (3.3) plus Ford's Lemma 2.2 (3.4) | Lemma 3.3 p. 46, Lemma 3.4 pp. 48–49 | **(3.3) and Ford's lemma taken from the thesis text**; the algebra combining them re-derived | §3 (this section) |
| S4 | exceptional λ | λ_j ↑ λ = σ\* − σ_n | p. 77 (same device, interior λ) | **own argument** | §4.2 |
| S5 | main integral, left line | (1/2λ)Σ a_k(log X_n + Y_n log kt + loglog kt) | Lemma 3.7 pp. 55–57 (replaces Lemmas 3.5, 3.6, 3.8, pp. 53–59) | **Lemma 3.7 taken from the thesis**: proof re-read, numerically spot-checked, not re-derived line by line | §4.1; `s_left` |
| S6 | main integral, right line | ≤ (a₀/2λ)(γx − log x) | (3.19), (3.20) p. 58; Ramaré (3.12) p. 53 | (3.19) **re-derived (own proof)** | §4.1; `B` |
| S7 | Σ a_k Re F\*(s_k−1) | ≤ 10⁻⁶⁰ | Lemma 3.18 pp. 74–75 | re-derived (thesis sign argument incomplete, F7) | §4.4; `tiny` |
| S8 | zero sums | ≤ −a₁F\*(σ\*−β₀) + C(−1,ν)η³Σ_k a_k[J·M(kt) + S(kt)] + 10⁻⁹⁹η | (3.26) p. 62; Lemmas 3.12 pp. 65–66, 3.13 pp. 66–68, 3.15 pp. 69–70, 3.16 pp. 70–72, 3.17 pp. 72–74 | re-derived (3.15 corrected; 3.13 bookkeeping restated); Ford's Lemma 4.4 and Re W(iy) ≥ 0 **taken as stated**, spot-checked | §4.3; `zero_err` |
| S9 | E-terms | Σ a_k\|E(s_k)\| + a₀\|E(σ\*)\|: explicit, ≤ 0.002 at v = 30, ≤ 7·10⁻⁵ at v = 300 | Lemma 3.19 p. 75 via Lemma 2.7 pp. 31–32 | **new bound** (thesis use was outside Lemma 2.7's hypotheses, F6) | §4.5; `Esum` |
| S10 | a₀Q(σ\*) | ≤ a₀[F(σ\*−1) − ηw(0)κ + \|E(σ\*)\| + 10⁻⁹η], κ = (log π − ψ(3/2))/2 = 0.55412 | Lemma 3.20 pp. 75–76 | re-derived (tail term added, F7) | §4.6; `KAPPA_Q`, `tiny` |
| S11 | F\* vs F at σ\* − β₀ | F\* ≥ F − ηw(0)(π/2λ)·0.36·π(η−y)/(2λ) | (3.51) p. 77 | re-derived (thesis sign slip, F7) | §4.6; `loss351` |
| S12 | the F-difference | a₁F(σ\*−β₀) − a₀F(σ\*−1) = G(µ) exactly (substitute u = ηx); G computed directly | (3.52) pp. 77–78 | re-derived; the thesis's C₄ bound is replaced | §4.7; `GTable` |
| S13 | induction | profile induction in s with a window | Prop. 3.1, Assumption 3.1, p. 50; Def. 3.3 p. 52 | **own argument**, replaces the uniform H(A) | §2 |

Collecting gives (★) with

  ηΨ = ηw(0)(B − a₀κ) + C(−1,ν)η³Σ_k a_k[J M + S] + E-terms + (3.51)-loss + 10⁻⁹η.

This is exactly `Psi_eta` in `zl_core.cell_terms`. The bracket B − a₀κ is positive, so replacing η by η_max is legitimate.

Typical sizes at v = 100.5 (Z₂ = 19.410, n = 3):

| Quantity | Value |
|---|---|
| ηw(0)B | 0.94454 |
| ηw(0)κ | 0.00696 |
| zero sums | 1.39·10⁻³ |
| E | 3.1·10⁻⁴ |
| (3.51) | 4·10⁻⁶ |
| ηΨ | 0.93933 |
| G(µ_low = 0.97885) | 0.93994 |

## 4. Lemma by lemma (deviations from the thesis are marked **Δ**)

### 4.1 Main term (replaces thesis Lemmas 3.5, 3.6 and 3.8) — **Δ**

- **Left line.** σ\* − λ = σ_n *exactly*. The bound used is |ζ(σ_n + iy)| ≤ X_n y^{Y_n} log y for y ≥ 3, with
  - (X₃, Y₃) = (0.618, 1/6) on σ₃ = ½ (Hiary–Patel–Yang, JNT 256 (2024), as quoted in Yang 2024 (3.5) and thesis p. 54);
  - (X_n, Y_n) = (1.546, 1/(2ⁿ−2)) for n ≥ 4 (Yang 2024 Thm 1.1).

  Thesis Lemma 3.7 (proof re-read; numerical spot check in `check_core.py` item 7) gives, with T = kt and δ = 2λ/π ≤ 1/π,

    ½∫ log|ζ(σ_n + i(T + uδ))| sech²u du ≤ log X_n + Y_n log T + loglog T.

- **Right line, (3.19).** Fix u. Then

  Σ_{k≥1} a_k log|ζ(σ′ + i(kt + uδ))| = Σ_n Λ(n)/(n^{σ′} log n)·Re(n^{−iuδ}Σ_{k≥1} a_k n^{−ikt}).

  Integrating against sech²u, ∫ n^{−iuδ} sech²u du = κ_n := πδ log n / sinh(πδ log n/2) ∈ (0, 2]; this is real, so the integral only sees the real part. Using Σ_{k≥1} a_k cos(kx) = P(x) − a₀ ≥ −a₀,

  −½ Σ_{k≥1} a_k ∫ log|ζ(σ′ + i(kt+uδ))| sech²u du ≤ a₀ Σ_n Λ(n)/(n^{σ′} log n) = a₀ log ζ(σ′).

  This is our own proof of thesis (3.19). Then log ζ(1 + x) ≤ γx − log x (Ramaré, Math. Comp. 85 (2016), Lemma 5.4).

- **Monotonicity in y.** With σ_n fixed, λ = 1 − y − σ_n and x = 1 − σ_n − 2y both decrease in y. So B increases in y: its bracket is positive, 1/(2λ) increases, and −log x increases. Hence s = 1 (y = y₁) is the worst case.
- **Comparison with fork A.** At v = 60 the n = 3 line gives c := Bℓ = 3.38460. Fork A's optimised-λ interpolation (Lemma 3.6) gives 3.3839 (`check_core.py` item 8). The line choice costs < 0.03% for v ≤ 125; for v ≥ 131 the n = 4 line is better.

### 4.2 Lemma 3.4 at the exceptional value λ = σ\* − σ_n — **Δ**

Ford's Lemma 2.2 (thesis Lemma 3.3) excludes a null set of λ. For n = 3 the value λ = σ\* − ½ is excluded, because zeros lie on the line Re s = σ\* − λ.

The argument:
- Apply (3.8) with non-exceptional λ_j ↑ λ, and let j → ∞.
- **Left integrals.** Every function log|ζ(σ\*−λ_j + i(T + 2λ_j u/π))| sech²u is bounded above by the integrable majorant log(C(2 + |T| + |u|)) sech²u, from the elementary bound |ζ(s)| ≤ C(1+|Im s|) for Re s ≥ ½, |s − 1| ≥ 0.4.
- The functions converge pointwise to log|ζ(σ_n + i(T+uδ))| ∈ [−∞, ∞), by continuity of ζ.
- So by the reverse Fatou lemma, lim sup of the left integrals ≤ the integral at λ, which §4.1 bounds.
- **Every other bound** used (§4.3–§4.6) is an explicit continuous function of λ, and its hypotheses do not involve λ.
- (C) is strict, so the contradiction persists in the limit.

The thesis uses the same limiting device (p. 77) but with λ in the interior.

### 4.3 Sums over zeros (thesis Lemmas 3.12, 3.13, 3.15, 3.16, 3.17)

We write z = σ\* + iT, T = kt ∈ [t, Kt].

| Item | Statement | Notes |
|---|---|---|
| near zeros, \|z−ρ\| ≤ λ | Re F\*(z − ρ) ≥ −C(0,ν)η³/λ³ each; for k = 1 the zero ρ₀ gives F\*(σ\*−β₀) | Lemma 3.16 (max principle on the half-disc). Needs: Claim W; Re W(iy) ≥ 0 (w is an autocorrelation); Ford's Lemma 4.4, Re(cot w − 1/w + 4w/π²) ≥ 0 on \|w\| = π/2, Re w ≥ 0 (spot-checked) |
| far zeros, \|z−ρ\| > λ | Re F₀(z − ρ) ≥ −C(−1,ν)η³\|z − ρ\|⁻³ | ν := λ/η_max (\|(z−ρ)/η\| ≥ ν); Re((z−ρ)/η) ≥ −1 since y < η; C(0,ν) ≤ C(−1,ν), so the N(z,λ) terms cancel favourably, as in the thesis |
| \|γ−T\| ≤ 1, \|z−ρ\| > λ | Σ\|z−ρ\|⁻³ ≤ J·M(T) − N(z,λ)/λ³, J := (λ⁻³ + (2σ₁−1−λ)⁻³)/2, σ₁ ≤ σ\* | Lemma 3.13; re-derived. The thesis writes "\|S\| = \|S₁\| + 2N"; the correct bookkeeping is with M = #{\|γ−T\| ≤ 1} = \|S₁\| + 2N, which gives the same bound |
| M(T) | ≤ (1/π)log(T/2π) + 2R₀(T) + 10⁻⁹ | Rosser 1941 Thm 19: R₀(T) = 0.137 log T + 0.443 loglog T + 1.588. M(T+1) − M(T−1) ≤ (1/π)log((T+1)/2π) and R₀(T±1) ≤ R₀(T) + 10⁻¹² |
| \|γ−T\| > 1 | Σ\|γ−T\|⁻³ ≤ S(T) := (1/2π)log(T/2π) + 4R₀(T) + 10⁻⁹ | Lemma 3.12. Via ∫x⁻³dN(T±x), integration by parts and Rosser; zeros with γ < 0 contribute < 10⁻¹⁰. The thesis states Lemma 3.12 and (3.33) for T ≥ e^56.5; their slack terms are O(log T/T) < 10⁻¹⁰ already for T ≥ e^28, which is all we use |
| cot terms, β ≥ σ\* − λ, \|z−ρ\| > λ | ≥ −10⁻¹⁰⁰η in total | **Δ** (Lemma 3.15 corrected). Zeros with β < σ\*: Re cot ≥ 0 (argument in (0, π/2]). Zeros with β ≥ σ\* have \|γ − T\| > T₀ (Claim W), so \|Re cot(x + iy)\| ≤ 8\|x\|e^{−2\|y\|} with \|y\| ≥ πT₀/(2λ) > 3·10¹⁰. The thesis's bound "≤ 10⁻¹⁰η" relied on η log T/(2λ) ≤ 1 (F7) |

The total error, summed with a_k, is `zero_err` = C(−1,ν)η_max³ Σ_k a_k[J·M(kt) + S(kt)]. It increases in y and η: as y grows, λ falls, J rises, ν falls and C rises.

### 4.4 Lemma 3.18 — **Δ** (cosmetic)

Re F\*(s_k − 1) = Re F₀(s_k−1) + f(0)(π/2λ)Re cot(π(s_k−1)/2λ). Since |Im(s_k − 1)| = kt ≥ e³⁰, both parts are < 10⁻⁶⁰ (fork A F7). The thesis's sign argument dropped −Re(1/z).

### 4.5 E-terms (thesis Lemmas 3.19 / 3.20) — **Δ**

E(s) = Re(1/2πi)∫_{(1/2)} F₀(s − z) Re ψ(z/2) dz + Re F₀(s), from Kadiri Prop. 2.1. It needs w′(0) = w(d) = w′(d) = w″(d) = 0, which `check_core.py` checks.

- **W₀ factor.** With x₀ := σ\* − ½ and C := C(x₀/η_max, x₀/η_max) (Ford), |W₀((s − ½ − iy)/η)| ≤ Cη³((σ−½)² + (T−y)²)^{−3/2}.
- **Digamma bound.** |Re ψ(¼ + iy/2)| ≤ log(|y|/2 + 4) + 10/3. Proof: Binet, ψ(w) = log w − 1/(2w) − ∫₀^∞ φ(t)e^{−wt}dt with 0 ≤ φ(t) = 1/(eᵗ−1) − 1/t + ½ ≤ t/12. This gives |∫| ≤ ∫(t/12)e^{−t/4}dt = 4/3; also 1/(2|w|) ≤ 2 and |log|w|| ≤ log(|y|/2 + 4).
- **Result.** Using log(|T+u|/2 + 4) ≤ log(T/2 + 4) + |u|/(T + 8),

  |E(s)| ≤ (C/2π)η³[(2/x₀²)(log(T/2+4) + 10/3) + 2/(x₀(T+8))] + Cη³/x₀³.

  For T = 0 the bracket is (2/x₀²)(log 4 + 10/3) + 2/(8x₀).
- This replaces thesis Lemma 2.7 as used in Ch. 3. That use was outside Lemma 2.7's hypotheses (fork A F6).

### 4.6 Q(σ\*) and (3.51)

- **Q(σ\*)** (Lemma 3.20). Q = f(0)(−½ log π + ½ψ(σ\*/2 + 1)) + F(σ\*−1) − Σ_ρ Re F(σ\*−ρ) + E(σ\*).
  - ψ is increasing and σ\* < 1, so the first term is ≤ −ηw(0)κ.
  - Zeros with |γ| ≤ 3·10¹² are on the line (Platt–Trudgian 2021), so Re(σ\*−ρ) > 0 and Re F ≥ 0.
  - Zeros with |γ| > 3·10¹² contribute ≤ ηw(0)Σ|γ|⁻² + C(−1, H/η)η³Σ|γ|⁻³ ≤ 10⁻⁹η, using Σ_{|γ|>H}γ⁻² ≤ 4(log H + 1)/H. This includes the f(0)Re 1/(σ−ρ) part the thesis omits (fork A F7).
- **(3.51).** F\*(x) = F(x) − f(0)(π/2λ)(1/u − cot u), u = πx/2λ, x = σ\* − β₀ = η − y ≤ η(1 − µ_low). Since (1/u − cot u)/u has positive Taylor coefficients, it is ≤ 1 − cot 1 = 0.3579 < 0.36 on (0, 1]. This replaces the thesis's ε₀ step, which had a sign slip (F7).

### 4.7 G(µ) and the final comparison

- G(µ) = a₁F(σ\*−β₀) − a₀F(σ\*−1) exactly, computed with `acb.integral`. G(0) = 0.8219901343 = the thesis's c₀.
- **G′ > 0 on [0.85, 1]**: certified on 150 sub-intervals with µ as a ball (`GTable.check_increasing`). Hence G(µ) ≥ G(µ_low) for µ ∈ [µ_low, 1).
- The program uses G at the grid point j/10⁴ ≤ µ_low.lower() (exact comparison).
- This is a direct integral; the thesis's cubic lower bound C₄(µ₀) was not rigorous as printed (0.93737 < 0.9376, F7).

## 5. Certification

### 5.1 Per cell (`zl_core.cell_terms`)

- A cell [v_a, v_b] becomes the arb ball v covering it (checked: lower ≤ v_a, upper ≥ v_b).
- All quantities are evaluated as balls in v, with y = A_w ℓ(Ke^v + T₀) (s = 1), η_max and λ = 1 − y − σ_n.
- The cell passes if `PsiEta.upper() < G(mu_low).lower()` for some line n ∈ {3, 4, 5}.
- n = 3 was used for v ≤ 131, n = 4 above.
- Cell width 0.004 (67 500 cells). The smallest relative margin is 1.5·10⁻⁶, in band (130, 131], where the n = 3 and n = 4 lines cross. Elsewhere it is 0.8–2.6·10⁻⁴, because constants were rounded up to 3 decimals.
- The (130, 131] margin is rigorous but the thinnest; if any input changes, bump that band by 0.001.

### 5.2 Window (`cert_profile.zw_window`)

- For a cell, the window is log u ∈ [v_a + log(1 − T₀e^{−v_a}), v_b + log(16 + T₀e^{−v_a})], enlarged by 10⁻⁹.
- Z_w is the exact maximum (as an arb upper value) of the bands meeting it, plus 5.558691·log 30 = 18.906 if the window dips below 30, plus 21.233 + 10⁻²⁰ if it exceeds 300.
- Floats only decide which bands meet the window, and the 10⁻⁹ enlargement dominates float error.
- **Effects of the window:**
  - Bands whose window reaches into a band with a larger Z get a smaller µ. This costs ≤ 0.004 in Z.
  - The band (297, 300] sees 21.233 above 300, so it needs 18.845 instead of ≈ 18.60.
  - The bottom V₀ = 30 was chosen so that 5.558691·log 30 = 18.906 < 18.919. So the classical region below does not lower µ there.
  - The bands beat MTY only for log t > e^{18.919/5.558691} = 30.069. On (30, 30.069) the certified region is true but slightly weaker than MTY (review item 10).

### 5.3 Profile design (`cert_profile.py design`, floats, not part of the proof)

- Local requirement on 13 points per band, including the band ends and the top 2.8.
- Three passes with window effects.
- Rounded up ×(1+2·10⁻⁴) to 3 decimals.
- The certification needed no bump.

## 6. Inputs and their status

| Input | Statement used | Source | Status | Conventions |
|---|---|---|---|---|
| Hiary–Patel–Yang | \|ζ(½+it)\| ≤ 0.618 t^{1/6} log t, t ≥ 3 | JNT 256 (2024) 195–217; quoted in Yang 2024 eq. (3.5) and thesis p. 54 | refereed | **UNSURE (minor)**: we did not read HPY itself |
| Yang | \|ζ(σ_k+it)\| ≤ 1.546 t^{1/(2^k−2)} log t, σ_k = 1 − k/(2^k−2), k ≥ 4, t ≥ 3 | JMAA 534 (2024) 128124, Thm 1.1 (arXiv:2301.03165v2 checked) | refereed | used for n = 4, 5 |
| Yang | ζ ≠ 0 for σ > 1 − loglog\|t\|/(21.233 log\|t\|), \|t\| ≥ 3 | same, Cor. 1.2 | refereed | strict >; used above log t = 300 and for the base case |
| Mossinghoff–Trudgian–Yang | ζ ≠ 0 for σ ≥ 1 − 1/(5.558691 log\|t\|), \|t\| ≥ 2 | Res. Number Theory 10:11 (2024), Thm 1.3 | refereed | used below log t = 30 |
| Ford | zero detector (Lemma 2.2), \|W₀(z)\| ≤ C(ν,r)\|z\|⁻³ (§7), Re(cot w − 1/w + 4w/π²) ≥ 0 (Lemma 4.4) | Number Theory for the Millennium II (2002); constants c₁, c₃ as corrected in arXiv:1910.08205 | refereed (+ author's arXiv corrections) | c₀ = 1/(sin θ cos³θ) (the thesis/BTY misprint it); W₀ bound spot-checked (max ratio 0.992, reviewer's dense scan) |
| Kadiri | explicit formula, Prop. 2.1 / Thm 3.1 | Acta Arith. 117 (2005) | refereed | as quoted in the thesis (3.3), Lemma 2.6 |
| Heath-Brown | weight w and its properties (w = g∗g) | Proc. LMS 64 (1992) | refereed | Re W(iy) ≥ 0 spot-checked |
| Ramaré | ζ(σ) ≤ e^{γ(σ−1)}/(σ−1), σ > 1 | Math. Comp. 85 (2016), Lemma 5.4 | refereed | |
| Rosser | \|N(T) − (T/2π)log(T/2πe) − 7/8\| ≤ 0.137 log T + 0.443 loglog T + 1.588, T ≥ 2 | Amer. J. Math. 63 (1941), Thm 19 | refereed | N counts 0 < γ ≤ T |
| Platt–Trudgian | RH for 0 < γ ≤ 3·10¹² | Bull. LMS 53 (2021) | refereed | |
| Yang's thesis, Ch. 3 | the *method*: Lemmas 3.4, 3.7, 3.12, 3.13, 3.16, (3.8), (3.26) | UNSW 2025 | **unrefereed**: we re-read these proofs, and the parts we changed are proved above | |

**Not used:** Fiori arXiv:2502.13282 (preprint), Bellotti–Trudgian–Yang (preprint), thesis Lemmas 2.1, 3.5, 3.6, 3.8, 3.9, 3.11, 3.14, and the t ≥ H₂ machinery.

**Tier:** "plus our own new lemmas" (CONTEXT.md rule 6), with refereed inputs only.

## 7. Deviations from the thesis (summary)

1. **Lemma 3.8 replaced.** The main term is computed directly per cell (§4.1). The thesis's arithmetic slip (1.73 vs 5.93) is gone with it.
2. **No interpolation.** λ = σ\* − σ_n, so ζ is used on the lines σ₃ = ½ or σ₄ = 5/7 only. Lemmas 3.5/3.6 and Fiori are not needed; the exceptional λ is handled by the limit argument (§4.2).
3. **Profile induction.** Induction in s over the whole profile with a height window, replacing the uniform H(A). This also removes the circularity with thesis Lemma 2.1 (F2): below log t = 30 only MTY is used.
4. **Height-wise error terms.** All error terms are evaluated per cell, with the actual λ and η_max, rather than as global constants (2.56, 0.75, 2.9, 0.00452, 0.9376).
5. **Corrected small slips** (fork A F6–F7): Lemma 3.15, Lemma 3.18, Lemma 3.19 (E-terms redone), Lemma 3.20 (the f(0)Re 1/(σ−ρ) tail), (3.51), and C₄(µ₀).
6. **No t ≥ H₂ regime.** Lemmas 3.9, 3.11, 3.14 are not used; above log t = 300 the published 21.233 is used.

## 8. Where we rely on the thesis text, UNSURE items, limitations

### 8.1 Steps taken from the thesis text rather than re-derived here

| # | What | Thesis place | What we did instead of a full re-derivation | Risk |
|---|---|---|---|---|
| R1 | Kadiri's explicit formula in the form (3.3), with φ(y) = (f(0) − f(y))e^{−ys}, and Lemma 2.6 (= Kadiri Prop. 2.1) | (3.3) p. 48; Lemma 2.6 p. 30 | Read as stated. Checked the algebra (3.3) + (3.4) ⇒ Lemma 3.4, and checked the hypotheses w′(0) = w(d) = w′(d) = w″(d) = 0. **Not compared with Kadiri's paper.** | low (refereed source; also used by BTY and MTY) |
| R2 | Ford's zero detector (Lemma 2.2 of Ford 2002) | Lemma 3.3 p. 46 | statement as quoted | low (refereed) |
| R3 | Lemma 3.7, the integral bound on a line from a pointwise bound | pp. 55–57 | Proof re-read (we note the typo "u ≥ −3q/2" for "u ≥ −q/2" on p. 56). It implicitly needs log(X T^Y (log T)^Z) ≥ 0, which holds for T ≥ e^28 (value ≥ 7.9). Numerical checks at T = 1000, 5000 (`check_core.py` 7); the reviewer re-derived it independently (`review/REVIEW.md` §2). | low–medium: this is the step that carries the main term |
| R4 | Ford's W₀ bound C(ν, r) (thesis Lemma 2.3 = Ford §7, with c₀ corrected) | Lemma 2.3 p. 24; (3.2) p. 48 | Formula as transcribed in `proof/zfr_audit/thesis_19.62/common.py` from Ford arXiv:1910.08205 §7. Spot-checked against W₀ computed by quadrature: max ratio 0.98 in `check_core.py` 2, and 0.9917 at r = 282 in the reviewer's denser scan (`review/ford_dense.py`). Ford's lemma is published; it is tight but not violated. | low–medium |
| R5 | Ford's Lemma 4.4: Re(cot w − 1/w + 4w/π²) ≥ 0 | (3.44) p. 71 | spot-checked on \|w\| = π/2 (`check_core.py` 6b) | low |
| R6 | Heath-Brown weight: w = g∗g, hence Re W(iy) ≥ 0, hence Re W(z) ≥ 0 for Re z ≥ 0 (harmonic minimum principle, W → 0 at ∞) | Def. 3.1 p. 47; used p. 62 and p. 71 | spot-checked (`check_core.py` 6); the identity w = g∗g was checked numerically in `proof/zfr_audit` | low |
| R7 | Hiary–Patel–Yang's 0.618 bound | p. 54 | as quoted (also quoted in Yang 2024 (3.5)) | low |

Everything else in §3 is re-derived in §4.

### 8.2 UNSURE / limitations

- An independent review (§9) was asked to attack R1–R7 and the new arguments S4, S9 and S13.
- The log t ∈ (30, 300] statement depends on the profile above and below only through Claim W. Changing the CSV requires re-running the certification.
- The constants are not optimised beyond rounding:
  - interior λ with Fiori would lower the peak near 130 slightly;
  - so would finer bands or a different θ.

## 9. Independent review

An adversarial review (a separate agent, fresh context) is in `review/REVIEW.md`.

**Status: no FATAL issue found. All open items are COSMETIC and have been addressed here.**

What the reviewer did:
- re-derived Claim W, the s = 1 worst case, the λ_j ↑ λ limit and the assembly of (★) term by term;
- tested Ford's two-line detector (to 10⁻²⁰) and Kadiri's explicit formula, with E(s) as defined (to 4·10⁻⁹), against ζ numerically;
- re-ran the v1 certification bit-for-bit;
- wrote an independent mpmath re-implementation of the cell inequality from the mathematics rather than from `zl_core.py`. It agrees with `cell_terms` to ≤ 3·10⁻¹¹ (with the same 0.36u majorant), at 20 heights;
- point-scanned every 0.05 in v: all margins positive;
- confirmed that none of the thesis audit's findings F1–F7 is inherited.

How its cosmetic items were handled:
- REPORT updates: S₀, the (30, 30.069) wording, the e^28 ranges for Lemma 3.12, (3.33) and Lemma 3.7, the run time, and Ford's 0.992 ratio.
- Code: the G-monotonicity range now starts at 0.849, so the grid point 0.8499 is covered. This was never triggered, since the minimum µ_low is 0.8808.

The v2 extension (§11) was not part of this review.

## 10. Files and how to re-run

All scripts are deterministic and run with `python -I <script>` from this folder (python-flint 0.9.0, mpmath).

| File | Purpose |
|---|---|
| `zl_core.py` | constants, weight w, G(µ), Ford's C(ν,r), Rosser counts, E-bounds, the per-cell inequality `cell_terms` |
| `cert_profile.py` | `design` (float search, writes `profile_design.json`), `certify` (rigorous; writes `zfr_local.csv`, `cert_summary.json`, `cert_log.txt`) |
| `profile_design.json` | the profile that was certified |
| `zfr_local.csv` | **interface file** (logt_lo, logt_hi, Z2, status, notes) |
| `zfr_local_coarse.csv` (`make_coarse.py`) | the same in 57 bands of width ≈ 5 (Z2 = max over merged bands; implied by `zfr_local.csv`) |
| `cert_summary.json`, `cert_log.txt`, `cert_run_output.txt` | per-band results: cells, lines used, minimum relative margin |
| `check_core.py` → `check_core_output.txt` | sanity checks of the analytic ingredients (0 failures) |
| `explore_local.py` | exploration only |

```bash
python -I cert_profile.py certify
```

```bash
python -I check_core.py
```

## 11. Version 2 of the Littlewood profile: log t ∈ (28.73, 6.007·10⁶] (`zfr_local_v2.csv`)

v1 (`zfr_local.csv` = `zfr_local_v1.csv`) is not changed. After the GTable fix below it was re-certified and is byte-identical (sha256 `45b22a98…`). v2 is a separate file, made by `cert_v2.py`.

### 11.1 What changes relative to v1

| | v1 | v2 |
|---|---|---|
| V₀ (bottom of the profile) | 30 | 28.73 (> log(3·10¹²) = 28.7297) |
| window below V₀ | MTY, Z_eff = 5.558691·log V₀ | the same with V₀ = 28.73; heights below 3·10¹² satisfy RH anyway |
| V₁ (top of the profile) | 300 | 6 006 998 |
| window above V₁ | Yang's 21.233 (+10⁻²⁰) | min(21.233, Z_VK(V₁)) + 10⁻²⁰, Z_VK(v) := 54.004·(log v)^{4/3}/v^{1/3} (= 11.588 at V₁) |
| bands | 161 | 366: (28.73, 29], (29, 30], then v1's band edges, then geometric bands (×1.05) above 300 |
| ζ-lines | n = 3, 4, 5 | n = 3 … 18; for each band the 3 best by a float ranking, plus 3, 4, 5 |
| initial cell width | 0.004 | 0.004·max(1, a/100), halved for a ≥ 300 |

The proof is the one of §2–§5, unchanged except for the window above V₁.

**Claim W above V₁.**
- Bellotti's Vinogradov–Korobov region, in Littlewood form: ζ ≠ 0 for σ ≥ 1 − 1/(Z₃(log t)^{2/3}(loglog t)^{1/3}) is the same as σ ≥ 1 − ℓ(t)/Z_VK(log t).
- Z_VK(v) is decreasing for log v > 4.
- So for log u > V₁: ℓ(u)/Z_VK(log u) ≥ ℓ(u)/Z_VK(V₁) > A_w·ℓ(u) ≥ y whenever Z_w ≥ Z_VK(V₁) + 10⁻²⁰. The 21.233 alternative is as in §2.
- **Base case:** every band has Z ≥ 11.68 > S₀·21.233 = 10.62.

**V₁** is the first geometric band edge at which the float-designed local constant exceeds Z_VK. Above V₁ the published VK region is better than this method.

**Constant used.** We use Z₃ = 54.004 (the arXiv version). The journal version prints 53.989 (LOG.md). The larger constant gives the weaker region, so using it is safe either way.

### 11.2 Result

Status: **all 366 bands certified** (`cert_v2_log.txt`, `cert_v2_run_output.txt`: "ALL BANDS CERTIFIED: True (366 bands, 27511 s)"). There are 7 410 616 Arb cells in total, and every row of `zfr_local_v2.csv` has status `proved`. sha256 of `zfr_local_v2.csv`: `ceacbca5a5dbdb9dae7a9835daef238487b0d0fa495392259897ed891288d345`.

Values from `zfr_local_v2.csv`:

| log t band | 28.73–29 | 30–31 | 40–41 | 100–101 | 300–315 | 512–538 | 967–1015 | ≈ 10⁴ | ≈ 10⁵ | ≈ 10⁶ | min (4.94–5.19)·10⁶ | top (5.72–6.01)·10⁶ |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Z₂ | 18.922 | 18.919 | 18.933 | 19.410 | 18.564 | 17.744 | 17.040 | 14.688 | 13.057 | 12.202 | 11.683 | 11.691 |

Z₂ ranges over [11.683, 19.681]. The smallest relative margin is 1.6·10⁻⁸, in band (2 377 171, 2 496 030]. It is small but certified: the proof only needs the Arb lower bound of each cell margin to be > 0. v2 has **not been independently reviewed** (v1 has; see `review/REVIEW.md`).

### 11.3 Inputs added for v2

These are additional to §6; the §6 table is unchanged.

| Input | Statement used | Source | Status |
|---|---|---|---|
| Bellotti | ζ ≠ 0 for σ ≥ 1 − 1/(54.004 (log t)^{2/3}(loglog t)^{1/3}), t ≥ 3 | J. Math. Anal. Appl. 536 (2024) 128249 (journal: 53.989; we use the weaker 54.004) | refereed; used only above log t = 6 006 998 |
| Yang | the same Thm 1.1 as in §6, now for the lines n = 4 … 18 | JMAA 534 (2024) | refereed |

### 11.4 GTable fix and review status

- **GTable fix.** `GTable.check_increasing` now starts at µ = 0.849 instead of 0.85, so the grid point 0.8499 is covered (review item, §9). The v2 run was started before the fix. G is the same function in v1 and v2 (θ = 1.1272), so the re-run v1 check covers v2 as well.
- **Review.** v2 has **not** been independently reviewed. It uses the reviewed v1 code path; only the window function and the set of lines differ.

## 12. Phase 1c — a height-dependent CLASSICAL zero-free region (BTY method, our own proof)

**Interface file:** [`zfr_classical_local.csv`](zfr_classical_local.csv) (columns logt_lo, logt_hi, Z1, status, notes; first version sha256 `f8a41422f6fe4988a5c314a32780adfaebd24f26a852492eb35df96105afa083`).

**Tag:** *our proof using the BTY method.* Bellotti–Trudgian–Yang, arXiv:2603.21490v1, is a preprint. We use its method and re-check every step for our parameters. We do **not** use its Theorem 1 (4.896) as an input. Section and lemma numbers below refer to the arXiv LaTeX source (`proof/zfr_audit/bty_4.896/source/`); audit item numbers I1–I15 refer to `proof/zfr_audit/bty_4.896/REPORT.md`.

### 12.0 中文摘要

- 在 log t ∈ (28.7296, 60] 上得到了随高度变化的**经典型**零点自由区域：ζ(σ+it) ≠ 0，只要 σ ≥ 1 − 1/(Z₁ log t)。共 81 段，全部在 Arb 中按闭区间小格严格验证（15 655 格，运行 6 秒）。
- 常数：log t ∈ (28.73, 28.8] 为 **4.614**，29 处 4.618，30 处 4.631，31 处 4.643，32 处 4.653，40 处 4.726，45 处 4.759，49–50 为 4.780。都优于 BTY 的统一常数 4.896，在最关键的 log t ≈ 29 处约低 5.8%。
- 与 BTY 原证明相比的改动：
  - 局部窗口归纳，取代全局假设；
  - η 与 A 耦合，取最坏情形 η = A/log t；
  - 误差项按 (k, m) 逐项估计：k ≥ 1 时 T₂ 可以忽略，m ≥ 1 时 x_m 更大；
  - 引理 14 改为直接计算；
  - 引理 5 不再需要 c₀ 拆分（精确的标度关系）；
  - 引理 11 只用到 u ≤ 54，素数只取 p ≤ 31。
- 输入全部是已评审的结果：Platt–Trudgian、MTY、Kadiri、Heath-Brown、Ford、Lehman，以及我们审计中已严格验证的 m_p 表。
- **能降到多少：** 这个方法在 log t ≈ 29 处的极限大约是 4.60；θ 已经最优。4.5 达不到，主要损失来自 µ ≈ log t / log(16t) ≈ 0.912。
- 独立审阅（§12.8）：没有致命问题，也没有重大问题；6 处外观性问题均已处理。修正后重新验证，CSV 逐字节不变。

### 12.1 Statement

**Theorem C (ours).** For every row (a, b, Z₁) of `zfr_classical_local.csv` and every real t with log|t| ∈ (a, b]: ζ(σ + it) ≠ 0 whenever σ ≥ 1 − 1/(Z₁ log|t|).

| Property | Value |
|---|---|
| Range | (28.7296, 60]; 81 bands of width 0.1 (to 32), 0.25 (to 36), 0.5 (to 44), 1 (to 60). The first edge 28.7296 is below log H = 28.72966, where RH holds |
| Rigour | every band is covered by closed v-cells (initial width 0.002, bisected on failure); on each cell the final inequality (CL) is verified in arb (128-bit) for **all** t in the cell |
| Smallest relative margin | 6.1·10⁻⁶ (band (31.8, 31.9]) |
| Re-run | `python -I check_cl.py` (constants, about 3 s), then `python -I cert_classical.py certify` (6 s) |

| log t band | 28.73–28.8 | 29.0–29.1 | 29.5–29.6 | 30.0–30.1 | 31.0–31.1 | 31.9–32 | 35–35.25 | 40–40.5 | 45–46 | 49–50 | 53–54 | 55–56 | 57–60 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| Z₁ | **4.614** | 4.618 | 4.624 | 4.631 | 4.643 | 4.653 | 4.685 | 4.726 | 4.759 | 4.780 | 4.800 | 4.838 | ≈ 5.13 |

- The bands above 54 are weaker on purpose. Their windows reach above the profile top 60, where only MTY is used. They are correct but of no use. The Littlewood bands are better there anyway.
- **For comparison** (`proof/zfr_audit/bty_4.896/check_part5`, indicative, BTY's own constants for A₀ = 1/4.896): the coupled final step at log t = 28.73, 32, 50 gives 4.659, 4.688, 4.792. The gain of about 0.045 at the bottom comes from the per-(k, m) error terms (§12.4 L8) and the direct Lemma 14.

### 12.2 The argument

**Notation.**
- v = log t; A_j = 1/Z_j for band j.
- H = 3·10¹², T₀ = 10¹⁰, K = 16, ε = 10⁻¹⁰⁰, S₀ = ½, θ = 1.1338.
- w, W, W₀ are as in BTY Def. 1 and Lemma 4. κ_m are as in BTY (3.3) (M = 6), δ_m = (2σ−1)m, and f, F are as in BTY Def. 2.
- a_k are those of BTY §4 (the same polynomial as in §2 above).

**Global parameters** (`cl_core.py`):
- Z_MIN = 4.58 ≤ every Z_j, A_MAX = 1/Z_MIN;
- η₀ = (1+2ε)A_MAX/log H = 0.0075998;
- σ₀ = 1 − A_MAX/log(KH + T₀) = 0.9930691.

**Hypothesis H(s):** no zero β + iγ with log|γ| in band j and β ≥ 1 − s·A_j/log|γ|.
- **Base:** H(½) follows from MTY, since ½A_j < 1/5.558691.
- **Step:** H(s) ⇒ H(min(s+ε, 1)) for s ∈ [½, 1). Then H(1) is Theorem C.

**Proof of the step.** Take a violating zero ρ₀ = β₀ + it with t > 0 and v = log t in band i, and put A = A_i.
- If t < H, then β₀ = ½ and there is nothing to prove. So t ≥ H.
- η := 1 − β₀ ∈ (sA/v, (s+ε)A/v] ⊂ (0, η₀].

*Window.* Let T = Kt + T₀. Choose y > 0 with:
- y ≤ A_j/min(b_j, log T) for every band j that meets [log H, log T];
- y ≤ 1/(5.558691·log T) if log T > 60 (MTY);
- y ≤ A/v.

Put σ = 1 − s·y. Then every zero with |γ| ≤ T has 1 − σ ≤ β ≤ σ:
- RH below H;
- H(s) in the bands, because log γ ≤ min(b_j, log T);
- MTY above 60;
- the lower bound by the symmetry ρ ↦ 1 − ρ̄.

This is the only place where zeros other than ρ₀ enter, apart from the unconditional tail sums (Lemma 6, |γ| > T). It replaces BTY's global hypothesis "no zeros with β ≥ 1 − A/log γ, γ ≥ H" (Lemma 6, Lemma 15).

*Consequences.*
- µ := (1 − σ)/η = s·y/η ∈ [y·v/((1+ε/s)A), y·v/A] ⊂ [µ_lo, µ_hi], µ_hi ≤ 1. So σ − β ≥ σ − 1 ≥ −η for every zero, which is the range where Lemma 5 (22) applies.
- σ ≥ 1 − A_MAX/log(KH+T₀) = σ₀, since y ≤ A_MAX/log T.
- β₀ ≤ σ, because µ ≤ 1.

In code (`window_y`, `cell_margin`), y is the minimum of these candidates, taken with log T at the cell top (an upper bound). The cap y ≤ A/vb is applied too. A smaller y is always allowed.

### 12.3 The inequality chain (CL)

With s_k = σ + ikt and the test function f of BTY Def. 2, the chain of BTY (44)–(47) reads as follows. Here f(0) is read as ηw(0) throughout (audit I10), and the k = 1 pair ρ₀, 1 − ρ̄₀ is isolated as in Lemma 6.

  0.1186·ηw(0) ≤ Σ_k a_k Re Σ_n Λ(n)n^{−s_k} f(log n)  (Lemma 10′, P ≥ 0)
  = Σ_k a_k [ηw(0)Σ_m κ_m(−½log π + ½Re ψ((s_k+δ_m)/2+1)) + Re F(s_k−1) − Re Σ_ρ F(s_k−ρ) + E_k]  (Lemma 9)

Bounding term by term (Lemmas 12, 13, 6, and the error bound of §12.4):

  **L14(η, µ)** := a₁F(σ−1+η) + a₁F(σ−η) − a₀F(σ−1)
   ≤ ηw(0)·[(κa/2)·v + C_UP] + 10⁻¹⁰η + 10⁻⁷ + η³(P_ERR + Q_ERR·v),

where:
- C_UP = (κ/2)Σ_{k≥1} a_k log(k/2π) + D_k0 + tiny − 0.1186 ≤ −1.687064 (BTY: −1.568 − 0.1186);
- κ = 433/859, a = 2919857/828465;
- P_ERR = 396.563, Q_ERR = 278.200 (`cl_constants.json`).

Put KC := aκw(0)/2 = 5.03905 and

  Q(η, µ, v) := L14(η, µ) − ηw(0)C_UP − 10⁻¹⁰η − 10⁻⁷ − η³(P_ERR + Q_ERR v) − KC·η·v.

The chain says Q ≤ 0 at the actual (η, µ, v). We show Q > 0, which is a contradiction:
- **Monotonicity in η (fixed µ, v).** ∂Q/∂η ≤ |∂L14/∂η| + w(0)|C_UP| + 10⁻¹⁰ − KC·log H ≤ 48.55 + 9.57 − 144.77 < 0 (`check_cl.py`). The bound on ∂L14/∂η comes from |W′(z)| ≤ w(0)/z² for real z > 0 and the explicit arguments (§12.4 L14). So Q(η, µ, v) ≥ Q(η_max(v), µ, v), η_max = (1+ε)A/v, for all η ≤ η_max.
- **At η = η_max,** KC·η·v = KC(1+ε)A exactly. So the condition is

  **(CL)** L14(η_max, µ) − η_max w(0)C_UP − 10⁻¹⁰η_max − 10⁻⁷ − η_max³(P_ERR + Q_ERR v) > KC(1+ε)A  for all µ ∈ [µ_lo, µ_hi], v ∈ cell.

### 12.4 Lemma by lemma (Δ = changed relative to BTY)

| BTY lemma | What BTY states | What we use / check (`check_cl_output.txt`) |
|---|---|---|
| L1–L2, §1 | the region for t ≤ e^{76.47}, then the Littlewood region | not used (we prove our own local statement) |
| L3 (f ≥ 0) | Σκ_m xᵐ > 0 on (0, 1] | re-checked exactly (Sturm) |
| L4 (Ford) | \|W₀(z)\| ≤ C(ν,r)\|z\|⁻³ | used with Ford's c₀ = 1/(sin θ cos³θ) (audit I2); refereed input |
| L5 (21) **Δ** | Re F(z) + Re F(2σ−1−z̄) ≥ 0 for 0 ≤ Re z ≤ 2σ−1; proof via B(y) with the split c₀m ≤ δ_m ≤ m, c₀ = 151/153, ε₀ = 1/2000 | For our σ₀, 2σ₀−1 = 0.98614 < 151/153, so BTY's c₀ fails. But δ_m = d·m with one d = 2σ−1, so Σ_m c_m/(d²m²+y²) = d⁻²Σ_m c_m/(m²+(y/d)²). Hence B ≥ 0 reduces to B̃(Y) = Σ_m (b_m m − \|b_m\|ε₀/m)/(m²+Y²) ≥ 0, i.e. c₀ = 1. Checked exactly by Sturm with ε₀ = 11/20000 ≥ η₀²C(r,r)/((2σ₀−1)²w(0)) = 5.343·10⁻⁴, r = (2σ₀−1)/η₀ = 129.76. The \|Im z\| → ∞ edge uses Σ m b_m = 1/859 > 0 (audit I3) |
| L5 (22) | > −44η/\|Im z\|² for −η ≤ Re z, \|Im z\| ≥ T₀ | constant 5.7 re-checked for our η₀; needed only for Re z ∈ (σ−1, σ) (audit I4), which holds since µ ≤ 1 |
| L6 **Δ** | far zeros > −10⁻⁸; near zeros from the global hypothesis | near zeros (\|γ\| ≤ T) from the window of §12.2; far-zero bounds re-checked with η ≤ (1+2ε)A_MAX/log t: 1.5·10⁻⁹ (k = 0), 1.6·10⁻¹⁰ (k ≠ 0) |
| L7 (Kadiri Prop. 2.1) | explicit formula | refereed input; hypotheses w′(0) = w(d) = w′(d) = w″(d) = 0 re-checked |
| L8–L9 **Δ** | \|E\| < 623η³ (t = 0), 14η² + 424η³ (t ≥ H) per m; total 187η² + 8013η³ (8396 after audit I8) | Per (k, m) with x_m = σ₀(1+2m) − m − ½ and C_m = C(x_m/η₀, x_m/η₀):<br>• k ≥ 1: T₁ ≤ (C_m/2π)η³(2 log(kt)/x_m² + 4·10⁻²⁴) (I₂ by pairing ±y, U(x) ≤ log x for x ≥ 2; I₁ + I₃ via U ≤ 6 + log(1+\|x\|)); T₂ ≤ C·η³/H³, because \|s_k+δ_m\| ≥ kt (BTY used only Re).<br>• k = 0: T₁ ≤ (C_m/2π)η³J(x_m), with J a rigorous upper sum using the monotonicity of Re ψ(¼ + iy/2) in \|y\| (J = 23.651, 1.516, 0.423, …); T₂ ≤ C(sp_m/η₀, ·)η³/sp_m³.<br>• Total η³(396.6 + 278.2 log t), i.e. ≈ 60η² + 400η³ at our η, instead of 187η² + 8396η³ |
| L10 **Δ** | ≥ 0.1186 f(0) via primes < 100, m ≤ 15, N = e⁵⁹ | primes p ≤ 31 only, m ≤ 15, N = e⁵⁴ (15 log 31 = 51.5 < 54); m_p from the audit's certified Table 1 (m₅ = 0.00735649, audit I11): κΣ log p·m_p = 0.118619 > 0.1186 |
| L11 **Δ** | f(u) ≥ κf(0) for u ≤ 59 | fails at u = 59 for our larger η₀ (w(59η₀) < κw(0)); proved for u ≤ 54: h(0) = 0, h′ > 0 on [0, ½], h ≥ 0.099 on [½, 54] (20 000 balls) |
| L12 | Σ ≤ (aκ/2)log t − 1.568 | same structure: k ≥ 1 via Kadiri (24) (error 5.6·10⁻¹⁴ < 10⁻¹⁰); k = 0 by the monotonicity of ψ with our σ₀ (s38 = −0.04063) |
| L13 | pole terms ≤ 10⁻¹⁰η | re-checked (H/η₀ > 10¹⁰, C(−1, 10¹⁰) = 50.07 < 51) |
| L14 **Δ** | L14 ≥ C₁(µ) + 3.909η + 26η² − 3897η³ (corrected: C₁′(µ) + 3.9098η + 20.153η² − 568.1η³) | **evaluated directly:**<br>• the m = 0 part a₁W(1−µ) − a₀W(−µ) = G(µ) = ∫₀^d e^{µu}(a₁e^{−u} − a₀)w du by rigorous quadrature on a 10⁻⁴ grid, using G′ > 0 on [0.879, 1] (121 balls);<br>• all other 19 arguments are real and ≥ R_MIN = 1/η₀ − 3 = 128.58, where W(z) = w(0)/z + w″(0)/z³ + O*(max\|w‴\|/z⁴ + 10⁻⁵⁰), with w″(0) = −50.0697 and max\|w‴\| ≤ 139.71 (Taylor at 0, w′(0) = 0; tails e^{−zd} < 10⁻⁵⁵).<br>• Check at (η, µ) = (0.0074, 0.912): quadrature 1.0242596, ours [1.02426 ± 2.9·10⁻⁶], BTY corrected 1.0237242 |
| L15 **Δ** | iteration with η > 1/(6 log t), μ > 1 − 2.78/log t, global A | the induction of §12.2 with the window, and the η-monotonicity of §12.3 (coupled worst case η = A/log t) |

### 12.5 Certification

- **Per cell** (`cl_core.cell_margin`). For v ∈ [va, vb]:
  - η = (1+ε)A/v as a ball;
  - µ_lo = y·va(1 − 2ε)/A and µ_hi = y·vb/A;
  - G at the grid point ≤ µ_lo;
  - L14_rest with η, µ as balls;
  - the result is a lower bound of (CL) LHS − RHS.

  Cells where it is not > 0 are bisected (down to 10⁻⁶). None remained.
- **Band edges** are the decimal strings of the CSV. The first and last cell of each band extend one ulp beyond the float edge, so the closed decimal band is covered (review C1).
- **Window** (`cl_core.window_y`): as in §12.2.
  - log T at the cell top is taken as an upper bound.
  - A band is included if the decimal a_j is below log T.
  - min(b_j, log T) uses the decimal b_j, rounded up.
  - Each candidate is rounded down.
- **Design** (`cert_classical.py design`, floats, not part of the proof):
  - per band, a bisection for the smallest Z at 9 points, with the band itself set to the trial Z in the window;
  - 4 passes, rounded up to 3 decimals with a factor 1 + 4·10⁻⁵.
- Every constant in `cl_constants.json` is stored rounded in the safe direction:
  - C_UP = upper + 10⁻²⁵;
  - P_ERR, Q_ERR ×(1 + 10⁻²⁰);
  - J and C_m are upper bounds.

### 12.6 Inputs and their status

| Input | Statement used | Source | Status |
|---|---|---|---|
| BTY method | Lemmas 3–15 (as re-checked above); not Theorem 1 | arXiv:2603.21490v1 | **preprint**; every step used is re-derived or re-checked here and in `proof/zfr_audit/bty_4.896` |
| Platt–Trudgian | RH for 0 < γ ≤ 3·10¹² | Bull. LMS 53 (2021) | refereed |
| Mossinghoff–Trudgian–Yang | ζ ≠ 0 for σ ≥ 1 − 1/(5.558691 log\|t\|), \|t\| ≥ 2 | Res. Number Theory 10:11 (2024), Thm 1.3 | refereed; base case and window above log t = 60 |
| Kadiri | Prop. 2.1 (explicit formula); (24) (digamma); Lemma 3.6 (U(y)) | Acta Arith. 117 (2005) | refereed (U-bound also checked rigorously on [0, 1000] in the audit, part 2) |
| Heath-Brown | Lemma 7.1: Re W(z) ≥ 0 for Re z ≥ 0 | Proc. LMS 64 (1992) | refereed |
| Ford | W₀ bound C(ν, r) | NT for the Millennium II (2002) §7; arXiv:1910.08205v4 | refereed (+ author's corrections) |
| Lehman | Lemmas 1, 2 (sums over zeros) | Acta Arith. 11 (1966) | refereed |
| Binet bound | \|Re ψ(¼+iy/2)\| ≤ log(\|y\|/2+4) + 10/3 (tail of J, y ≥ 1000) | §4.5 above (own proof) | own |
| m_p, p ≤ 31 | certified lower bounds for min_x G_p(1, x) | `proof/zfr_audit/bty_4.896/part3_output.txt` | own rigorous computation |

**Not used:** BTY Theorem 1 (4.896), Yang's thesis, Fiori, the Littlewood bands of §1–§11.

**Tier:** our proof using the BTY method (preprint), with refereed inputs only.

### 12.7 How far below 4.896 can this go at log t ≈ 29?

- **About 4.60 at best.** The certified 4.614 is within about 0.3% of what this machinery gives:
  - **θ:** a float scan of θ ∈ [1.10, 1.19] gives the best local value 4.608 at θ = 1.1338, which is BTY's choice.
  - **Lemma 10:** using the u-dependent weight f(log n) instead of κηw(0) might add about 0.03 to 0.1186. That moves Z by about 0.005.
  - **κ_m:** BTY estimate their κ_m to be within 1% of the limit of the Stechkin–Heath-Brown construction.
- **The binding loss is structural.** σ must lie to the right of all zeros up to height 16t, so µ = (1−σ)/η ≤ log t/log(16t) = 0.912 at log t = 28.7. G(0.912) = 0.9942 against G(1) = 1.0058. That 1.2% alone keeps Z above ≈ 4.56.
- **Z₁ = 4.5 is out of reach** with this weight and this trigonometric polynomial. It would need a better polynomial (lower a/G for µ ≈ 0.91), or a different method.
- Using RH below 3·10¹² does not help further: every height in the window is above H.

### 12.8 Review status

An independent adversarial review (a separate agent, fresh context) is in `review_classical/REVIEW.md`.

**Status: no FATAL and no MAJOR issue. Six COSMETIC items, all handled.**

What the reviewer did:
- Re-derived steps §12.2–§12.3 from the BTY LaTeX and the audit:
  - the induction and base case (MTY Thm 1.3 checked);
  - the window (RH below H, min(b_j, log T), MTY above 60, far zeros via Lemma 5 (22) with µ ≤ 1);
  - all signs and rounding directions;
  - Lemma 5 with c₀ = 1 (correct; BTY's own split would fail for our σ₀);
  - Lemma 11 up to u ≤ 54;
  - the per-(k, m) error terms;
  - the direct L14;
  - the η_max worst case. Treating µ as fixed is legitimate: it is a monotonicity argument at the true µ.
- Checked, for every cell, the hypotheses the code does not assert: σ ≥ σ₀ (slack 10⁻⁴), η_max ≤ η₀, and 0.88003 ≤ µ ≤ 0.9551.
- Wrote an independent mpmath implementation from the formulas:
  - C_UP, Q_ERR and κΣ log p·m_p agree to all digits;
  - P_ERR = 396.479 (ours 396.563, the safe side, from the J upper sum);
  - J(x₀) = 23.6418 (ours 23.6510);
  - ∂L14/∂η ≈ 4.1 (our bound 48.55);
  - L14 by two independent quadratures agrees to 12 digits and lies inside our ball at 14 heights;
  - every point margin is positive and above our cell margin (e.g. 4.08·10⁻⁴ vs 3.89·10⁻⁴ at v = 28.73);
  - a dense scan of 1799 points, all band edges included, gives min relative margin 4.6·10⁻⁵ at v ≈ 31.8–31.9.
- Tested the Lemma 5 positivity numerically at 7 extreme (σ, η) pairs, for y up to 10⁷.
- Re-ran `check_cl.py` and `certify` bit-for-bit.

How its cosmetic items were handled:
- **C1 (the only literal gap).** The cells used binary-float band edges while the CSV prints decimals. On 13 slivers of width ≤ 1.4·10⁻¹⁵, the certificate gave only the next band's constant. **Fixed:** every band's first and last cell now extend one ulp beyond the float edge, so the decimal band is covered; `window_y` uses decimal bounds of the edges. Re-certified: all 81 bands OK, and the CSV is byte-identical (sha256 `f8a41422…`).
- **C2, C3.** Two negligible slips in `check_cl.py`, both corrected; the constants are unchanged:
  - Lemma 6's B29 now uses log(2H/T₀)/(4H²) + 1/(8H²);
  - Lemma 12's error term has its first summand coded as x/(2|z|²).
- **C4.** The derivative bound 48.55 is argued in §12.3; the code only evaluates it.
- **C5.** `acb.integral` is called with a ball endpoint d(θ); the effect is < 10⁻¹⁰⁰.
- **C6.** The cap y ≤ A/vb is redundant but harmless.
- **Limitation.** The bands in (57, 60] are held at ≈ 5.13 by the G-table floor µ ≥ 0.88, not by the inequality. They lie outside the needed range.

### 12.9 Files

| File | Purpose |
|---|---|
| `cl_core.py` | parameters, w, W_big, G/GTable, L14_rest, window_y, cell_margin |
| `check_cl.py` → `check_cl_output.txt`, `cl_constants.json` | all parameter-dependent lemma checks and the constants C_UP, P_ERR, Q_ERR (0 failures) |
| `polyq.py` | exact polynomial arithmetic and Sturm sequences (copied unchanged from `proof/zfr_audit/bty_4.896/`) |
| `cert_classical.py` | `design` → `profile_classical.json`; `certify` → `zfr_classical_local.csv`, `cert_classical_summary.json`, `cert_classical_log.txt` |

```bash
python -I check_cl.py
```

```bash
python -I cert_classical.py certify
```
