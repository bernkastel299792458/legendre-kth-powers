# Audit of Ramaré–Zuniga Alterman, arXiv:2603.25961v3, Theorem 1.2 (the bound b₄)

*Clean-context, adversarial audit written for the legendre_k67 project. Folder: `work/audit_rza/`. Nothing outside this folder was modified.*

**Source.** The arXiv LaTeX sources v1, v2 and v3 were downloaded on 2026-11-06 into `src_dl/v{1,2,3}/` (sha256 values are printed by `run_all.py`).
- The v3 `.tex` is byte-identical to the copy in `work/phase1_cs/src/2603.25961/x/`.
- Every number in Theorems 1.1 and 1.2 is produced by an embedded Sage block (v3 `.tex`, lines 87–548). We transcribed that block, re-ran it in Arb, and then replaced each of its hard-coded inputs with an independent recomputation.

Line numbers below refer to `src_dl/v3/x/OnADoubleMobiusSum-20.tex`. Equation labels are the LaTeX labels; for example, `exxp` is the display numbered (6.6) in the PDF.

## 摘要（中文）

- **结论：b₄ = 0.5936 不能使用。Theorem 1.2 的证明不成立（FAILS）。**
  - 证明的出发点不等式 (6.6)（`exxp`）是错的。
  - 原因：作者把 n_ℓ(X/ℓ;1+ε)² 里的因子 (X/ℓ)^{−2ε} 写成了 X^{−2ε}，等于丢掉了 ℓ^{2ε} ≥ 1。
  - 我们用 arb 给出了严格反例。例如 X = 1000、ε = 0.04 时，真值 S_ε(X) = 0.370740，而 (6.6) 的右边只有 0.299154。
  - 后面的 Lemma 6.2、6.3 和 Ω₁、Ω₂ 都建立在这个不等式上，所以表中九个数值**全部没有被证明**。这些数值本身是否成立：UNSURE。在 X ≤ 5·10⁴ 的数值实验里，S_ε 远小于这些值。
- **另有一个独立的大错。** Lemma 5.2 中的常数 W = ∏(1−2/p²+1/p³) 写成了 0.40282，正确值是 0.428250 = (6/π²)∏(1−1/(p(p+1)))。
  - 这一错误使 Theorem 1.1 的上界整体偏小。按真值重算后：
    - 0.6593 → 0.6849；
    - 0.4988 → 0.5247；
    - 0.467 → 0.4762；
    - 0.4664 → 0.4670。
  - 我们用两种独立方法确认了这个错误：
    - G(X) 关于 log X 的斜率；
    - 与 Helfgott 的极限 lim S₀ ≈ 0.4407 的一致性：用论文的 W 会推出 S₁₁(∞) ≈ 0.401，而 S₁₁(160) 只有 0.33497。
- **其它问题：**
  - Lemma 4.11 的 Euler 因子有一个符号错误：c₁ 应为 0.71336，不是 0.60300。
  - Lemma 4.13 的两个常数是从 4.11 复制过来的。
  - Lemma 6.2 证明中“例外类上 max m_ℓ(t) ≤ 57731/570570”是错的：11 类的最大值为 69/455，13 类为 53/385。利用 Δ ≤ 0 可以修复，ax₂ 不变。
  - 另有若干无害的笔误。
- **已核实的部分：**
  - Lemma 3.1（Δ_q 的界与符号表）在 arb 中核实。它的来源 IF Lemma 5.2 本身对偶数 q 有错，而 RZA 的 g₂ 正好修正了这一点。
  - 所有 Euler 积在 arb 中复算，都与论文一致（P0_LX 和 W 除外）。
  - 4·10⁹ 范围内的扫描、S₁₁(80)、S₁₂(80) 都与论文吻合。
- **依赖层级：** Lemma 2.2 和 2.3 的一部分只来自 Helfgott 未发表书稿中的计算（unrefereed）。即使 §6 修好，b₄ 也要依赖这一来源。
- **只修正输入、沿用论文（有缺陷的）推理链时：**
  - 0.5936 那一行变成 0.6166；若用证明里实际推出的较小系数，则是 0.5711。
  - 这些数**仍然依赖错误的 (6.6)**，只能作参考。
- **对本项目的影响：**
  - CS Lemma 6（`lem:fxone`）需要：对所有 X ≥ 3·10¹²、0 < ε ≤ 2δ/log X（δ ≤ 0.3255，即 ε ≤ 0.0227），有 S_ε(X) ≤ b₄。
  - RZA v3 的定理在形式上覆盖这些假设，但证明不成立，所以这一需求**没有满足**。
  - 因此，在“refereed + audited preprints + own reviewed lemmas”这一层级上，CS 的改进对数幂（6−4σ）以及 k ≈ 57 **目前不能声称**。
  - 退路：
    - (B) 退回 JY/KLN 的 (log T)^{5−2σ}；
    - (A) 退回 CS v1 的 log³T。
- **可以修复。**
  - 正确的恒等式是 S_ε = X^{−ε}Σ_ℓ b_ℓ c_ε(ℓ)(ℓ/X)^ε (m_ℓ+εΔ_ℓ)² + 2/ζ − G/ζ²：衰减是 X^{−ε}，不是 X^{−2ε}。
  - 探索性估计（不是证明）显示，沿这条路有望得到 b₄ ≈ 0.525（X ≥ 10¹²）或 ≈ 0.517（X ≥ 3·10¹²），比 0.5936 还好。
  - 但这需要我们自己写出并审查一个新引理。

## 1. Theorem 1.2 exactly as stated (v3)

**Quantity.** S_ε(X) = Σ_{d,e≤X} μ(d)μ(e)/[d,e]^{1+ε}, for real X > 0 and ε ≥ 0. Here [d,e] = lcm(d,e), and the sum is over all integers d, e ≤ X (non-squarefree terms vanish).

**Claim.** "When 0 ≤ ε ≤ 1/25, we have 0 ≤ S_ε(X) ≤" the value in the table below.

| range of X | condition on ε | printed value | Sage parameters (R, S) | v1/v2 value |
|---|---|---|---|---|
| 422 ≤ X < 10⁸ | ε ≤ 1/100 | 0.5107 | (158, 100) | 0.5109 (range 422–10⁷) |
| 10⁸ ≤ X < 10¹² | ε ≤ 1/100 | 0.689 | (347, 100) | 0.6323 (range 10⁷–10¹²) |
| **10¹² ≤ X < 10¹⁶** | **ε ≤ 1/25** | **0.5936** | **(112, 25)** | 0.593 |
| 10¹² ≤ X < 10¹⁶ | ε ≤ 1/50 | 0.5501 | (204, 50) | 0.5503 |
| 10¹⁶ ≤ X < 10³³ | ε ≤ 1/50 | 0.5103 | (243, 50) | 0.5104 |
| 10¹⁶ ≤ X < 10³³ | ε ≤ 1/100 | 0.4901 | (461, 100) | 0.4901 |
| X ≥ 10³³ | ε ≤ 1/25 | 0.51 | (242, 25) | 0.5099 |
| X ≥ 10³³ | ε ≤ 1/50 | 0.4905 | (440, 50) | 0.4905 |
| X ≥ 10³³ | ε ≤ 1/100 | 0.4794 | (836, 100) | 0.4794 |

The five rows in our brief are rows 2, 3, 4, 5 and 7. Note that 10¹⁶ ≤ X < 10³³ has **no** ε ≤ 1/25 row; that range needs ε ≤ 1/50.

The statement adds: "In fact, we can provide uniform upper bounds for S_ε(X) with ε ∈ [0, 1/10]". There are no other hypotheses.

**How the values are produced.** Each printed value is max(⌈Ω₁[R;T,T₀]⌉₄, ⌈Ω₂[R,S;T,T₀]⌉₄), from (6.10) and (6.11) (lines 1814–1880).
- Ω₁ covers ε ∈ [0, 1/R]; Ω₂ covers ε ∈ (1/R, 1/S].
- Θ(T, T₀) is Theorem 1.1's bound for S₀ on [T, T₀).

**v2 → v3.** Two bugs in Ω₂ were fixed (term q₂, and the exponents 2^{1/S} → 2^{2/S} and 2^{4/10}/10² → 2^{4/S}/S² in q₄). The first X-range moved from 10⁷ to 10⁸, and R was re-optimised. Neither error found below is touched by these changes.

## 2. Verdicts

| value (row) | verdict | what we can say |
|---|---|---|
| **0.5936** (10¹² ≤ X < 10¹⁶, ε ≤ 1/25) | **FAILS** — not established | (i) The proof rests on inequality (6.6), which is false (§3, I1). (ii) Its Θ = 0.4987 rests on the wrong W (I2). Re-running the paper's chain with corrected inputs (still using the false (6.6)) gives 0.6166, or 0.5711 with the coefficient the proof actually derives. Whether the statement is true: UNSURE (plausible) |
| 0.5501 (10¹²–10¹⁶, ε ≤ 1/50) | FAILS | same reasons; corrected-input replay 0.5747 / 0.5491 |
| 0.689 (10⁸–10¹², ε ≤ 1/100) | FAILS | same reasons; replay 0.7139 / 0.6985 |
| 0.5103 (10¹⁶–10³³, ε ≤ 1/50) | FAILS | same reasons; replay 0.5191 / 0.4970 |
| 0.51 (X ≥ 10³³, ε ≤ 1/25) | FAILS | same reasons; replay 0.5106 / 0.4885 |
| 0.5107, 0.4901, 0.4905, 0.4794 (the other rows) | FAILS | same reasons. Row 1 also relies on the unverified direct computation 0.445 (I15) and on I14 |
| Theorem 1.1 (S₀ bounds) | VERIFIED WITH CORRECTIONS, given the external inputs of §7 | The proof method is sound, but W is wrong. Corrected rigorous bounds, valid for all X ≥ T (§4): 0.6849 (10⁸ ≤ X < 10¹²), 0.5247 (10¹²–10¹⁶), 0.4762 (10¹⁶–10³³, J = 142), 0.4670 (X ≥ 10³³, J = 160). Printed: 0.6593, 0.4988, 0.467, 0.4664. Row 422–10⁸ (0.445) not re-verified |
| Lemma 3.1 (Δ_q bound, sign table) | **VERIFIED** (`lemma31/REPORT.md`), conditional on F₁ ≥ 0 (Ramaré, Math. Comp. 2015, refereed). The constants 0.03, 4.1, (5+ε2^ε)/2 and the sign table hold (Arb); 4c, 4d hold in sharper forms | IF's Lem 5.2 (the source) is wrong for even q; RZA's g₂ fixes it |
| Lemma 6.2's pattern constants | VERIFIED WITH CORRECTIONS | min constants hold; the max claim for classes 11/13 is false (I19), repaired via 4d |

**What "replay" means.** The replay numbers are the paper's own formulas (6.10)–(6.11) evaluated in Arb, with every input replaced by our audited value and R re-optimised (`rza_audited.py`). They are **not** proved bounds, because (6.6) is false.

## 3. The fatal error: inequality (6.6) (`exxp`, lines 1478–1489)

**Where it comes from.**
- The exact formula (`classic`) is S_ε(X) = Σ_ℓ μ²(ℓ)φ_{1+ε}(ℓ)ℓ^{−2−2ε} m_ℓ(X/ℓ;1+ε)².
- With n_ℓ(Y;1+ε) = m_ℓ(Y;1+ε) − ℓ^{1+ε}/(φ_{1+ε}(ℓ)ζ(1+ε)), this gives the identity S_ε = Σ_ℓ μ²φ_{1+ε}ℓ^{−2−2ε} n_ℓ(X/ℓ)² + 2/ζ − G(X)/ζ². This step is correct; we re-derived it.
- By Lemma 3.1 applied at Y = X/ℓ,
  - n_ℓ(X/ℓ;1+ε) = **(X/ℓ)^{−ε}** (m_ℓ(X/ℓ) + εΔ_ℓ(X/ℓ,ε)).

**What the paper writes instead.** The paper first uses φ_{1+ε}(ℓ)/ℓ^{2+2ε} ≤ φ(ℓ)/ℓ², which is correct. It then writes the square as **X^{−2ε}**(m+εΔ)², which loses the factor ℓ^{2ε}. The correct statement is the exact identity

  S_ε(X) = X^{−2ε} Σ_ℓ μ²(ℓ) φ_{1+ε}(ℓ)/ℓ² · (m_ℓ(X/ℓ) + εΔ_ℓ(X/ℓ,ε))² + 2/ζ(1+ε) − G(X;1+ε)/ζ(1+ε)².

**Why (6.6) cannot be rescued by a cruder inequality.** φ_{1+ε}(ℓ)/ℓ² ≥ φ(ℓ)/ℓ². Writing φ_{1+ε}(ℓ) = φ(ℓ) ℓ^ε c_ε(ℓ), with c_ε(ℓ) = ∏_{p|ℓ}(1 + (1−p^{−ε})/(p−1)) ≥ 1, the weight in the identity is

  X^{−ε} · (μ²φ(ℓ)/ℓ²) · c_ε(ℓ) · (ℓ/X)^ε.

So the main term decays only like X^{−ε}, not X^{−2ε}.

**Rigorous counterexample** (`rza_counterexample.py`, Arb). A and B are exactly as defined in (6.7)–(6.8), with Δ from its defining identity in Lemma 3.1. S_ε is computed both directly from the double sum and from `classic`; the two agree. The corrected identity reproduces S_ε exactly.

| X | ε | S_ε(X) | RHS of (6.6) | (6.6) |
|---|---|---|---|---|
| 1000 | 0.04 | 0.3707402897 | 0.2991542612 | **false** |
| 1000 | 0.01 | 0.4200767339 | 0.3939191080 | **false** |
| 3000 | 0.04 | 0.3565548095 | 0.2784589400 | **false** |
| 3000 | 0.02 | 0.3936352032 | 0.3417554205 | **false** |

The float exploration (`explore_exxp.py`) gives the same picture at X = 10⁴ and 5·10⁴ for ε ∈ {0.01, 0.02, 0.04, 0.1}.

**Downstream.**
- Lemma 6.2 bounds A(X), which carries the prefactor X^{−2ε}; Lemma 6.3 does the same for B(X).
- (`TotEst`) and both Ω₁ and Ω₂ inherit this. In particular, Ω₂'s factor e^{−2 log T/R} on Θ (0.61 for the 0.5936 row) and on the large cross term K_b (≈ 4.1) are unjustified.
- So the proof establishes none of the nine values. This also applies to the "uniform bounds for ε ∈ [0, 1/10]".

## 4. The second major error: W in Lemma 5.2 / Theorem 1.1

**The error.** Lemma 5.2 (`GetGq`, line 1229) gives G_q(X) = Σ_{ℓ≤X,(ℓ,q)=1} μ²(ℓ)φ(ℓ)/ℓ² = W r_q(log X + s_q) + O*(…). Here W = H_f(0) = ∏_p(1 − 2/p² + 1/p³) = (6/π²)∏_p(1 − 1/(p(p+1))). The Sage block hard-codes `APROD = 0.40282372` and uses it as an **upper** bound for W (Sage line 355; text lines 1242, 1373, 1385 and U(η;u,v;k,J)). The true value is W = 0.428249506119, so the hard-coded value is 6.3% too small.

**Evidence.**
- (a) An Arb product over p ≤ 10⁸ gives 0.4282495061 (`rza_euler.py`). The tail factors are < 1, so this is an upper bound.
- (b) Float slope of G(X) in log X: 0.4282509 on [10⁵, 10⁶] and 0.4282502 on [10⁶, 10⁷] (`explore_W_slope.py`).
- (c) Consistency with Helfgott.
  - Theorem 1.1's own decomposition, with J → ∞, gives lim S₀ = W(log 2 + S₁₁(∞)).
  - Our exact sums give S₁₁(80) = 0.333415398792 (matching the paper's S11_80 to all digits) and S₁₁(160) = 0.334974651, increasing slowly.
  - Helfgott's lim S₀ ∈ [0.4406, 0.4408] needs S₁₁(∞) ∈ [0.33569, 0.33616] with the true W. With the paper's W it would need 0.40088, which is impossible.

**Corrected Theorem 1.1 bounds.** `rza_audited.py` uses the true W. It takes all divisors n | Π(j), which can only increase S₁₁ and S₁₂, so the bound holds for every X ≥ T without the η-subdivision. J is re-optimised. Exact Arb sums come from `rza_thm11_ext.py`.

| range | printed | replay with the paper's W (float, its cutoffs) | corrected (rigorous, given §7) | J |
|---|---|---|---|---|
| 10⁸ ≤ X < 10¹² | 0.6593 | 0.65906 | **0.6849** | 21 |
| 10¹² ≤ X < 10¹⁶ | 0.4988 | 0.49852 | **0.5247** | 61 |
| 10¹⁶ ≤ X < 10³³ | 0.467 | 0.46680 | **0.4762** | 142 (the paper uses 80: 0.4929) |
| X ≥ 10³³ | 0.4664 | 0.4663 | **0.4670** | 160 (we infer that larger J would go below 0.4664) |
| (ours) X ≥ 3·10¹² | — | — | 0.5159 | 68 |

We re-derived the rest of the Part 2 argument and found it correct: the decomposition (5.3), the j = 1 term, S₀*** via G_q, Lemma 5.1 (`Tail`), and Corollaries 4.7 and 4.9.

## 5. Line-by-line findings (F = fatal, X = fixable with a numerical effect, C = cosmetic)

| # | Where | Issue | Sev. | Effect |
|---|---|---|---|---|
| I1 | (6.6) `exxp`, l.1478 | (X/ℓ)^{−2ε} replaced by X^{−2ε}; inequality false (§3) | **F** | Theorem 1.2 not proved |
| I2 | Lemma 5.2, `APROD` | W = 0.40282372 instead of 0.42824951 (§4) | **X** (large) | Θ +0.026 (10¹²–10¹⁶); Theorem 1.1 values wrong |
| I3 | Lemma 4.11 proof, l.2252, 2259, 2264 | Printed Euler factor 1 + (p^{2−ξ}−2p−1)/(p^{3−ξ}(p^ξ−1)) has a sign error. The correct factor is (1+f(p))(1−1/p) = 1 + (p²−2p^{1+ξ}+p^ξ)/(p³(p^ξ−1)). The paper's P0_LX = 0.694045937 is the product of the wrong factor; the correct product is 0.821065298, so c₁ = **0.713358**, not 0.6030. The paper's scans (logmx = 1.29424 at X = 3, logmm = 0.50551 at X = 1) were evidently done with the correct c₁ and hold (ours: 1.2941694, 0.5055381). The stated interval for c₁ and its use as `loglemma1_1` = 0.6031 in Cor. 4.12 are wrong | X | loglemma1_1 0.6031 → 0.7134 (≈ +2.7·10⁻⁴ on the 0.5936 row) |
| I4 | Lemma 4.13 | log2mx, log2mm are K₁'s numbers (identical digits). True values: sup(K₂(X) − c₂ log X) = 2.15300 (X = 6); inf(K₂ − c₂ log(X+1)) = −0.13571 (X = 1). Cor. 4.14's proof drops log2mm, which is valid only if log2mm ≥ 0. Corrected: L₂ ≤ c₂/L₀ + (log2mx − min(log2mm, 0))/L₀², so loglemma2 0.06099 → 0.06230 | C | ~10⁻⁶ |
| I5 | Lemma 4.10 | The claimed maxima Ξ₁(978118)/√978118 = 2.25265 and Ξ₂(478671)/… = 1.58716 are not maxima on (0, 5·10⁶]. Ours: 2.253270 (X = 4963335) and 1.587891 (X = 4869267); the ratio tends to the main constant 2.2537 | C | none (the analytic constants 2.5879 and 1.8223 dominate) |
| I6 | Lemma 4.8 | The error term omits the p = 2 factor F₃(2)' = 9.09 of P₀ and the tail factors, in both the text and the Sage code | C | none (v₃ = 1.666 < mx₃ = 2.6764) |
| I7 | Lemma 5.2 | The s_q interval double-counts γ (`ASUM` = 2.046752376 already contains γ; true Σ = 1.469536711) | C | none (s_q cancels) |
| I8 | Lemma 4.11 proof | The tail of T_f over p > 10⁸ is assumed ≤ 0, but its terms are positive for 10⁸ < p < 1.5·10¹³. Correct: ±2.0·10⁻⁸ | C | negligible |
| I9 | all "PRECISION 10⁸" products | Values are truncated, some below the true finite products by ≤ 3·10⁻⁹ (e.g. P1_M), so they are not strict upper bounds | C | negligible; we use Arb values |
| I10 | Lemma 6.2 / Sage `p2` | The weights ax₂ = 57731/570570 and subs = 0.8988 sum to 0.99998 < 1 on ℓ ≤ X/47. This is more than compensated: Sage's K_b leaves ax₂ and subs off the Ξ₁ terms (by operator precedence), so it is larger than the coefficient the proof derives (4.1117 vs 2.2549) | C | net conservative (−0.035 on the 0.5936 row if the proof's coefficient is used) |
| I11 | l.1768 | "t ↦ log(log t/log 10¹²)/log t is decreasing for t ≥ e·10¹²" is false (it increases up to t = e^{e·L₀}). The bound actually used, ≤ 1/(1+L₀), holds because the maximum is 1/(eL₀) | C | none |
| I12 | l.1814 and the Ω₂ paragraph | "ε ≤ 1/R < 25/4", "S ≥ 25/4": Lemmas 6.2/6.3 and the value 9.1 need ε ≤ 1/10, i.e. S ≥ 10. All rows use S ≥ 25 | C | none |
| I13 | Lemma 6.2 proof | "ℓ < X/47" should read "ℓ > X/47"; display (`crux`) misplaces √ℓ/φ_{1/2}(ℓ) (A₁ is computed correctly) | C | none |
| I14 | Lemma 6.2, second reduction | Uses Lemma 4.3's X ≥ 10³ constants (1.040, 1.048), which needs X/10.9 ≥ 10³. For 422 ≤ X < 10900 the general constants (0.578, 1.166) are needed (ax₁ 0.0161 → 0.0354). The true maximum of the window sum is 0.51020 at X ≈ 575, against the 0.48177 used (`deps_lit/`), which costs ≤ 7.6·10⁻⁵ on S_ε | X | row 1 only |
| I19 | Lemma 6.2 proof, l.1551 | "max m_ℓ(t) ≤ 57731/570570 for the classes {1,11,13,17}" is false. Exact values: class 11 gives 69/455 = 0.15165 (t ∈ [15,17)), class 13 gives 53/385 = 0.13766 (`rza_mpatterns.py`). Repaired in `lemma31/`: Δ ≤ 0 holds for classes 11, 13, 17 (sign table 4d in a stronger form), and \|m₁\| ≤ 19/210, so ax₂ = 57731/570570 remains valid | X (repaired) | none after repair (with the paper's own statements only, ax₂ = 69/455) |
| I15 | Theorem 1.1 Part 1 | 0.445 on 422 ≤ X < 10⁸ (direct computation) — **not re-verified** (too costly here) | — | row 1 only |
| I16 | Lemma 4.11 proof (min) | "log[X] − log(([X]+1)/[X])" should be "+" | C | none |
| I17 | Cor. 4.9 | The integrand is written (log u − 1); the antiderivative used is that of (log u − 2). The final bound is right | C | none |
| I18 | Lemma 5.2 proof | "w_q P ≤ ∏_{2\|q} G₁ ∏_{2∤q} G₂" has G₁ and G₂ swapped (the statement is right) | C | none |

**Checked and found correct** (re-derived by hand or in code):
- Lemmas 2.4 (m3), 2.5 (m4), with g₀(2) = √3(√2−1)/2 and g₂(2) = (H₂/H₁)(1−2^{−ξ}) (exact ratio 2.950558 ≤ the printed 2.9506).
- Every Euler factor of Lemmas 4.5, 4.6, 4.8, 4.10, 4.11 (P₁), 4.13 and 5.2. All printed closed forms equal the generic H_{f′}(0), H̄_{f′}(−δ), P_α and T_f of Theorems 4.1/4.2 at nine test primes, except P0_LX (I3).
- All tail constants b_M.
- The identities in §6 (`classic`, `vv1`/`vv2`, the 1 − G/ζ identity, the B-cancellation for ℓ > X/10.9), Bohr's inequality, and the expansion of C(X).
- Lemma 6.1 usage.
- The monotonicity of 2ε − 9.1ε²e^{−2γε}.
- The Ω₁/Ω₂ bookkeeping, *given* (6.6).

**Effect of each correction alone on the 0.5936 row**, inside the paper's own chain (`rza_effects.py`; R = 112 as printed; the best R in brackets):

| correction | value | change |
|---|---|---|
| none (paper inputs) | 0.593530 (0.592906 at R = 111) | — |
| W true, Θ(10¹²) recomputed (I2) | 0.617993 (0.616352) | +2.45·10⁻² |
| c₁ true (I3) | 0.593807 | +2.8·10⁻⁴ |
| log2mx, log2mm true (I4) | 0.593531 | +1·10⁻⁶ |
| our Euler products / our scans | 0.593530 | < 10⁻¹⁰ |
| proof-form K_b (I10) | 0.558700 (0.546537) | −3.5·10⁻² |
| all corrections (minimal / proof-form K_b) | 0.6166 / 0.5711 (best R) | |

## 6. Recomputed numerical inputs

Everything is in Arb, or uses float scans with an a-priori error bound ≤ 2·10⁻⁹ relative (tolerance 10⁻⁸) plus exact Arb evaluation at every extremal candidate.

| Input (paper) | paper value | ours | status |
|---|---|---|---|
| P1_M, P1_delta2_M, P2, P2_delta, P3 (= AP0_LX), P3_spec (= AP1_LX), P1x, P1x_delta, P1_LX, PPdelta, Sumx part, ASumx part | see `rza_assembly.PAPER` | agree to ≤ 3·10⁻⁹ (`out/rza_euler_out.txt`) | OK (I9) |
| P0_LX | 0.694045937 | 0.821065298 (correct factor) | **I3** |
| APROD = W | 0.40282372 | 0.4282495061 | **I2** |
| ASUM | γ + 2.046752376 | γ + 1.469536711 | I7 |
| Fmx1, Fmx2, mx1 (sup ≤ 4·10⁹ at X = 42) | 6.2359917, 3.1684312, 2.0680375 | same, max at 42, scan to 4·10⁹ | OK |
| mx2 (Z₁, ≤ 10⁷, at 6) | 1.9038079 | 1.9036540 at 6 | OK |
| mx3 (Z₂, ≤ 10⁶, at 2) | 2.6771003 | 2.6764484 at 2 | OK |
| mxxx, mx_aux11 (≤ 5·10⁶) | 2.2526507, 1.5871607 | 2.2532700, 1.5878911 | I5 (harmless) |
| logmx, logmm | 1.2942433, 0.5055088 | 1.2941694, 0.5055381 (true c₁) | OK |
| log2mx, log2mm | 1.2942433, 0.5055088 | 2.1529986, −0.1357138 | I4 |
| S11_80, S12_80 | 0.333415398793, 41346.25411 | 0.333415398792, 41346.2541122 | OK |
| value1 = G(10⁸; 1.1) ≥ 9.1 | 9.1 | 9.103954 | OK |
| Bound0 = 0.445 | — | not recomputed | UNSURE |
| Bound1–Bound4 (Theorem 1.1) | 0.6593 / 0.4988 / 0.4670 / 0.4664 | 0.6849 / 0.5247 / 0.4762 / 0.4670 | I2 |
| u₁ = 2323/30030, −1/30, m ≥ 0 for t < 5 | | exact: hold (attained) | OK |
| u₂ = 57731/570570 (max, classes 1, 11, 13, 17) | | 69/455 (class 11), 53/385 (class 13) | I19 (repaired) |

**Partial checks of external lemmas** (X ≤ 10⁸; not proofs):
- Lemma 2.2: |m(X)| ≤ √(2/X) and |m₂(X)| ≤ √(3/X). The ratio is ≤ 1, with equality only as X → 2⁻ and X → 3⁻.
- Lemma 2.3: |m(X)| log X/0.010032 ≤ 0.573 for X ≥ 617990; |m₂(X)| log X/0.0296 ≤ 0.954 for X ≥ 5379.
- Lemma 4.3: Σμ²/ℓ − (6/π²) log X ∈ [1.04049, 1.04708] on [10³, 10⁸] and ∈ [0.57862, 1.16546] on [1, 10⁸].

## 7. Upstream dependencies

Sources: `deps_lit/DEPS.md` (statements, page and equation numbers, status checks) and `lemma31/REPORT.md`. "Book" means H. Helfgott, *The ternary Goldbach problem*, book manuscript dated 16 Dec 2019, which is not published.

| RZA item | used for b₄ via | upstream source | status | matches RZA's use? / our check |
|---|---|---|---|---|
| Lem 2.1 \|m_q\| ≤ 1 | Lemma 6.2 (ℓ ≤ X/47) | Granville–Ramaré, Mathematika 43 (1996), Lem 10.2 | refereed | yes (secondary sources + elementary proof; original not seen) |
| Lem 2.2 \|m\| ≤ √(2/X), X ≤ 10¹⁴ | Lemma 2.5 → Lemmas 3.1, 5.1 | Helfgott book Lem 5.10, (5.62) | **unrefereed book, computation** | yes; our check holds to 10⁸ |
| Lem 2.2 \|m₂\| ≤ √(3/X), X ≤ 10¹² | Lemma 2.5 | Helfgott book (5.79) | **unrefereed book, computation** | yes (odd ℓ); our check holds to 10⁸ |
| Lem 2.3 \|m\| ≤ 0.010032/log X, X ≥ 617990 | Lemma 2.5 (H₁) | Ramaré–Zuniga Alterman, Funct. Approx. 74(2) (2026) 193–211, Cor 1.2 | refereed (but uses the book's Lem 5.10 on [1.5·10⁷, 10¹⁴)) | yes; our check holds to 10⁸ |
| Lem 2.3 \|m₂\| ≤ 0.0296/log X, X ≥ 5379 | Lemma 2.5 (H₂) | Helfgott book Lem 5.17, (5.89) | **unrefereed book** | yes; our check holds to 10⁸ |
| Lem 3.1 (Δ_q bound, sign table) | Lemmas 6.2, 6.3 | Ramaré–Zuniga Alterman, "identity factory", Math. Comp. 2026 (doi 10.1090/mcom/4216), Thm 1.7 with its Lem 5.2 replaced | refereed (published online) | **VERIFIED** (`lemma31/`). IF's own Lem 5.2 is unjustified for even q, X ≥ 10¹²; RZA's g₂ is the correct fix |
| F₁ ≥ 0 (positivity of Σμ(n)log(x/n)/n) | Lemma 3.1 claim m_q/X^ε ≤ m_q(·;1+ε) | Ramaré, Math. Comp. 84 (2015), Cor 1.10 | refereed | not obtained; Arb check for x ≤ 47, floats to 10⁷ |
| Thm 4.1 | Lemmas 4.5, 4.6, 4.10 | Zuniga-Alterman, Colloq. Math. 168 (2022), Thm 3.3 + summation by parts | refereed | yes (derivation checked) |
| Thm 4.2 (incl. E₁⁽¹⁾ = 1.044, E₁⁽²⁾ = 0.232) | Lemmas 4.8, 4.11, 4.13, 5.2 | same paper, Thm 4.6 | refereed (its D₂ uses the book's Lem 5.2) | yes, formula by formula; all Euler factors re-derived (§5) |
| Lem 4.3 (1.040, 1.048) | Lemma 6.2 (ax₁) | Ramaré, Math. Comp. 85 (2016), Lem 3.4 | refereed | yes; our check holds to 10⁸. Used outside its range for X < 10900 (I14) |
| Lem 4.4 (π, θ bounds) | all Euler-product tails | Dusart, Ramanujan J. 45 (2018), Cor 5.2, Thm 4.2 | refereed | yes (Cor 5.2 text not seen; zbMATH + numerics) |
| Lem 6.1 (1/ε < ζ(1+ε) ≤ e^{γε}/ε) | §6 | IF Lem 8.1(i) (+ Ramaré 2016 Lem 5.4) | refereed | yes |
| Theorem 1.1 Part 1 (0.445 on 422 ≤ X < 10⁸) | row 1 only | RZA's own direct computation | unrefereed computation | **not re-verified** |
| all "numerical inspections" | Lemmas 4.5–4.13, value 9.1 | RZA's own computations | unrefereed | **re-computed** (§6); errors I3–I5 |

**Tier summary for b₄.**
- Even with a repaired §6, b₄ would rest on: refereed papers; Helfgott's **unrefereed book computations** (via Lemma 2.5 and through FA-II Cor 1.2); and RZA's own computations, which we re-did.
- So the best attainable tier is "refereed + unrefereed computation (Helfgott book) + audited preprint/own lemma". The project should decide whether the book counts as an acceptable input. The project's other inputs may already use it (UNSURE; not checked here).

## 8. What our use in CS Lemma 6 needs, and whether it is met

**Use.** CS Lemma 6 (`lem:fxone`; arXiv:2507.15184v2, l.644–669 of `InghamPostArXiv.tex`; the same number in v1. Earlier versions of this report and `phase1_cs` said "Lemma 7" — that is `lem:3/2`, which does not involve b₄) uses Σ_n λ_X(n)²/n^τ ≤ ζ(τ)S_{τ−1}(X) ≤ b₄e^{γ(τ−1)}/(τ−1), with τ − 1 = ε ∈ {2δ/log X, δ/log X} and X = hT, h = 1, T ≥ T₀ ≥ 3·10¹². It therefore needs **S_ε(X) ≤ b₄ for all X ≥ 3·10¹² and all 0 < ε ≤ 2δ/log X**. Our corrected rows (`work/phase1_cs/cs_bounds.py`, `_b4_for`) use:
- (A): δ = 0.3033, so ε ≤ 0.0211 at X = 3·10¹² and ε ≤ 0.0165 at X ≥ 10¹⁶;
- (B): δ = 0.3255, so ε ≤ 0.0227 and ε ≤ 0.0177 respectively;
- b₄ = max(0.5936, 0.5103, 0.51) = 0.5936 over [10¹², 10¹⁶) ∪ [10¹⁶, 10³³) ∪ [10³³, ∞).

**Hypotheses on X and ε.** Met by the theorem as *stated*: ε ≤ 1/25 on [10¹², 10¹⁶) and ε ≤ 1/50 on [10¹⁶, 10³³). Our `_b4_for` checks this correctly.

**Validity.** **Not met.** Theorem 1.2 is not proved (I1). So, until a correct proof exists, the corrected CS bounds that use b₄ cannot be used at the tier "refereed + audited preprints + our own reviewed lemmas". These are (B), eq. (119) with (log T)^{6−4σ}, and (A), Corollary 1. The fallbacks recorded in `work/phase1_cs/REPORT.md` apply:
- (B) → JY/KLN with (log T)^{5−2σ};
- (A) → the v1 form with log³T.

**Repair (exploration only, `explore_repair.py`; not a proof).** The exact identity of §3 keeps a decay X^{−ε}, and log X ≥ 27.6. If the rest of the paper's chain is re-done with weights c_ε(ℓ)(ℓ/X)^ε X^{−ε}, the supremum over ε sits at ε → 0, i.e. at Θ:
- b₄ ≈ 0.525 for X ≥ 10¹²;
- b₄ ≈ 0.517 for X ≥ 3·10¹²;
- this stays true unless the c_ε-weights grow faster than e^{8ε}.

That is *better* than 0.5936. A rigorous version needs:
- a c_ε-weighted Theorem 1.1 (new Euler products and scans with f(p)c_{ε₀}(p));
- Lemmas 6.2/6.3 redone with the corrected weights;
- an ε-grid maximisation.

This would be our own lemma, not RZA's. It is well within reach of the code in this folder, but it must be written and reviewed before k ≈ 57 can be claimed.

**Update (repair done, `repair/REPORT.md`).** Our own Theorem R, proved and certified in Arb, gives:
- S_ε(X) ≤ **0.5159** for X ≥ 3·10¹², 0 < ε ≤ 0.0227;
- **0.5161** using no result from Helfgott's book, neither directly nor indirectly. This combines:
  - our own √-certificate to 10¹⁰;
  - Ramaré 2015;
  - Lemma R7, which re-proves Zuniga-Alterman's E₁⁽²⁾ = 0.232 from our own odd-squarefree count to 10⁸ and Cohen–Dress–El Marraki 2007;
- 0.5247 for RZA's own row (X ≥ 10¹², ε ≤ 1/25).

It was independently reviewed (`work/review_b4/REVIEW.md`: all five items CONFIRMED). The robustness of the certificate is discussed in `repair/REPORT.md` §3a: the cross term T₄ could be under-estimated by up to a factor 1.98 before the supremum would leave ε → 0⁺.

## 9. Files and how to re-run

```
python -I run_all.py          # ~3-4 min; uses cached scan A
python -I run_all.py --full   # + re-runs the 4e9 sigma-scan (~8 min)
```
`run_all_output.txt` holds the tagged result (`OK` / `ISSUE` / `FAIL`; exit code 1 on any FAIL).

| File | Content |
|---|---|
| `rza_common.py` | constants (ξ, B_κ, C_κ, Δ₁^δ), Upper/Lower rounding |
| `rza_assembly.py` | line-by-line Arb transcription of the v3 Sage block. `PAPER` = all hard-coded inputs; reproduces all nine printed values |
| `rza_euler.py` → `out/euler_products.json` | all Euler products / prime sums over p ≤ 10⁸ in Arb (16 processes, ~30 s); closed-form vs generic check |
| `rza_thm11.py`, `rza_thm11_ext.py` → `out/thm11_fullsums*.json` | exact S₁₁(J), S₁₂(J) (J ≤ 160) via a pair-sum identity; float replay of the paper's U with its cutoffs; Helfgott consistency |
| `rza_scans.py` → `out/scans_*.json` | all "numerical inspection" maxima/minima (A: 4·10⁹; B–F; G: value1; H, I: partial checks of external lemmas) |
| `rza_counterexample.py` | rigorous counterexample to (6.6) |
| `rza_mpatterns.py` | exact m_ℓ(t) pattern constants of Lemma 6.2 |
| `rza_effects.py` → `out/rza_effects_out.txt` | effect of each correction alone on the 0.5936 row |
| `rza_audited.py` → `out/rza_audited_out.txt` | corrected Theorem 1.1 bounds; Theorem 1.2 replay with audited inputs (two variants); b₄ for our X-ranges (replay, not a proof) |
| `explore_*.py` | float explorations (W slope, (6.6) at larger X, repair estimate) — not used for any claim |
| `lemma31/` | sub-audit of Lemma 3.1 (Δ_q bound, sign table, m_ℓ patterns) |
| `deps_lit/DEPS.md` | statements and status of the cited upstream results |
| `src_dl/v{1,2,3}/` | downloaded arXiv sources (data only) |
