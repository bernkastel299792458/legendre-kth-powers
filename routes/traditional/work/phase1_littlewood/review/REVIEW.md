# Referee report: height-dependent Littlewood zero-free region on log t ∈ (30, 300]

**Object under review:** `work/phase1_littlewood/` (`zl_core.py`, `cert_profile.py`, `check_core.py`, `zfr_local.csv`, `cert_summary.json`, `cert_run_output.txt`).

**Claim.** For each of the 161 bands (a_i, b_i] in `zfr_local.csv`, ζ(σ+it) ≠ 0 whenever log|t| ∈ (a_i, b_i] and σ ≥ 1 − loglog|t|/(Z_i log|t|).
- The bands cover (30, 300] contiguously.
- The constants are 18.593 ≤ Z_i ≤ 19.681. The brief says "18.56"; the file's minimum is 18.593, in band (285, 290].

**Method.** The proof follows A. Yang, PhD thesis (UNSW 2025), Ch. 3, with:
- a per-height profile Z(v);
- an induction in a scalar s ∈ [S₀, 1] (S₀ = 0.85 in REPORT.md, 0.5 in the current code);
- λ = σ* − σ_n, with no Phragmén–Lindelöf step;
- local error terms throughout.

Referee: adversarial review, 2026-11-06. No existing file was modified. All scripts are in this folder; run each with `python -I <script>.py`.

**Versions reviewed.** The author kept working while this review ran (11:26–12:50).

| File | State reviewed | Notes |
|---|---|---|
| `zfr_local.csv` | sha256 `45b22a98…fadf0584c` | identical to `zfr_local_v1.csv` and `work/v5/inputs/zfr_local_v1.csv` |
| `zl_core.py` | md5 `2f333646…`, 12:02 | Since my first reading: S₀ 0.85 → 0.5; LINES extended to n ≤ 18; new guard ν > 2 tan θ. None changes the argument |
| `cert_profile.py` | md5 `4d73fff3…`, 11:56 | Since my first reading: Z_w ≥ 21.233 + 10⁻²⁰ above 300 |
| `REPORT.md` | 11:59 | **did not exist when the review started**; reviewed in §10 |

- All numerical runs here (`indep_check`, `rerun_cert`, the §8 decomposition) were made at 12:13–12:50, so against the current code.
- The 12:04 `cert_summary.json` reproduces exactly.
- The v2 profile (`profile_v2.json`, `cert_v2*`, V₀ = 28.73 … 6·10⁶) is a different claim and was **not** reviewed.

## Verdict

**I found no fatal error.**

- **The logic holds.** The height-dependent induction, the zero-free window, the λ = σ* − ½ limit argument and the assembly of the final inequality are all correct. I re-derived each of them independently (§2–§5).
- **The code matches the mathematics.**
  - All rounding directions are correct and the cell cover is exact.
  - The certification run reproduces bit-for-bit (§6).
  - An independent mpmath re-implementation, written from the derivation in §2 and not from `zl_core.py`, agrees with `cell_terms` to ≤ 3e-11 once it uses the same 0.36u majorant for 1/u − cot u. With the exact value it is smaller by ≤ 5.4e-6, the code's deliberate over-estimate. Tested at 20 heights.
  - A point scan every 0.05 in v at the band constants gives positive margins everywhere (worst relative margin 2.4e-4, at v = 92).
- **None of F1–F7 from the thesis audit is inherited** (§7).
- **The ~1% improvement over the thesis audit's per-height table is explained** (§8). It is not an artefact.

**Documentation.** When this review started, the write-up the code cites (`REPORT.md`) did not exist. That was my one FIXABLE finding.

- REPORT.md appeared at 11:59.
- I have since checked it against my independent derivations (§10). Its arguments are correct:
  - Claim W;
  - the λ_j ↑ λ limit;
  - the Lemma 3.13 bookkeeping;
  - the digamma proof (simpler than mine and valid);
  - the E-bound;
  - the tiny terms;
  - (3.51) and G.
- **What remains is only COSMETIC** (§9, §10). The most visible items are:
  - the REPORT says S₀ = 0.85, but the code now uses 0.5;
  - it states that bands on (30, ≈32.5] beat MTY, which is false on (30, 30.07);
  - §9 still holds a `REVIEW_STATUS` placeholder.

---

## 1. Inputs actually used

All inputs are refereed, or are thesis lemmas re-checked here.

| Input | Where used | Checked here |
|---|---|---|
| MTY 2024 (RNT 10:11): σ ≥ 1 − 1/(5.558691 log\|t\|), \|t\| ≥ 2 (closed region) | window below v = 30 | constant read in `sources_zfr/mty_rnt.txt` l.16 |
| Yang JMAA 534 (2024), arXiv 2301.03165v2: σ > 1 − loglog\|t\|/(21.233 log\|t\|), \|t\| ≥ 3 (open region); \|ζ(σ_k+it)\| ≤ 1.546 t^{1/(2^k−2)} log t, k ≥ 4, t ≥ 3 | base case; window above 300; lines n ≥ 4 | constants read in `2301.03165.txt` l.12, l.65 |
| Hiary–Patel–Yang JNT 256 (2024): \|ζ(½+it)\| ≤ 0.618 t^{1/6} log t, t ≥ 3 | line n = 3 | cited as (3.5) in 2301.03165 |
| Ford 2002, Lemma 2.2 (two-line detector) = thesis Lemma 3.3 | Lemma 3.4 | numerically **exact to 1e-20** against ζ (§5, check 1) |
| Kadiri 2005, Prop. 2.1 (explicit formula) = thesis Lemma 2.6 / (3.3) | (3.8), Q(σ*), E(s) | numerically **exact to 4e-9** against Σ Λ(n)n^{−s}f(log n) (check 2) |
| Ford 2002 §7, W₀ bound, with c₀ = 1/(sin θ cos³θ) (arXiv correction) | all W₀ estimates | spot checks at the actual (ν, r) (check 4) |
| Ford 2002, Lemma 4.4; Heath-Brown 1992 (Re W ≥ 0 on Re z ≥ 0) | Lemma 3.16 | `check_core.py`; (3.42) re-checked (check 5) |
| Ramaré 2016, Lemma 5.4: ζ(σ) ≤ e^{γ(σ−1)}/(σ−1) | main term | — |
| Rosser 1941, Thm 19 | M(T), S(T) | derivation re-done (§2.3) |
| Platt–Trudgian 2021 (RH to 3·10¹²); Lehman 1966 | k = 0 zero sum (negligible) | §2.6 |

**Not used:** the Fiori preprint (Phragmén–Lindelöf), thesis Lemma 2.1 (4.862, the source of F2), thesis Lemmas 3.6, 3.8, 3.9 and 3.11, and thesis Lemma 2.7 (the source of F6).

---

## 2. Independent re-derivation of the cell inequality

Notation:
- t is the height of the hypothetical zero ρ₀ = 1 − η + it, and v = log t.
- ℓ(t) = loglog t / log t.
- A = 1/Z_band, A_w = 1/Z_w, K = 16, T₀ = 10¹⁰.
- f(u) = ηw(ηu), F(z) = W(z/η), F₀(z) = W₀(z/η).

Choose:
- σ* = 1 − y, with y = s·A_w·ℓ(Kt + T₀);
- s_k = σ* + ikt;
- λ = σ* − σ_n.

### 2.1 Starting point

The starting point is the positivity identity (thesis (3.8)) for non-exceptional λ ∈ (1 − σ*, ½):

  0 ≤ Σ_{k≥1} a_k I(s_k, λ) + a₀ Q(σ*).

- **Lemma 3.4 holds.** I(s, λ) is Kadiri's formula with −Re ζ′/ζ(s) replaced by Ford's detector. I verified this structure numerically (§5, checks 1–2).
- **All a_k > 0** (min a_k = 19/677835). This matters for Lemma 3.18 and for every "a_k × (lower bound)" step.

### 2.2 Main term

The left line is Re = σ_n, with δ = 2λ/π. Thesis Lemma 3.7 applies at σ = σ_n, Z = 1:

  (1/4λ) a_k ∫ log|ζ(σ_n + i(kt + δu))| sech²u du ≤ (a_k/2λ)(log X + Y log kt + loglog kt).

- Lemma 3.7's proof silently needs log(X T^Y log T) ≥ 0 in order to drop the I₂-range weight. This holds for T ≥ e^30.

The right line is handled by (3.19):
- Expand log|ζ(σ′+iτ)| = Σ Λ(n)/(n^{σ′} log n)·cos(τ log n).
- Use ½∫cos(ωu)sech²u du = (πω/2)/sinh(πω/2) ∈ (0, 1].
- Use P ≥ 0, so that −Σ_{k≥1} a_k cos(kx) ≤ a₀.

This gives −(1/4λ)Σ_{k≥1} a_k ∫ log|ζ(s_k + λ + …)| ≤ (a₀/2λ) log ζ(σ* + λ). Ramaré then gives log ζ(1 + x) ≤ γx − log x.

Total: f(0)·B, where B is exactly the `B` of `cell_terms` (l.175–180). ✓

### 2.3 Zero sums, k ≥ 1

I rearrange as in (3.26).

**Disc |s_k − ρ| ≤ λ.**
- Every zero in the disc has Re(s_k − ρ) ≥ 0, by the zero-free window (§3).
- (3.42) gives Re F* ≥ −C(0, ν)η³/λ³ per zero, with ν ≤ λ/η.
- For k = 1, ρ₀ contributes exactly F*(σ* − β₀).

**Outside the disc.**
- Every zero has Re((s_k − ρ)/η) ≥ −y/η = −µ > −1 and |(s_k − ρ)/η| > λ/η ≥ λ/η_max = ν.
- Ford gives |F₀| ≤ C(−1, ν)η³|s_k − ρ|⁻³.

**Strip |γ − kt| ≤ 1: the pairing ρ ↔ ρ′ = 1 − ρ̄.**
- Valid for λ ≤ σ* − ½, so in the limit λ_j ↑ λ when n = 3.
- d₁ + d₂ ≥ 2σ* − 1 and d₁, d₂ > λ give d₁⁻³ + d₂⁻³ ≤ λ⁻³ + (2σ* − 1 − λ)⁻³ = 2J.
- A zero on the critical line contributes ≤ (σ* − ½)⁻³ ≤ J, by Jensen.
- The reflections of the N disc zeros are N distinct strip zeros, each contributing ≤ (2σ* − 1 − λ)⁻³.
- With |S₁| = M_count − 2N this gives Σ_{strip, outside} ≤ J·M_count − N/λ³.

Since C(0, ν) ≤ C(−1, ν), the disc terms are absorbed. Total error ≤ C(−1, ν)η³(J·M_count + S_far). This is `zero_err` (l.182–191).
- `sig1 = sig.lower()` only enlarges (2σ₁ − 1 − λ)⁻³. That is valid, because the subtracted term 2J − (2σ* − 1 − λ)⁻³ stays ≥ λ⁻³.

**Counting functions.**
- M_count ≤ (1/π)log(T/2π) + 2R₀(T) + 1e-9, by Rosser.
- S_far = Σ_{|γ−T|>1}|γ−T|⁻³ ≤ (1/2π)log(T/2π) + 4R₀(T) + 1e-9.
  - Each side gives (1/4π)log(T/2π) from the main part.
  - Each side gives 2R₀ from the R-part: the boundary term ≤ R₀(T ± 1), plus 3∫R₀x⁻⁴ ≤ R₀ + O(1/T).
- The thesis states Lemma 3.12 and (3.33) for T ≥ e^56.5. The proofs only need the O(log T/T) slack terms to be < 1e-10, which holds for T ≥ e^30. **COSMETIC:** state this in the write-up.

**Cot sum (Lemma 3.15).**
- Zeros with σ* − λ ≤ β < σ* give Re cot ≥ 0.
- Zeros with β ≥ σ* lie at |γ − kt| > T₀, because the window is zero-free. Each contributes O(e^{−π·10¹⁰/λ}).
- This uses only |σ* − β| ≤ y < η.

### 2.4 E-terms (Kadiri's error term)

For s with Re s − ½ ≥ x₀:

  |E(s)| ≤ (1/2π)∫|W₀((s − ½ − iy)/η)|·|Re ψ(¼ + iy/2)| dy + |W₀(s/η)|.

- Ford's bound applies with ν = r = x₀/η. Here r is at least ≈ 80 > tan θ = 2.104.
- I use log(|T + u|/2 + 4) ≤ log(T/2 + 4) + |u|/(T + 8), together with ∫(x₀² + u²)^{−3/2} du = 2/x₀² and ∫|u|(x₀² + u²)^{−3/2} du = 2/x₀.
- This gives exactly `E_bound` (l.140–148). |W₀(s/η)| ≤ Cη³/x₀³ is very conservative but valid.

**Digamma lemma** (it is only sample-checked in `check_core`, so here is a proof). Let z = ¼ + iτ and w = z + 1.
- Binet's second formula with φ(t) = 1/(e^t − 1) − 1/t + ½ ∈ [0, t/12] gives |ψ(w) − log w + 1/(2w)| ≤ 1/(12(Re w)²) = 0.0533.
- With ψ(z) = ψ(w) − 1/z, |Re(1/(2w))| ≤ 0.4 and |Re(1/z)| = ¼/(1/16 + τ²):

  |Re ψ(z)| ≤ log(τ + 5/4) + 0.4533 + ¼/(1/16 + τ²),

  using log|w| ≥ log(5/4) > 0.
- This is ≤ log(τ + 4) + 10/3 for all τ ≥ 0. The worst case is τ = 0: 4.453 ≤ 4.497. With τ = |y|/2 this is the lemma.
- A dense check gives minimum slack 0.49, at y = 0 (check 3).

### 2.5 The k = 0 term

- Q(σ*) = f(0)(ψ(σ*/2 + 1) − log π)/2 + F(σ* − 1) − Σ_ρ Re F(σ* − ρ) + E(σ*), from Kadiri; the Hadamard coefficient was verified numerically (check 2).
- Since ψ is increasing on (1, ∞) and σ* < 1, ψ(σ*/2 + 1) < ψ(3/2) = 2 − γ − 2log 2. So the Γ-part is ≤ −f(0)κ, with κ = (log π − ψ(3/2))/2 = 0.554120 (`KAPPA_Q`).
- Using η_max here is legitimate only because B − κ > 0. It is, since B ≈ 30–60.

### 2.6 Negligible terms (`tiny` = 1e-9 η_max)

The terms covered are:
- Lemma 3.15 far zeros: ≤ e^{−6·10¹⁰}.
- Lemma 3.18: Re F*(s_k − 1) = Re F₀(s_k − 1) + (πf(0)/2λ)·Re cot(·). The second part is < 0, and |F₀| ≤ 47η³/t³ < 10⁻³⁰η. (As F7 noted, the thesis's own proof of Lemma 3.18 drops a term.)
- Lemma 3.20, |γ| > 3·10¹²:
  - the w(0)η·Re(1/(σ* − ρ)) part ≤ ηw(0)·y·Σ_{|γ|>H}γ⁻² ≈ 10⁻¹³η;
  - the F₀ part ≤ 47η³·log H/H² ≈ 10⁻²³η.
- Zeros with |γ| ≤ H are on the critical line, so Re F(σ* − ρ) ≥ 0 by Heath-Brown.

Total ≪ 10⁻⁹η. ✓

### 2.7 The ρ₀ term and the gain G

- F*(σ* − β₀) = F(σ* − β₀) − f(0)(π/2λ)(1/u − cot u), with u = π(η − y)/(2λ) ≤ 1.
- 1/u − cot u ≤ 0.36u on (0, 1], since (1/u − cot u)/u is increasing and equals 1 − cot 1 = 0.3579 at u = 1. This gives `loss351`, with the sign of the thesis's F7 slip corrected.
- a₁F(σ* − β₀) − a₀F(σ* − 1) = a₁W(1 − µ) − a₀W(−µ) = ∫e^{µu}(a₁e^{−u} − a₀)w(u) du = G(µ), with µ = y/η.

**Final inequality.**

  G(µ) ≤ η w₀ (B − a₀κ) + zero_err + Σ_k a_k|E(s_k)| + a₀|E(σ*)| + loss351 + tiny.

This is term-for-term `Psi_eta` (l.207). There is no sign or factor discrepancy.

---

## 3. Induction and window logic (brief item 1)

### 3.1 Base case

- From 21.233 (an open region): no zeros with β ≥ 1 − S₀·ℓ/Z_i, because S₀/Z_i < 1/21.233.
  - With the REPORT's S₀ = 0.85 this needs Z_i > 18.048.
  - With the current code's S₀ = 0.5 it needs Z_i > 10.617.
  - Both hold (min 18.593).
- S₀ enters the certificate only through the negligible factors (1 ± O(ε/S₀)).

### 3.2 Step H(s) ⇒ H(s+ε)

A zero ρ₀ violating H(s+ε) has η ∈ (sAℓ(t), (s+ε)Aℓ(t)]. Here A is the constant of ρ₀'s own band, and that band's closed cell cover contains v.

**Zero-free window.** For u ∈ [t − T₀, 16t + T₀]:
- **Bands (30, 300].** H(s) gives β < 1 − sA(log u)ℓ(u). Also A(log u) ≥ A_w by the definition of Z_w, and ℓ(u) ≥ ℓ(16t + T₀), because ℓ is decreasing for log u > e and log u ≥ 29.999. Hence β < σ*. Strict, as required by Lemmas 3.15/3.16.
- **log u ≤ 30 (MTY).** 1/(5.558691 log u) = ℓ(u)/(5.558691·loglog u) ≥ ℓ(u)/(5.558691·log 30) = ℓ(u)/18.906 ≥ s·A_w·ℓ(16t + T₀), since Z_w ≥ 18.906. Hence β < σ*.
- **log u > 300 (Yang, open region).** β ≤ 1 − ℓ(u)/21.233 < 1 − s·ℓ(16t + T₀)/Z_w = σ*. This uses Z_w ≥ 21.233 and s ≤ 1 − ε < 1, so it is strict.

**What the thesis needs.** Lemmas 3.15/3.16 only need the union of [kt − T₀, kt + T₀], k = 1..16. The code demands the whole interval, which is conservative. Zeros off the critical line at low heights (e.g. 3·10¹² < |γ| < t − T₀) affect only the k = 0 sum, and only negligibly (§2.6). So no zero-free region is needed there.

**Window code** (`zw_window`):
- lo = va + log(1 − T₀e^{−va}) and hi = vb + log(16 + T₀e^{−va}) enclose the true window, since both endpoints increase in v and e^{−va} ≥ e^{−vb}.
- The ±1e-9 slack dominates float error.
- The ≥/≤ tests over-include half-open bands.
- `rerun_cert.py` compared Z_w with an exact 50-digit window maximum for all 67,500 cells: zero violations.

### 3.3 Uniform-A leftovers from the thesis (all removed)

| Thesis item | How the code handles it |
|---|---|
| ν = λ₁/η₁ | per cell ν = λ/η_max |
| σ₁ in Lemma 3.13 | σ.lower() of the cell |
| µ₀ | per-cell µ_low |
| η ≤ η₁ | per-cell η_max |
| Lemma 3.18's η/2 < 1 − σ* < η | ⇔ ½ < µ < 1. Here µ_low ∈ [0.8807, 0.9924] (every 10th cell sampled); µ < 1 holds strictly, because A_w ≤ A and ℓ(16t + T₀) < ℓ(t) |
| Lemma 3.20 | only enters `tiny` |
| 0.71 log T, 18.6, 2.56, 0.75 | not used; the formulas are evaluated directly |

### 3.4 Is s = 1 the worst case?

Write y_s = sA_wℓ_K and η_s ≤ (s+ε)Aℓ. As s decreases:

| Quantity | Direction | Effect |
|---|---|---|
| λ = 1 − y − σ_n | increases | — |
| 2σ* − 1 − λ = σ_n − y | increases | J decreases |
| x = 1 − 2y − σ_n | increases | γx − log x decreases |
| B | positive bracket/(2λ), plus a decreasing term | decreases |
| ν = λ/η | increases | C(−1, ν) decreases (C is decreasing in r: checked) |
| x₀ = ½ − y | increases | the E-bound decreases |
| u = π(η − y)/(2λ) | decreases | loss351 decreases |
| µ_s | µ_s ≥ (A_w/A)(ℓ_K/ℓ)·s/(s+ε) ≥ µ_low (independent of s) | — |
| Constraints λ < ½, λ > y, σ* > ¾ | become easier | — |

Every term of ηΨ is increasing in η (and B − κ > 0). So evaluating at y₁ = A_wℓ_K and η_max ≥ Aℓ ≥ η_s bounds every s ∈ [S₀, 1 − ε]. ✓

The factor (1 + 2ε/S₀) in η_max is harmless over-allowance.

---

## 4. λ = σ* − σ_n and the exceptional set (brief item 2)

- **Lemma 3.7 on σ = ½.** Applicable as stated: the hypothesis is ½ ≤ σ ≤ 1 − t⁻¹. Its proof uses only |s − 1| ≥ ½ on the middle range and the pointwise bound elsewhere. log|ζ| = −∞ at zeros on the line only helps an upper bound.
- **Lemma 3.4 is not applied at λ itself** (it may be exceptional, for n = 3 certainly so if zeros are on the line). Instead:
  - Take non-exceptional λ_j ↑ λ with λ_j > y. For n = 3, λ_j < σ* − ½, which is exactly what the pairing in §2.3 needs.
  - **Left line.** As j → ∞, the points σ* − λ_j + i(kt + 2λ_j u/π) converge to ½ + i(kt + 2λu/π). log|ζ| is subharmonic, hence upper semicontinuous on ℂ, so limsup ≤ log|ζ(limit)| pointwise.
  - **Reverse Fatou** applies with the integrable majorant log(C(2 + |kt| + |u|))·sech²u. This comes from the convexity bound, uniformly for Re ∈ [½, ½ + δ₀].
  - **Right line.** Bounded by (3.19) at each j; continuous in λ_j.
  - **All other bounds** (J(λ_j), C(−1, λ_j/η), loss351, the cot sums) are continuous in λ_j and valid at each j.
- Hence 0 ≤ lim sup_j(RHS_j) ≤ the λ-version. **Sound.**
- The same argument covers n ≥ 4 if σ_n carries zeros.
- The thesis's own "take λ_j ↑ λ*" (p. 77) is the same device.
- This step is now written out in REPORT.md §4.2, which was added during the review; it matches the argument here.

---

## 5. Numerical checks of the analytic inputs (`check_formulas.py` → `check_formulas_output.txt`)

1. **Ford's detector (thesis (3.4)) for f = ζ.** At s = 0.9 + 30i (λ = 0.45 and λ = 0.30) and s = 0.95 + 50i (λ = 0.41), −Re ζ′/ζ equals the right-hand side to **1e-20**. This confirms the 1/(4λ) prefactor and the 2λiu/π scaling, which fix B = (1/2λ)[…].
2. **Explicit formula (3.3)** with E(s) as in thesis Lemma 3.4, f(u) = 0.3·w(0.3u), s = 0.9:
   - LHS 1.67193490679, RHS 1.67193491051. The difference, 4e-9, is within the zero-sum tail of ≤ 2e-6.
   - The Lemma 2.6 form agrees after its O(1/γ) tail (≈ 0.0017) is accounted for. This confirms the Γ-term (ψ(σ/2 + 1) − log π)/2 behind the Q-gain.
   - At complex s = 0.9 + 30i: LHS −0.48649988365, RHS −0.48649987987 (diff 3.8e-9). This is the form used for every k ≥ 1.
3. **Digamma lemma:** min slack 0.4922 over y ∈ [0, 200] (step 0.01) and y = 2·10³…2·10³⁹, attained at y = 0. This agrees with the proof in §2.4.
4. **Ford's W₀ bound at the parameters used:** max |z³W₀(z)|/C(ν, r) on boundary and far points.

   | (ν, r) | ratio |
   |---|---|
   | (−1, 40) | 0.894 |
   | (−1, 60) | 0.961 |
   | (−1, 90) | 0.961 |
   | (−1, 160) | 0.985 |
   | (0, 60) | 0.960 |

   - W₀ was computed by quadrature, and by the integration-by-parts series for large |z|; at the same points (|z| = 90…300) the two agree to ≤ 1e-10.
   - The bound is **tight**. Asymptotically z³W₀ = w″(0) + [w‴(0) − e^{−zd}w‴(d)]/z + O(z⁻²), with w″(0) = −45.868 and w‴(0) = −w‴(d) = 106.48. On Re z = −1 the oscillating part reaches ±311/|z|, while C(−1, r) − |w″(0)| ≈ 2.7 at r = 160.
   - It still holds, and it is Ford's published lemma. For the actual ν ≈ 138–282 the dense scan is in `ford_dense_output.txt`: 

   | r | max ratio |
   |---|---|
   | 80 | 0.9676 |
   | 100 | 0.9760 |
   | 140 | 0.9827 |
   | 200 | 0.9882 |
   | 282 | 0.9917 |

   The maximum lies just above |z| = r; the scan steps Im z by r/2000. The bound holds with < 1% slack at the largest ν used. In the certificate Re z ≥ −µ ≥ −0.9924, so the true situation is slightly better than ν = −1.
5. **(3.42) on the half disc:** for (λ, η) = (0.494, 0.006), min Re F* = −7.98e-5 ≥ −C(0, ν)η³/λ³ = −8.71e-5. For (0.27, 0.0016), −9.41e-6 ≥ −9.82e-6. ✓

I read the author's `check_core.py` output (`../check_core_output.txt`) but did not re-run it. Checks 1–5 above cover its sample checks more densely.

---

## 6. Code audit (brief item 4)

**Cell coverage.**
- Band edges are exact floats. Cells are consecutive float edges, `edges[0] = a`, `edges[-1] = b`, and bisection shares midpoints.
- `v = arb(mid, rad)` contains both ends. Tested: `contains(va)` and `contains(vb)` are both True for [130.123, 130.127].
- Every one of the 67,500 cells passed at the initial width 0.004. No bisection and no bump rounds occurred: `cert_run_output.txt` has only round 0.

**Rounding directions.**

| Expression | Why it is conservative |
|---|---|
| `nu_l = nu.lower()` | Ford's bound holds for any r ≤ \|z\|; C is also decreasing in r |
| `sig1 = sig.lower()` | enlarges J |
| `x0 = (sig − ½).lower()` | E_bound is decreasing in x₀; Ford is valid for smaller ν, r |
| `E_coef(x0, eta_max.upper())` | ν smaller |
| `mu_low.lower()` with factor (1 − 4ε/S₀) | lower bound for µ |
| `Psi_eta.upper()` vs `G.lower()` | correct comparison directions |
| `Zw` from `arb(Zs).upper()` | A_w lower bound |
| `Z` as `arb('18.919')` | ball containing the decimal |

All conservative. ✓

**G table.**
- G′ > 0 is certified on [0.85, 1] (150 µ-balls; acb.integral, entire integrand, so ignoring the `analytic` flag is safe).
- The lookup uses grid g = (⌊10⁴m⌋ − 1)/10⁴ with `assert g.upper() ≤ mu_low.lower()`.
- G(g) is a ball enclosure, and `.lower()` is taken. ✓
- Edge case (COSMETIC, never triggered): if mu_low ∈ [0.85, 0.8501), then g = 0.8499 lies outside the certified-monotone interval. The observed min µ_low is 0.8808.

**Ford constants.** `C_ford` uses Ford's corrected c₀ = 1/(sin θ cos³θ), so F5 is fixed. It asserts r > tan θ. ν = −1 is valid for all off-disc zeros, since Re((s_k − ρ)/η) ≥ −µ > −1.

**Reproduction.** `rerun_cert.py` re-ran `certify_band` for all 161 bands in memory. The cell counts and min-margins are identical to `cert_summary.json` (to 1e-12), all bands are ok, and there are 0 window violations. `profile_design.json`, `zfr_local.csv` and `cert_summary.json` agree band-by-band.

**Independent re-implementation** (`indep_check.py` → `indep_check_output.txt`).
- Written from §2 in mpmath. It uses the exact 1/u − cot u and the exact J.
- Test heights: v ∈ {30.0005, 31, 45, 60, 80, 95.5, 100, 129.9, 130, 130.3, 130.6, 131, 160, 216, 250, 296.9, 297.2, 297.5, 299, 300}.
- At these heights `cell_terms`' Ψη exceeds the independent value by 1e-7 to 5.4e-6. The code is always the larger, as it should be.
- The whole difference is the code's majorant 0.36u for 1/u − cot u ≈ u/3 in `loss351`. With the same majorant the two agree to ≤ 3e-11 (v = 30.0005, 31, 60, 95.5, 216, 299).
- Dense point scan (Δv = 0.05, 5401 points): margin > 0 everywhere. The worst relative margin is 2.41e-4 (v = 92, n = 3). For n = 4 the worst is 2.43e-4 (v = 294.25).

**Thinnest certified margin.** Band (130, 131], minrel 1.5e-6, in the cell where the code switches between lines n = 3 and n = 4. It is rigorous, but any change to inputs would break it first. COSMETIC.

---

## 7. Thesis findings F1–F7 (brief item 5)

| Finding | Status in the new code |
|---|---|
| F1 (Lemma 3.8 arithmetic) | **Not inherited.** B is computed directly; Lemma 3.8's E(t) is not used. c(v) matches the audit's independent "optimised λ" value (3.3846 vs 3.3839 at v = 60; 3.4411 vs 3.4408 at 95.5; 3.4981 vs 3.4946 at 129.9) |
| F2 (circularity with Lemma 2.1) | **Not inherited.** Refereed MTY (5.558691) is used below 30; thesis Lemma 2.1 is not used |
| F3 (Lemma 3.6 range) | Not applicable (no Phragmén–Lindelöf) |
| F4 (Lemma 3.9 sign) | Not applicable |
| F5 (Ford c₀ typo) | Fixed: Ford's c₀ |
| F6 (Lemma 2.7 outside hypotheses) | Not applicable: own E-bound (§2.4) |
| F7 | (3.51) uses the correct u = π(σ* − β₀)/(2λ); C₄ is replaced by the exact G integral; the Lemma 3.18 and 3.20 omissions are covered by `tiny` (§2.6); Lemmas 3.11/(3.27)/(3.32) are not used |

---

## 8. Why the constants beat the audit's per-height table by ≈1%

At v = 60 the band constant is 19.043. The thesis audit's "local constant" was 19.26. The gap needs explaining, because an unexplained gain could hide an error.

- **The main coefficient c is the same in both.**
- **The audit's table divides by a uniform worst case.** Its denominator is I(µ₀) − loss − C3max, with C3max = +0.0045, the sup over t (attained at log t ≈ 1144).
- **Locally, the net error is negative.** Net error = −Q-gain + zero sums + E + loss351:

| v | c = Bℓ | Q-gain | zero sums | E | net error | G(µ_low) | implied Z | band Z |
|---|---|---|---|---|---|---|---|---|
| 60 | 3.38458 | −0.010553 | 0.003171 | 0.000709 | **−0.006659** | 0.938182 | 19.0387 | 19.043 |
| 95.5 | 3.44112 | −0.007261 | 0.001513 | 0.000341 | **−0.005403** | 0.939635 | 19.3527 | 19.362 |
| 129.9 | 3.49810 | −0.005607 | 0.000909 | 0.000206 | **−0.004490** | 0.940523 | 19.6737 | 19.680 |
| 216 | 3.34254 | −0.003891 | 0.001284 | 0.000110 | **−0.002496** | 0.941334 | 18.8223 | 18.836 |
| 299 | 3.29452 | −0.002980 | 0.000776 | 0.000067 | **−0.002125** | 0.927408 (µ = 0.881) | 18.8373 | 18.845 |

- The Q-gain 2.945η outweighs the local zero-sum error. The thesis's uniform zero-sum bound 18.6·log T is ≈ 2.7× the local value at v = 60, because it uses λ* = 0.278 from near e^216.
- The implied Z = (w₀c + ℓ·net/η)/G reproduces every band constant to < 0.015.
- The jump at (297, 300] (Z = 18.845 vs 18.603) is explained by the window reaching above 300. There Z_w = 21.233 and µ drops to 0.881.

---

## 9. Issues found

| # | Severity | Issue | Evidence / fix |
|---|---|---|---|
| 1 | FIXABLE → **resolved during review** | The proof write-up was missing when the review started; `REPORT.md` was added at 11:59 | REPORT.md checked in §10; its remaining slips are cosmetic (items 9–13) |
| 2 | COSMETIC | Thesis Lemma 3.12 and (3.33) are stated for T ≥ e^56.5 but applied from T ≥ e^30 | the proofs' slack terms are O(log T/T) < 1e-10 at e^30; add one sentence |
| 3 | COSMETIC | Lemma 3.7 implicitly needs log(X T^Y (log T)^Z) ≥ 0 | true for T ≥ e^30 (≥ 7.9); mention |
| 4 | COSMETIC | `GTable.lower` can pick g = 0.8499 < 0.85, outside the certified-increasing range | not triggered (min µ_low = 0.8808); start `check_increasing` at 0.849 or clamp |
| 5 | COSMETIC | Thin certified margin, 1.5e-6 relative, in band (130, 131] at the n = 3/4 switch | rigorous; if inputs change, bump Z(130, 131] by 0.001 |
| 6 | COSMETIC | Brief states Z_i ≥ 18.56; the file has 18.593 | — |
| 7 | COSMETIC | `check_core.py` checks the digamma bound at 12 points and Ford's bound at 90 points only. Ford's C(−1, r) is tight (ratio 0.992 at r = 282) | proof of the digamma bound in §2.4; denser checks in `check_formulas.py` and `ford_dense.py`. Ford's lemma is published, so tightness alone is not a defect |
| 8 | COSMETIC | Unused `H_RH` constant; the docstring says "A_w = min of A" while code passes Z_w = max Z | consistent, just wording |
| 9 | COSMETIC | REPORT §2 says S₀ = 0.85 (base case 18.593 > 18.048); `zl_core.S0` is now 0.5 | both valid; make them agree |
| 10 | COSMETIC | REPORT §5.2 says the bands on (30, ≈32.5] are "genuinely better than MTY". MTY's region equals Z_eff(v) = 5.558691·log v, which is < 18.919 for v < e^{18.919/5.558691} = 30.069 | on (30, 30.069) the certified band is (slightly) weaker than MTY. It is still true, but the claim is false there |
| 11 | COSMETIC | REPORT §1 "re-run 24 s"; the current run takes 45 s | — |
| 12 | COSMETIC | REPORT §8.1 R4 / §6 quote the W₀ check as "max ratio 0.98"; the dense scan here reaches 0.9917 at r = 282 | still < 1; the bound is Ford's published lemma, and it is tight |
| 13 | COSMETIC | REPORT §9 still contains the placeholder `REVIEW_STATUS` | fill in |

**Nothing FATAL was found.** In particular, all of the following are correct:
- the window/induction logic;
- the strictness and ℓ-monotonicity;
- the s = 1 worst case;
- the λ = σ* − ½ limit;
- the signs of every term in the final inequality;
- the coverage, rounding and G-table logic of the code.

---

## 10. Review of REPORT.md (added during the review)

I checked each argument of REPORT.md against §2–§4 of this review.

| REPORT section | Verdict |
|---|---|
| §2 Claim W | correct; identical to §3.2 here, and strictness above 300 is now also enforced by the +10⁻²⁰ |
| §2 µ bounds | correct |
| §2 condition (C) | correct |
| §3 table S1–S13 | consistent with §2 here |
| §4.1 (3.19) proof | correct |
| §4.1 monotonicity in y | correct |
| §4.2 limit argument | correct. It uses continuity of log\|ζ\| into [−∞, ∞), which is stronger than the u.s.c. used here, and the majorant from \|ζ(s)\| ≤ C(1 + \|Im s\|) on Re s ≥ ½, \|s − 1\| ≥ 0.4 |
| §4.3 zero sums | correct. The corrected bookkeeping "M = \|S₁\| + 2N" is exactly the one derived in §2.3 here. The cot bound \|Re cot(x+iy)\| ≤ 8\|x\|e^{−2\|y\|} is valid for \|y\| ≥ 1 |
| §4.5 digamma proof | correct: Binet at Re w = ¼ gives ∫(t/12)e^{−t/4} = 4/3; 1/(2\|w\|) ≤ 2; \|log\|w\|\| ≤ log(\|y\|/2 + 4) since \|w\| ≥ ¼ |
| §4.5 E-bound | matches §2.4 |
| §4.6 | correct; Σ_{\|γ\|>H}γ⁻² ≤ 4(log H + 1)/H is generous |
| §4.7 | correct |
| §8.1 R1–R7 (steps "taken from the thesis") | checked independently here, numerically: R1 and R2 against ζ to 4e-9 and 1e-20 (§5 checks 1–2); R4 by a dense scan (§5 check 4); R3 re-read (its I₂ step implicitly needs log(XT^Y log T) ≥ 0, which holds) |

Cosmetic slips are items 9–13 of §9.

---

## 11. Files (this folder)

| File | Purpose | Run time |
|---|---|---|
| `indep_check.py` → `indep_check_output.txt` | independent mpmath re-implementation; comparison with `cell_terms` at 20 heights; dense point scan of margins | ~1.5 min |
| `rerun_cert.py` → `rerun_cert_output.txt` | in-memory re-run of the whole certification; exact-window cross-check of `zw_window` for all cells; min µ_low | ~5 min |
| `check_formulas.py` → `check_formulas_output.txt` | Ford detector and Kadiri explicit formula vs ζ (400 zeros); digamma lemma; Ford W₀ bound at the used (ν, r); (3.42) | ~25 min |
| `check_formulas_345.py` → `check_formulas_345_output.txt` | checks 3–5 alone (identical code) | ~2 min |
| `ford_dense.py` → `ford_dense_output.txt` | dense scan of Ford's bound on Re z = −1, r ∈ {80, 100, 140, 200, 282} | ~1 min |
