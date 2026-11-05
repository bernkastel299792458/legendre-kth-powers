# Review checklist (v4) — interim results k ≥ 70 (high confidence) and k ≥ 74 (refereed inputs only)

> **v4 note.** The earlier k ≥ 67 claim is **withdrawn**: the PhD-thesis proof of the Littlewood constant 19.62 contains an arithmetic error (`zfr_audit/thesis_19.62/REPORT.md`).
> - Items A1 (19.62) and everything specific to the k = 67 certificates no longer bear on the main results.
> - Theorem 1 (k ≥ 70) depends on 4.896 (A2), which was audited and verified (`zfr_audit/bty_4.896/REPORT.md`).
> - Theorem 2 (k ≥ 74) uses only refereed inputs.
> - Remaining high-priority items:
>   1. A2: an independent expert check of BTY Theorem 1, needed for Theorem 1 only;
>   2. A5: the printed JNT Bellotti table;
>   3. A10 / B8: Lemma 4;
>   4. B5: Lemma T for k₀ = 70, 74;
>   5. C6: a rigorous second implementation of δ_S.

## Status after two independent AI reviews of v2 (GPT, Claude; 2026-11-06)

Full texts are in `../review/`; responses are in `../review/response_to_reviews_2026-11-06.md`.

| ID | Reviews' verdict on v2 | v3 status |
|---|---|---|
| A1 (19.62) | UNSURE | **Audit: the proof as written fails** (Lemma 3.8 arithmetic error) → k = 67 withdrawn; 19.62 is no longer used |
| A2 (4.896) | UNSURE | **Audit: verified** after correcting 15 non-fatal issues; it depends only on published results; needed only for k ≥ 70 |
| A5 (Bellotti table) | ISSUE: only arXiv v2 compared; margins sensitive (C × 1.05 fails) | **Still open**: needs the printed JNT table. Tolerances are given in manuscript §11. |
| A6 (CHJ II, common T\*) | OK (both reviews) | — |
| A7 (CHL) | OK for the values; ISSUE: upstream KLN dependency not stated | Fixed: (I10) added; the small-T case of KLN Lemma 3.2 is verified in Arb (`kln_lemma32_check.py`) |
| A10 (Lemma 4) | ISSUE: required C², but M = 2 pieces are only C¹ | Fixed: Lemma 4 is proved for F ∈ C¹ with F′ absolutely continuous and F″ ∈ L¹, via ψ₁ (manuscript §7) |
| C2 (Prop. S code) | Minor: the integration start omitted an interval of size about 10⁻³⁷ | Fixed; certificates regenerated and re-checked |
| C5 (certificate endpoints) | Minor: no endpoint assertions | Fixed: `--expect-range` |
| Conventions (γ < T vs ≤ T; λ_K ≥ 1) | Minor | Fixed (manuscript §2, Lemma 5) |
| Literature (KLN/Hiary) | v2 was inaccurate | Fixed (manuscript §3.2) |
| Context (k = 86 published; quasi-RH ⇒ k = 8) | GPT | Added (manuscript §1.1) |
| D (Lean) | OK; the scope must be stated precisely | Statements tightened (manuscript App. B, README, Assembly.lean) |

New items for v3:
- **A11:** (I10), the upstream chain CHL ← KLN ← HPY, plus the Arb check.
- **B8:** the proof of Lemma 4 via ψ₁.
- **C8:** the endpoint padding 2⁻⁴⁰ in `rig_delta`.

---

This checklist is for human experts and AI reviewers. Please report each item as `ID: OK / ISSUE / UNSURE — comment`.
Items are ordered by how much the conclusion depends on them.

Where things are:
- main document: `manuscript.md` (v4);
- source checks: `input_verification/report_*.md`;
- code: `code/`;
- certificates: `certificates/`;
- Lean: `LegendreK67/`.

## A. Inputs from the literature

| ID | Item | Used in | What to check |
|---|---|---|---|
| A1 | (I5) Littlewood constant **19.62** (Yang, PhD thesis, UNSW 2025, Thm 1.2; open access, doi:10.26190/unsworks/31825) | Prop. S range, Prop. H range | **Withdrawn in v4** (proof fails, Lemma 3.8). No longer used by either main theorem; kept for the record. |
| A2 | (I5) classical constant **4.896** (Bellotti–Trudgian–Yang, arXiv:2603.21490, Thm 1; does not use the thesis) | Prop. S range (low heights) | Correctness of Lemma 1 there, and the use of 21.233 above exp(76.463). arXiv only. Needed only for Theorem 1 (k ≥ 70); without it, Theorem 2 (k ≥ 74) still holds. |
| A3 | (I5) VK constant 54.004 (Bellotti, JMAA 536 (2024): the journal states 53.989, arXiv states 54.004) | Lemma T; large heights | Confirm the journal statement. Either value suffices. |
| A4 | (I3) Johnston–Yang Lemma 2.6 / Table 3: C₁ ≤ 17.418 and C₂ ≤ 2.231 for σ ∈ [0.98, 1), T ≥ H₀ = H_R | Props. H, S; Lemma T | The table values; that C₁ increases and C₂ decreases (JY p. 9); the T-range in KLN Lemma 4.14 with H₀ = H_R. |
| A5 | (I4) Bellotti Thm 1.1 / Table 2 (all 39 rows, manuscript App. A) | Props. H, S | The JNT 2025 printed table against arXiv v2; the hypotheses T ∈ (T₀, T₁] and σ ∈ [α₀, 1]. |
| A6 | (I6) Cully-Hugill–Johnston II Thm 1.3 / Cor 3.3 / Table 1 (α = 1/10, ω = 0.2, M = 1.260, x ≥ e^1000) | Prop. H, Lemma T | The **same T\*** for x and x+h; the range max{51, log² x} < T < (x^{1/10} − 2)/4. |
| A7 | (I8) Cully-Hugill–Lee pairs (3.90970·10⁷, 4·10^18) and (2.51949·10^11, e^600), as in arXiv v3 | Lemma 6 | The printed corrigendum (Math. Comp. 93 (2024)) against arXiv v3. |
| A8 | (I7) BKLNW Cor 5.1 (b = 300) and Table 14 | Props. H, S; Lemma T | The constants α₁, α₂ and the derivation of the lower bound. |
| A9 | (I1) H_R = 3 000 175 332 800; (I2) N(T) ≤ T log T/(2π) for T ≥ H_R | everywhere | Values. |
| A10 | (I9) smooth explicit formula (Lemma 4) | Prop. S | The proof in manuscript §7 (F ∈ C¹, F′ absolutely continuous, F″ ∈ L¹, compact support in (1, ∞), via ψ₁); a precise reference for the ψ₁ explicit formula. |

## B. New mathematics

| ID | Item | Where |
|---|---|---|
| B1 | Prop. H: the split σ-integral; σ₁ = 0.98 (KLN used only where (I3) applies); the factor 2 for ±γ; σ\* ≥ α₀; the case σ\* ≥ 1 − η | manuscript §6 |
| B2 | Lemma 3: j-fold integration by parts, no boundary terms, \|ρ(ρ+1)⋯\| ≥ \|γ\|^j | §7 |
| B3 | Prop. S: the Stieltjes step, zeros below H_R, the trivial-zero term, prime powers | §7 |
| B4 | Lemma 5: choice of Φ; monotonicity of the width; Bellotti rows only for log T₀ ≤ v ≤ log T₁; trivial part uses N(t) | §7 |
| B5 | **Lemma T**: every majorant inequality, and the monotonicity conditions (C1)–(C4), (P1)–(P5) | §8, `code/tail.py` |
| B6 | Lemma 6 (lower range from CHL) | §5; Lean `ineq32_of_CHL_range` |
| B7 | Lemma 1: reduction to all k ≥ k₀ (needs k₀ ≥ 62) | §4; Lean `main_of_gap` |

## C. Computation

| ID | Item | Where |
|---|---|---|
| C1 | Formula ↔ code for Prop. H, including the checks of (H1)–(H4) | `code/rigorous_hyb.py: rig_delta` |
| C2 | Formula ↔ code for Prop. S: Abel summation, cells straddling Bellotti rows, v_start, tail | `code/rigorous_smooth.py: rig_delta_smooth_pure, Phi_upper` |
| C3 | R̃_j via Taylor expansions | `rigorous_smooth.py: weight_constants` |
| C4 | Lemma T arithmetic | `code/tail.py` |
| C5 | Run `python code/verify_all.py`; compare with `certificates/verify_all_output.txt` (hashes, contiguity, δ < 1) | |
| C6 | Independent reimplementation (other language or library) | |
| C7 | Sanity: the method must fail for small k (`certificates/sanity_small_k.txt`); try a smaller k with `scan_min_k.py` | |

## D. Lean

| ID | Item |
|---|---|
| D1 | `lake build` succeeds, and `LegendreK67/Audit.lean` lists only `propext`, `Classical.choice`, `Quot.sound`. |
| D2 | The fields of `Hypotheses` (CHL1, CHL2, num1, num2, Hsmooth, Hhyb, Htail) match manuscript §10. |
| D3 | The constants in `Assembly.lean` match the certificates: `main_k70` (L₁ = 2186309/1024, L₂ = 9521, L₃ = 10^8), `main_k74` (L₁ = 578863/256, L₂ = 7343, L₃ = 10^8), and Δ₁, Δ₂. |

## E. Dependence summary for reviewers

- **Thesis-only:** none (19.62 withdrawn in v4).
- **arXiv-only:** BTY, Thm 1 (4.896) — Theorem 1 (k ≥ 70) only; independently audited in `zfr_audit/bty_4.896/`.
- **Partly checked:**
  - published version of Bellotti JNT Table 2 (only arXiv v2 was compared);
  - printed CHL corrigendum (only arXiv v3 was compared);
  - journal text of Bellotti JMAA (53.989 vs 54.004).
- **Everything else:** refereed, and checked against arXiv versions of the sources.
