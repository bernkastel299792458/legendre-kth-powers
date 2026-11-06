# Checking Lee's zero-density and zero-counting inputs against the original sources

*This report was produced by a verification sub-agent on 2026-11-06 and saved by the main session. The main session re-read Johnston–Yang (2023) Lemma 2.6 and Table 3 itself and confirms the values quoted in §1 below.*

**Scope.** E. S. Lee, arXiv:2602.14340v2 (3 Mar 2026), quotes four inputs. This report checks each against the paper it comes from: I-KLN (eq. 2.7), I-NT (eqs. 2.4–2.5), I-HR (the Riemann height) and I-BEL (eq. 2.6 / Table 2).

**Method.**
- Each original was downloaded from arXiv into `sources_density/` and extracted with `pdftotext -enc UTF-8 -layout`.
- Page numbers are PDF pages of the arXiv version named.
- No published journal version could be read (ScienceDirect and ams.org returned HTTP 403 or a bot check). Every "confirmed" refers to the arXiv version named.

| Source | arXiv version read | Published as |
|---|---|---|
| Kadiri–Lumley–Ng (KLN) | 2101.12263v1 | JMAA 465 (2018) 22–46 |
| Johnston–Yang (JY) | 2204.01980v2 | JMAA 527 (2023) 127460 |
| Bellotti–Wong (BW) | 2412.15470 v1, v2 | Math. Comp., doi:10.1090/mcom/4133 |
| Platt–Trudgian (PT) | 2004.09765v1 | Bull. LMS 53 (2021) 792–797 |
| Bellotti (log-free) | 2405.12545 v1, v2 | JNT 269 (2025) 37–77 |

## Summary

| Input | Status | Finding |
|---|---|---|
| **I-KLN**, Lee (2.7) | **DISCREPANCY** | 17.253 and 5.663 are the largest A (σ = 0.99) and largest B (σ = 0.60) in KLN's original Table 1. That table is grid-only, uses the RH height 3.06·10¹⁰, and relies on Hiary's a₁ = 0.63. JY call Hiary's bound "unreliable" and recompute (a₁ = 0.77, H₀ = H_R) **for σ ∈ [0.98, 1) only**. Their C₁ exceeds 17.253 for σ ≥ 0.998 and reaches **17.418** as σ → 1. For 0.6 < σ < 0.98 nobody has recomputed KLN's constants without Hiary's flawed bound. |
| **I-NT**, Lee (2.4)–(2.5) | **CONFIRMED WITH CAVEAT** | BW v2 Thm 1.1: \|N(T) − (T/2π)log(T/2πe)\| ≤ 0.10076 log T + 0.24460 log log T + 8.08344 for T ≥ e. Lee's extra "−7/8" is harmless for upper bounds. N(T) ≤ T log T/(2π) holds for all T ≥ 21.12, with a margin of about 1.36·10¹² at T = H_R. |
| **I-HR**, Platt–Trudgian | **CONFIRMED** | Theorem 1: RH holds up to 3 000 175 332 800, i.e. for the lowest 12 363 153 437 138 zeros. Simplicity of these zeros is not stated, and is not needed. |
| **I-BEL**, Bellotti Thm 1.1 | **CONFIRMED WITH CAVEAT** | Hypotheses: T ∈ (T₀, T₁], σ ∈ [α₀, 1], N(σ,T) counts 0 < γ < T with σ < β < 1. Lee's 17 rows match arXiv **v2**, not v1. Bellotti's proof cites no thesis; its zero-free regions all come from published papers. One input, Ramaré–Zuniga Alterman (arXiv:2405.12662, Funct. Approx. 74 (2026)), was a preprint at the time. The published JNT Table 2 was not accessible. |

## 1. [I-KLN] DISCREPANCY

- **KLN Lemma 4.14 (p. 20):** H₀ = 3.0610046·10¹⁰, T ≥ H₀, σ > 1/2 + d/log H₀. The bound has the form (C₁/2πd)(log kT)^{2σ}(log T)^{5−4σ}T^{8(1−σ)/3} + (C₂/2πd)(log T)². KLN Table 1 (p. 23) lists values at σ₀ = 0.60, 0.65, …, 0.99 only:
  - row 0.60: A = 2.177, B = 5.663;
  - row 0.99: A = 17.253, B = 2.446.

  Its Lemma 3.2 uses Hiary's a₁ = 0.63.
- **Johnston–Yang** (JMAA 527, 2023), §1.4: Hiary's result is "unreliable". JY eq. (2.2):

  N(σ,T) ≤ C₁(σ) T^{8(1−σ)/3} log^{5−2σ} T + C₂(σ) log² T.

  Lemma 2.6: "For corresponding values of σ, C₁(σ) and C₂(σ) in Table 3 (see Appendix B), the bound (2.2) holds."
- **JY Table 3** (H₀ = 3 000 175 332 800, k = 1):

  | σ | 0.980 | 0.990 | 0.997 | 0.998 | 0.999 | → 1 |
  |---|---|---|---|---|---|---|
  | C₁ | 16.281 | 16.848 | 17.248 | 17.305 | 17.362 | 17.418 |
  | C₂ | 2.231 | 2.150 | 2.094 | 2.086 | 2.077 | 2.069 |

- **JY p. 9:** "if σ₁ < σ < σ₂, then one can take C₁(σ₂) and C₂(σ₁) … as C₁ and C₂ are respectively increasing and decreasing in σ".
- **Consequence:** the sources do not establish Lee's (2.7) for σ ∈ (0.997, 1), nor anywhere in (0.6, 0.98).
- **Fix adopted in this project:** use JY's values for σ ∈ [0.98, 1), namely C₁ ≤ 17.418 and C₂ ≤ 2.231, and apply the trivial bound to zeros with β < 0.98 (σ₁ = 0.98). For k = 67 the trivial term still decays, because 1 − σ₁ = 0.02 > 1/67.

## 2. [I-NT] CONFIRMED WITH CAVEAT
See the summary. Only the upper bound N(T) ≤ T log T/(2π) for T ≥ H_R is used.

## 3. [I-HR] CONFIRMED
Platt–Trudgian, Theorem 1.

## 4. [I-BEL] CONFIRMED WITH CAVEAT

- **Statement.** v2 Theorem 1.1 (p. 2): "For every T ∈ (T₀,T₁] and σ ∈ [α₀,1] as displayed in Table 2 … N(σ,T) ≤ C T^{B(1−σ)}".
- **Last range.** The final range (exp(481958), exp(6.7·10¹²)], with 1.62·10¹¹ T^{1.448(1−σ)} for σ ∈ [0.985, 1], is stated in the text (p. 27).
- **Versions.**
  - v1 differs from v2, e.g. the (e⁸⁰, e⁹⁰] row: v1 has C = 296669.03, B = 5.197; v2 has C = 370655.73, B = 5.216.
  - The change comes from switching to the Ramaré–Zuniga Alterman constants.
  - Lee's printed values are the v2 values. The rows with log T < 80, used in this project, were checked separately against the v2 PDF and LaTeX source.
- **Zero-free regions used in Bellotti's proof** (all published):

  | Height | Region |
  |---|---|
  | ≤ e^{46.2} | Mossinghoff–Trudgian–Yang, 5.558691 |
  | up to e^{170.2} | Ford-type region via Hiary–Patel–Yang |
  | up to e^{481958} | Yang, 21.233 |
  | beyond | Bellotti, Korobov–Vinogradov 53.989 |

- **Other ζ bounds.** Hiary's 1.461 is used only for |t| ≤ 3 (rechecked numerically: max |ζ(1/2+it)| on [0, 3] ≈ 1.46035). Also used: Hiary–Patel–Yang's 0.618, and Patel–Yang's 66.7 t^{27/164}.
