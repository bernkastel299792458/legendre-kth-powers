# v5 status (2026-11-07 04:30)

## Certified result
> **Update 2026-11-07:** the current certified result is **k ≥ 37** (section "k = 37 certified" below). The k = 36 chain failed (last section). The k ≥ 41 text that follows is the 04:30 record.

**k ≥ 41.** Certificate chain `certs/k41_T1_refereed_own_lemmas*`, independently re-checked in pure Arb by `check5.py`: CHAIN VERIFIED.

| Range of L = log x | Method | Pieces | Max δ |
|---|---|---|---|
| ≤ 1228.607 | CHL lower range | — | — |
| [1228.607, 14023.25] | Prop. S | 3678 | 0.8246 |
| [14023.25, 10¹⁰] | Prop. H | 3628 | 0.9750 |
| ≥ 10¹⁰ | Lemma T (σ₁ = 0.93) | — | — |

**Inputs.** The literature inputs are refereed only: MTY 5.558691, Littlewood 21.233, VK 54.004, Johnston–Yang, CHJ II, BKLNW, CHL, Platt–Trudgian, Bellotti–Wong, HPY. No BTY 4.896, no Chourasiya–Simonič, no RZA.

**Our own lemmas.** Each has passed an independent AI review; none has had a human referee.
- Bellotti §4 counting repair and the λ-box argument.
- Lemmas A, B, B-W, C, D.
- Local classical zero-free constants (Theorem C).
- Local Littlewood zero-free constants, v1 and v2.
- Low-σ KLN-type constants: our own Arb computation of the published KLN18/JY method.

Configuration and SHA256 of every input file: `certs/k41_T1_refereed_own_lemmas.json`.

## Next
- k = 37–40 fail in the mid range, L ≈ 7500–8100: Prop. S has δ = 1.09 at k = 40, and Prop. H only works from L ≈ 11100.
- `rows_mid_v4` (lemma A/D rows on log T ∈ [110, 350]) is the lever for this; the [350, 600] rows are still being computed.

## 2026-11-07: k = 37 certified (T1: refereed inputs + own reviewed lemmas)
- certs/k37_T1_refereed_own_lemmas*: CHAIN VERIFIED by check5.py (independent pure-Arb re-check).
- S: 5518 pieces on [1131463/1024 (1104.944), 38055/2], max delta 0.860166.
- H: 49670 pieces on [38055/2, 1e10], max delta 0.999998 (very thin margin; k = 37 is at the edge of current inputs).
- Lemma T at L3 = 1e10 with sigma_1 = 0.93.
- Inputs: Bellotti rows v2/v3/v4a (refereed status), zfr_local_v2 + classical local bands, kln_low_v1 (JY52).
- The follow-up T2 scan (k = 28-37, +CS/Theorem R) was stopped at the user's request (CPU load); not run.

## 2026-11-07: sampled scans with bel_mid_v4b (scan_v8.txt)
- T1 (refereed + own lemmas, JY52): min k (samples) = 36. k = 35 fails only in the seam, first S fail L = 1093.27, worst S delta 1.354 at L = 1818.27; H works from L = 3969.
- T2 (+ CS preprint, Theorem R b4 = 0.5161, KFORMS JY52,B119): min k (samples) = 36 as well. k = 35 worst S delta 1.331 at L = 1318.27; k = 34 worst 1.691; k = 32 worst 2.735.
- Seam diagnosis (k = 35, L = 1818): the bound is 100% the Bellotti-row part at log T ~ 29-50 (row alpha0 = 0.98, C = 167.09, B = 8.448, eta v = 0.209). KLN is negligible. k = 35 needs a 26-35% reduction there.
- Known levers: exact |w^| kernel instead of R_j/xi^j about 5%; Revers 2602.05614 (zeta on the critical line) under 1%; Chirre-Helfgott 2512.15709 only moves L1 to about 1066. None closes the gap. k = 35 needs new low-height density constants (C e^{B/Z} lower by about 30%).
- H generator v2 (c chosen by minimising the rig5 delta): soundness unchanged, check5 recomputes every piece; it removes the delta ~ 0.99999 artefacts of the v4 pick_c.

## 2026-11-07: where the k = 35 seam constant comes from (float diagnostics, not certified)
Seam row L31902 (log T in [49, 50], alpha0 = 0.98, B = 8.4484, C = 167.09), at log T = 49.36:
C = d4 * d5 * (1/w) * Hn * cf / den = 3.668 * 1.061 * 2.018 * 1.776 * 11.17 / 0.938.
- **cf (Lemma B-W, zeros per box):** #B is an integer, so #B <= floor(bound) is a free, rigorous refinement.
  - Probe (scratch `cf_floor.py`, Arb box bounds, floor of the cell-wise upper bound): at lambda = 14, cf falls from 11.12 to 9.57 = 2 Z (at most 2 zeros per box at delta = nu), so C falls from 165.3 to 142.2 (x0.861).
  - lambda = 14 stays the best box height (C at lambda 12/16/18: 155.5/144.8/174.8). Same factor at log T 36 (x0.89) and 40 (x0.87); log T 28.7 x0.935.
- **d4 (Lemma A):** 3.668, against about 1.3 from the model S ~ 1/2 + ((x - v)L - gamma)/Delta. Most of the loss is the Rankin step on n in [V, X]: any single n^{-eps} majorant loses a factor >= e there, and a positive mixture is no better. Only a different evaluation helps, e.g. an explicit Graham-type bound sum_{n<=N} Psi(n)^2 <= N/Delta (1 + c/Delta) for N >= V.
- **Hn = 1.776** (near part 1.683, far part 0.093) and **den = 0.938**: little room.
- **Budget for k = 35:** floor x0.86, exact |w^| x0.95, total about x0.82. That gives worst S delta about 1.11 (T1), and k = 35 needs x0.74. **A sharper Lemma A (d4 lower by about 10-20%) together with the floor would be enough.** That is the next research lever; it is not started.

## 2026-11-07 20:47: k = 36 chain FAILED (rigorous); certified result stays k = 37
- certs/k36_T1_refereed_own_lemmas: L1 = 1099873/1024 (1074.095); Lemma T at 1e10 OK; H (generator v2) covers [24037/4, 1e10] with 3873 pieces, max delta 0.491294.
- **S fails** even at width 1/1024 (M = 2 best): L = 1141.03 (delta 1.0000008), 1174.0 (1.0194), 1240.05 (1.00000003), 1274.0 (1.0461), 1324.0 (1.0459). No _S/_H csv was written; check5 was not run.
- The sampled scans (scan5.py, S samples every 25 from L1) reported "min k = 36" for T1 and T2. They miss these narrow peaks, so **sampled "min k" values are optimistic and are not results**.
- The failure points are in the seam (zeros at log T ~ 31.7-36.8), where the Bellotti-row part dominates. The floored zero count (cf, x0.86-0.89 at these heights; see the diagnostics above) would very likely close them, but it needs regenerated and re-verified low rows. Not done.
