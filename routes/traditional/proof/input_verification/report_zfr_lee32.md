# Input verification: zero-free regions (I-ZFR) and Lee Prop. 3.2 (I-LEE32)

*Produced by a verification sub-agent on 2026-11-06; saved by the main session. Sources are in `sources_zfr/`, including Yang's PhD thesis (open access, CC BY 4.0, doi:10.26190/unsworks/31825).*

## Statuses

| Item | Status |
|---|---|
| 5.558691, \|t\| ≥ 2 (Mossinghoff–Trudgian–Yang, Res. Number Theory 10:11, 2024, Thm 1.3) | **CONFIRMED** (journal PDF) |
| 21.233, \|t\| ≥ 3 (Yang, JMAA 534 (2024) 128124, Cor 1.2) | **CONFIRMED** (arXiv v2 full text; journal abstract) |
| 53.989, \|t\| ≥ 3 (Bellotti, JMAA 536 (2024) 128249; arXiv:2306.10680) | **CONFIRMED WITH CAVEAT**: the journal abstract says 53.989, but arXiv v1 (the only version) says **54.004**. The journal full text was not accessible. *This project uses 54.004, which is implied by either value.* |
| 4.896, t ≥ 3 (Bellotti–Trudgian–Yang, arXiv:2603.21490v1, Thm 1) | **CONFIRMED WITH CAVEAT**: arXiv only. Does **not** depend on the thesis; above exp(76.463) it uses the published 21.233 region. There is a typo in its parameter table ("(4.8596)^-1" should be (4.896)^-1). |
| 4.862 (t ≥ 2), 19.62 (t ≥ 3), 51.34 (t ≥ 3) (A. Yang, PhD thesis, UNSW Canberra, Aug 2025, Thms 1.1–1.3) | **CONFIRMED WITH CAVEAT**: thesis only; the three constants depend on each other |
| 4.8594 (BTY Thm 2) | Conditional only; not used |
| Width monotonicity / uniformity for \|t\| ≤ T | **CONFIRMED** |
| Lee Prop 3.2, k = 67, "for all log x ≥ x_A" | **CONFIRMED WITH CAVEAT** (see below); *no longer used by this project* |
| `mpm.dps = 150` in Lee's code | **DISCREPANCY (benign)**: it should be `mpm.mp.dps`, and with mpmath ≥ 1.4 it raises an error |

## Thesis details

- Theorem 1.1: ζ(σ+it) ≠ 0 for t ≥ 2 and σ > 1 − 1/(4.862 log t).
- Theorem 1.2: ζ(σ+it) ≠ 0 for t ≥ 3 and σ > 1 − log log t/(19.62 log t).
- Theorem 1.3: ζ(σ+it) ≠ 0 for t ≥ 3 and σ > 1 − 1/(51.34 (log t)^{2/3}(log log t)^{1/3}).
- The three are proved via Lemmas 2.1 (4.862 for 2 ≤ t ≤ exp(56.6)), 3.1 (19.62 for t ≥ exp(56.5)) and 4.1 (51.34 for t ≥ exp(544000)), which use each other in the overlapping ranges.
- No arXiv or journal publication containing 19.62 or 51.34 was found.

## Monotonicity

- 1/(Z1 log t) decreases for t > 1.
- log log t/(Z2 log t) decreases for t > e^e.
- 1/(Z3 (log t)^{2/3}(log log t)^{1/3}) decreases for t > e.
- So the maximum of the three widths decreases for t > e^e, and the region at height T holds uniformly for 3·10^12 ≤ |t| ≤ T. Zeros below 3·10^12 lie on the critical line.

**Crossover heights (log t):**

| Set | classical = Littlewood | Littlewood = VK | classical = VK |
|---|---|---|---|
| thesis | 56.564 | 545,528 | 10,951 |
| published | 45.594 | 482,036 | 8,264 |

## Lee Prop 3.2

- **Lee's own verification is incomplete.** His proof and code check the bound only at the threshold. The phrase "to ensure that the final bound decreases as x → ∞" does not prove monotonicity. His `optimise` routine only increases c, which explains c_A = 1.01001.
- **Recomputation.** At x_A = 37,420,887 the bound is 0.999999858 (and 1.00000013 at x_A − 1), so Table 3 is reproduced. This needs Z_eff = 19.4678, i.e. the thesis KV constant 51.34.
  - With the littlewood_thesis constants the bound at x_A is 1.40.
  - With the published constants it is 8.37.
- **A monotonicity argument exists:** with fixed α and Z frozen at its value at x_A, the bound decreases when Z0 < (1 − 8α/3)/(3α) = 21.22 and Z0 < 1/(2α).
- **This project does not use Lee Prop 3.2.** Its KLN constants are also affected by the discrepancy in `report_density.md`. It is replaced by Lemma T of the manuscript, which uses the corrected Johnston–Yang constants and only the published Vinogradov–Korobov region, with an explicit monotone-majorant argument checked in Arb.
