# Sources

The papers we used are **not** in this repository; their copyright belongs to their authors and publishers. During the work they were stored locally in `papers/` and `proof/input_verification/sources_*/` (both excluded by `.gitignore`). Below is the list, with links, so that every check can be reproduced.

In the "Role" column, (I1)–(I10) are the inputs of `proof/manuscript.md` §3.1.

## Inputs to the main theorems

| Work | Links | Role |
|---|---|---|
| E. S. Lee, *Minimal zero-free regions for results on primes between consecutive perfect kth powers*, Acta Arith. 225 (2026) 149–162 | [doi:10.4064/aa260304-20-7](https://doi.org/10.4064/aa260304-20-7), [arXiv:2602.14340](https://arxiv.org/abs/2602.14340), code: [EthanSLee/PrimesBetweenConsecutivePowers](https://github.com/EthanSLee/PrimesBetweenConsecutivePowers) | framework, inequality (3.2); k ≥ 86 |
| M. Cully-Hugill, E. S. Lee, *Explicit interval estimates for prime numbers*, Math. Comp. 91 (2022); Corrigendum, Math. Comp. 93 (2024) | [arXiv:2103.05986](https://arxiv.org/abs/2103.05986) (v3 used) | (I8): lower range, Lemma 6 |
| M. Cully-Hugill, D. R. Johnston, *On the error term in the explicit formula of Riemann–von Mangoldt* I and II | [arXiv:2111.10001](https://arxiv.org/abs/2111.10001), [arXiv:2402.04272](https://arxiv.org/abs/2402.04272) | (I6): Prop. H, Lemma T |
| C. Bellotti, *An explicit log-free zero density estimate for the Riemann zeta-function*, J. Number Theory 269 (2025) | [arXiv:2405.12545](https://arxiv.org/abs/2405.12545) (v1, v2 compared) | (I4) in v4: printed Table 2. We found a counting gap in §4 (`work/phase0_bellotti/REPORT.md`), so v4 is not supported. v5 uses her method with repaired counting and recomputed rows |
| D. R. Johnston, A. Yang, *Some explicit estimates for the error term in the prime number theorem*, J. Math. Anal. Appl. 527 (2023) | [arXiv:2204.01980](https://arxiv.org/abs/2204.01980) | (I3): 17.418 / 2.231 |
| H. Kadiri, A. Lumley, N. Ng, *Explicit zero density for the Riemann zeta function*, J. Math. Anal. Appl. 465 (2018) | [arXiv:2101.12263](https://arxiv.org/abs/2101.12263) | (I3) framework; (I10) |
| G. A. Hiary, D. Patel, A. Yang, *An improved explicit estimate for ζ(1/2+it)*, J. Number Theory 256 (2024) | [arXiv:2207.02366](https://arxiv.org/abs/2207.02366) | (I10) |
| C. Bellotti, T. Trudgian, A. Yang, *Zero-free regions inspired by work of Heath-Brown* | [arXiv:2603.21490](https://arxiv.org/abs/2603.21490) | (I5): **4.896**, used by k ≥ 70 only; audited in `proof/zfr_audit/bty_4.896/` |
| M. J. Mossinghoff, T. S. Trudgian, A. Yang, *Explicit zero-free regions for the Riemann zeta-function*, Res. Number Theory 10 (2024) 11 | [doi:10.1007/s40993-023-00498-y](https://doi.org/10.1007/s40993-023-00498-y), [arXiv:2212.06867](https://arxiv.org/abs/2212.06867) | (I5): 5.558691, used by k ≥ 74 |
| A. Yang, *Explicit bounds on ζ(s) in the critical strip and a zero-free region*, J. Math. Anal. Appl. 534 (2024) | [arXiv:2301.03165](https://arxiv.org/abs/2301.03165) | (I5): Littlewood region, 21.233 |
| C. Bellotti, *Explicit bounds for the Riemann zeta function and a new zero-free region*, J. Math. Anal. Appl. 536 (2024) | [arXiv:2306.10680](https://arxiv.org/abs/2306.10680) | (I5): VK region, 54.004 |
| S. Broadbent, H. Kadiri, A. Lumley, N. Ng, K. Wilk, *Sharper bounds for the Chebyshev function θ(x)*, Math. Comp. 90 (2021) | [arXiv:2002.11068](https://arxiv.org/abs/2002.11068) | (I7) |
| D. Platt, T. Trudgian, *The Riemann hypothesis is true up to 3·10^12*, Bull. London Math. Soc. 53 (2021) | [arXiv:2004.09765](https://arxiv.org/abs/2004.09765) | (I1) H_R |
| C. Bellotti, P.-J. Wong, *Improved estimates for the argument and zero-counting function of the Riemann zeta-function* | [arXiv:2412.15470](https://arxiv.org/abs/2412.15470) | (I2) N(T) |

## Additional inputs used by v5 (`work/`)

The v5 chains (k ≥ 37) use the refereed inputs above, apart from BTY's Theorem 1 and Bellotti's printed table, and also the following. Statements and the exact use of each are listed in the workstream reports.

| Work | Links | Role in v5 |
|---|---|---|
| D. R. Heath-Brown, *Zero-free regions for Dirichlet L-functions, and the least prime in an arithmetic progression*, Proc. London Math. Soc. (3) 64 (1992) 265–338 | — | Lemma B (Lemma 3.2), Theorem C (weight w, Re W ≥ 0) |
| J. Thorner, A. Zaman, *An explicit version of Bombieri's log-free density estimate and Sárközy's theorem for shifted primes*, Forum Math. 36 (2024) | [arXiv:2208.11123](https://arxiv.org/abs/2208.11123) | Lemma B: an inequality proved inside Prop. 2.11 |
| D. Patel, A. Yang, *An explicit sub-Weyl bound for ζ(1/2+it)*, J. Number Theory (2024) | — | 66.7·t^{27/164} in c₁ and in Lemma B-W |
| O. Ramaré, S. Zuniga Alterman, identity factory for Möbius sums (Math. Comp. 2026) | [arXiv:2312.05138](https://arxiv.org/abs/2312.05138) (v3 read) | Lemma A, input (A3); audited in `work/audit_rza/` |
| K. Ford, *Zero-free regions for the Riemann zeta function*, Number Theory for the Millennium II (2002), with the author's corrections | [arXiv:1910.08205](https://arxiv.org/abs/1910.08205) | Theorem C and the local Littlewood bands (zero detector, W₀ bound) |
| H. Kadiri, *Une région explicite sans zéros pour la fonction ζ de Riemann*, Acta Arith. 117 (2005) | — | explicit formula in Theorem C and the Littlewood bands |
| R. S. Lehman, *On the difference π(x) − li(x)*, Acta Arith. 11 (1966) | — | sums over zeros in Theorem C |
| H. Rademacher, *On the Phragmén–Lindelöf theorem and some applications*, Math. Z. 72 (1959) | — | Lemma B-W (statement as usually quoted) |
| O. Ramaré, *An explicit density estimate for Dirichlet L-series*, Math. Comp. 85 (2016) | — | ζ(σ) ≤ e^{γ(σ−1)}/(σ−1) (Lemma 5.4), local Littlewood bands |
| J. B. Rosser, *Explicit bounds for some functions of prime numbers*, Amer. J. Math. 63 (1941) | — | N(T), local Littlewood bands |
| C. Bellotti, T. Trudgian, A. Yang (preprint, above) | [arXiv:2603.21490](https://arxiv.org/abs/2603.21490) | the **method** of Lemmas 3–15, re-checked step by step for Theorem C; Theorem 1 (4.896) is **not** used |
| A. Yang, PhD thesis (above) | — | the **method** of Ch. 3 for the local Littlewood bands, with the changed steps re-proved; 19.62 is not used |

Used only in exploratory scans (not in the k ≥ 37 chain): Chourasiya–Simonič, [arXiv:2507.15184](https://arxiv.org/abs/2507.15184) (v2, preprint; audited in `work/phase1_cs/`).

Checked but not needed: Chirre–Helfgott, [arXiv:2512.15709](https://arxiv.org/abs/2512.15709) (short intervals from finite RH verification; raises L₁ for k = 35 only to about 1066); Revers, [arXiv:2602.05614](https://arxiv.org/abs/2602.05614) (ζ(1/2+it) constant; effect below 1%).

## Withdrawn input

| Work | Links | Note |
|---|---|---|
| A. Yang, *Explicit zero-free regions for the Riemann zeta-function*, PhD thesis, UNSW Canberra (2025) | [doi:10.26190/unsworks/31825](https://doi.org/10.26190/unsworks/31825) | 19.62. The proof has an arithmetic error (Lemma 3.8), see `proof/zfr_audit/thesis_19.62/REPORT.md`. Because of this, k = 67 was withdrawn. |

## Context and related work (not used in the proofs)

| Work | Links |
|---|---|
| M. Cully-Hugill, *Primes between consecutive powers*, J. Number Theory (2023) | [arXiv:2107.14468](https://arxiv.org/abs/2107.14468) |
| D. R. Johnston, J. P. Sorenson, S. N. Thomas, J. E. Webster, *Primes and almost primes between cubes* | [arXiv:2601.15564](https://arxiv.org/abs/2601.15564) |
| M. Chamberland, A. Straub, *Weakening the Legendre Conjecture* | [arXiv:2602.22502](https://arxiv.org/abs/2602.22502) |
| M. Visser, *Effective short intervals containing primes* | [arXiv:2508.18786](https://arxiv.org/abs/2508.18786) |
| M. Visser, *Primes between 8th powers?* (conditional on the claimed 7/8 quasi-RH) | [arXiv:2610.20058](https://arxiv.org/abs/2610.20058) |
| OpenAI, *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8* (preprint, 30 Sep 2026; not peer-reviewed) | [github.com/openai/math](https://github.com/openai/math) |
| C. Bellotti, *Explicit zero density estimate near unity* | [arXiv:2311.05136](https://arxiv.org/abs/2311.05136) |
| P. Dusart, *Estimates of some functions over primes without R.H.* | [arXiv:1002.0442](https://arxiv.org/abs/1002.0442) |
| N. Costa Pereira, *Estimates for the Chebyshev function ψ(x) − θ(x)*, Math. Comp. 44 (1985) — quoted by Lee; we could not access it and use BKLNW Table 14 instead | — |
