# Requirement curve: how strong must each zero-free region be for the k = 67 proof?

*The computation was done by fork B of the zfr_audit session; the harness blocked it from writing this file, so the main thread wrote it from fork B's report and outputs. The main thread re-checked the key claims (`spot_check.py`) and added the grid-profile test (`priority_grid.py`, §4).*

## 摘要（中文）

- **需求（其余常数按证明取值，重新优化证书参数后，严格计算）：**
  - Z₁ ≤ **4.90875**（余量 0.26%），Z₂ ≤ **19.8539**（余量 1.19%）；
  - VK 几乎不需要：Prop H 完全不用，Lemma T 允许 Z₃ ≤ 65.1；
  - 用证书**原有**参数时余量几乎为零：Z₁ 4.89608，Z₂ 19.6212，其中 Prop H 的一块恰好需要 19.620。
- **瓶颈位置：** 都在经典区域与 Littlewood 区域的交界 log t ≈ 55 附近。Z₁ 的瓶颈在 log t ≈ 52–55，Z₂ 的瓶颈在 log t ≈ 58–85。分高度的需求见 §3：高处要求宽松得多，log t > 100 时 Z₂ 到 21 以上都可以。
- **论文修复后的统一常数 19.90 和 20.08 都不能让 k = 67 闭合**，在 L ≈ 3950–4350 处有空洞。主线程独立复核过：即使把块宽缩到 1/4096、M 放到 8，δ 仍 ≥ 1.0004。
- **按高度取局部常数则可以闭合：** 每个高度用修复后方法的局部常数 1/A(t)，取 19 个格点、每格取端点较大值再加 0.01。λ\* 和优化 λ 两种都闭合，而且在 log t ∈ [55, 56.5] 上只用 BTY 的 4.896，不需要论文的引理 2.1。但这种随高度变化的定理目前**没有证明**：论文的归纳只给出一个统一的 A。
- **用 Z₁ 换 Z₂：** 统一 Z₂ = 19.90 时，k = 67 需要 Z₁ ≤ 4.835（直到 e^61.3）。BTY 方法用耦合路线约可达 4.830（指示值），余量 0.11%。统一 Z₂ = 20.08 时需要 Z₁ ≤ 4.825，方法只能达到约 4.837，不够。
- **只用已发表结果（21.233）时：** 需要 Z₁ ≤ 4.634，BTY 的 4.896 远远不够。

## 1. Set-up

The k = 67 proof uses the zero-free region only through one number per evaluation: a lower bound η for the zero-free width that holds uniformly for all zeros with H_R < |γ| ≤ e^V. The original code uses

η(V) = max( 1/(Z₁V), log V/(Z₂V), 1/(Z₃V^{2/3}(log V)^{1/3}) ),  (Z₁, Z₂, Z₃) = (4.896, 19.62, 54.004).

`zfr_model.py` replaces this η by a hypothetical one:
- other global constants;
- one constant scaled on one height band only;
- a height-dependent Littlewood constant Z₂(v).

It then reruns the **unchanged certified code** (`proof/code/rigorous_smooth.py` for Prop S, `rigorous_hyb.py` for Prop H). Nothing in `proof/code/` or `proof/certificates/` is modified; the patch is applied in memory.

"**Closes**" means all of the following:
- a cover of [L₁, 10⁸] by Prop S / Prop H pieces was found;
- every piece was then re-evaluated under the hypothetical region, with pure arb arithmetic, and has δ < 1;
- contiguity was checked exactly, in rationals.

Lemma 6 (CHL) covers L ≤ L₁ = 2089605/1024, and Lemma T covers L ≥ 10⁸. Each cover is saved as `out/cover_<name>.csv`.

"**Fails**" means the search found no cover. The search used:
- Prop S with pieces at least 1/256 wide and M ∈ {2, 3, 4};
- Prop H with c and σ\* re-optimised per piece;
- a free S/H junction.

A different method could move the thresholds. For the main failure claims, `spot_check.py` also tries M up to 6 (§5).

Heights: the zero height is t = e^v. Here L is the proof's own variable; the bottleneck pieces at L ≈ 3700–4300 use zeros up to v ≈ 52–85.

## 2. Global thresholds (the other constants as in the proof)

| constant | with the certificates' own pieces / parameters | re-optimised: closes at | fails at | binding L |
|---|---|---|---|---|
| Z₁ (classical) | 4.896079 (slack 0.002 %) | **4.90875** (+0.26 %) | 4.908875 | 3747–3781 (v ≈ 52–55) |
| Z₂ (Littlewood) | 19.6212 (Prop S), 19.620 (Prop H, piece [6989.944, 6989.955]) | **19.853906** (+1.19 %) | 19.854687 | 4213–4216 (v ≈ 59–85) |
| Z₃ (VK) | Prop H never needs VK (every v3 H piece survives Z₃ = 10⁴) | Lemma T: Z₃ ≤ 65.117 | — | L ≥ 10⁸ |

**Published-only fallback** (Littlewood 21.233 and VK 53.989, Yang JMAA 2024): the proof then needs Z₁ ≤ **4.634** (it fails at 4.656). So BTY's 4.896 is **not** enough without the thesis's Littlewood region.

**Where each constant acts.** The two bottlenecks sit on either side of the classical/Littlewood crossover at v = e^{19.62/4.896} = 55.0:
- Smoothing pieces below L ≈ 3832 survive with the Littlewood region removed.
- Pieces above L ≈ 3844 survive with the classical region removed.

## 3. Band-localised requirement (one band changed, everything else as in the proof)

**Littlewood.** Z₂ = z on the band only, 19.62 elsewhere, Z₁ = 4.896.

| band v = log t | largest z that closes | first failure at (L) |
|---|---|---|
| (55, 58] | ≥ 30 (band not needed) | — |
| (58, 61] | 19.88 | 4077–4178 |
| (61, 64] | 19.88 | 4280 |
| (64, 67] | 20.09 | 4477–4508 |
| (67, 70] | 20.27 | 4681–4696 |
| (70, 75] | 20.18 | 4883 |
| (75, 80] | 20.48 | 5216–5249 |
| (80, 85] | 20.53 | 5550–5586 |
| (85, 90] | 20.74 | 5888–5912 |
| (90, 100] | 20.91 | 6222–6257 |
| (100, 110] | ≥ 21.0 | 6892–6914 |
| (110, 130] | 21.56 | 7547–7886 |
| (130, 170] | 21.84 | 8899–9084 |
| (170, 300] | ≥ 21.56 (smoothing not tried above L = 12000) | 12001–12318 |
| (300, 10³] | 23.81 | 19741–20138 |
| (10³, 10⁴] | 24.94 | ≈ 1.34·10⁵ |
| (10⁴, 10⁵] | 28.59 | ≈ 6.7·10⁵ |
| (10⁵, 6.78·10⁵] | ≥ 30 | — |

The bisection ran only 5 steps, so the Z₂ values are resolved to about ±0.04. The bands interact: a profile that stays below every single-band limit can still fail (§4), so this table is a guide, not a criterion.

**Classical.** The width 1/(Z₁v) is scaled by s on one band. The table gives the weakest admissible Z₁ = 4.896/s.

| band v = log t | weakest Z₁ that closes |
|---|---|
| (28.73, 31] | 4.99 |
| (31, 34] | 5.02 |
| (34, 37] | 5.04 |
| (37, 40] | 5.02 |
| (40, 43] | 5.01 |
| (43, 46] | 4.97 |
| (46, 49] | 4.94 |
| (49, 52] | 4.91 |
| (52, 55] | ≈ 4.909 (= global Z₁\*) |

Resolution is about ±0.015.

## 4. Per-height Littlewood profiles (Z₁ = 4.896, Z₃ = 54.004)

The repaired thesis method (`../thesis_19.62/`, finding F1) gives a **local** constant 1/A(t) at each height. The thesis's induction uses one A for all t ≥ H₁, so these local constants are a sensitivity guide and **not** a theorem. Using them would need a height-dependent version of the thesis's argument.

| model | closes? | failing range (L) |
|---|---|---|
| uniform Z₂ = 19.90 (repaired, optimised λ) | **no** | holes 3956–4082, 4174–4269 |
| uniform Z₂ = 20.08 (repaired, thesis λ\*) | **no** | holes 3948–4354 |
| fork B `PROF_lamstar`: thesis λ\*, 7 summary samples, worse endpoint per interval ([60,80): 20.00) | no | 4181–4333 |
| fork B `PROF_lamstar_but_6080_opt`: as above but 19.44 on [60, 80) | yes | — |
| fork B `PROF_lamstar_interp`: linear 19.42 → 20.00 on [60, 80) | yes, but the interpolation is **too optimistic** (see below) | — |
| fork B `PROF_opt`: optimised λ, 7 summary samples | yes (max δ 0.99980) | — |
| fork B `PROF_opt_noLW_below60`: no Littlewood below v = 60 | no | 3949–4195 |
| fork B `optprof55`: `PROF_opt` with Z₂ = x on [55, 60) | closes for x ≤ 19.857 | fails at 19.868 |
| main `GRID_lamstar`: thesis λ\*, full 19-point grid (see below) | **yes** (max δ 0.99979) | — |
| main `GRID_opt`: optimised λ, full grid | **yes** (max δ 0.99979) | — |
| main `GRID_lamstar_noLW`: as `GRID_lamstar`, no Littlewood region below v = 56.5 | **yes** (max δ 0.99989) | — |
| main `GRID_opt_noLW`: as `GRID_opt`, no Littlewood region below v = 56.5 | **yes** (max δ 0.99989) | — |

In every closing model the largest δ sits at L = 3708.38. That is the classical (Z₁) bottleneck, not a Littlewood one.

**Why the main thread added the grid profiles.** The thesis output has local constants at 19 heights, not just 7. For the thesis λ\* they rise **concavely** on [60, 80]: 19.415, 19.644, 19.807, 19.947, 19.997 at v = 60, 65, 70, 76.5, 80. At v = 65 the true value 19.644 is 0.08 above fork B's linear interpolation. The `GRID_*` models give each grid cell the larger of its two endpoint values plus 0.01. The `*_noLW` variants drop the Littlewood region below v = 56.5, so heights [55, 56.5] rest on BTY's 4.896 alone rather than on the thesis's unaudited Lemma 2.1 (finding F2).

**Result: all four grid models close.** So the concavity does not matter, and fork B's conclusion holds in a stronger form.

*If* the repaired thesis method is turned into a height-dependent theorem, k = 67 closes. That theorem would be: ζ ≠ 0 for σ > 1 − log log t/(Z₂(t) log t), where Z₂(t) is the local constant plus 0.01 on log t ∈ [56.5, 225.4], and Z₂ ≤ 19.10 above. The proof then closes:
- with either choice of λ;
- without the thesis's Lemma 2.1 on [55, 56.5].

The uniform repaired constant (19.90 or 20.08) does **not** suffice:
- The proof tolerates at most a uniform 19.854.
- Its Littlewood bottleneck uses zeros at v ≈ 58–85. There the local constants are 19.3–20.0.
- The sup that sets the uniform constant is attained higher up, at v ≈ 95 (λ\*) or v ≈ 129 (optimised λ). There the requirement is much weaker (≥ 20.9; §3).

**Caveat.** Between grid points the profile assumes the local constant stays below the larger endpoint value plus 0.01. That is plausible on monotone stretches, but it is not proved. In any case the local constants are themselves grid estimates from `../thesis_19.62/check_corrected_constant.py`.

## 4b. Trading Z₁ against Z₂ (`priority_combo.py`, `../bty_4.896/check_part6_combo.py`)

Can a sharper classical constant make up for a weaker *uniform* Littlewood constant? All runs are rigorous under the stated hypothetical region and used the same search as §1. Output: `out/priority_combo.json`.

| uniform Z₂ | largest Z₁ that closes | fails at |
|---|---|---|
| 19.90 | **4.835** | 4.84 |
| 20.08 | **4.825** | 4.83 |

The required Z₁ must hold up to the new crossover log t = e^{Z₂/Z₁}: 61.3 for (19.90, 4.835), 64.2 for (20.08, 4.825).

`check_part6_combo.py` evaluates BTY's final step with our corrected constants at those heights (indicative: η₀, σ₀ not recomputed for the new A₀):

| route | best 1/A₀ at log t = 61.30 | best 1/A₀ at log t = 64.18 |
|---|---|---|
| decoupled (the paper's route) | 4.8672 | 4.8731 |
| coupled (η ≥ A/L; see `../bty_4.896/REPORT.md` §4) | **4.8297** | **4.8373** |

So **uniform 19.90 plus a coupled BTY-type classical region with Z₁ = 4.835 up to e^{61.3} would close k = 67**, with a margin of 0.005 (0.11 %) in Z₁. That still needs two new proofs: the repaired thesis at 19.90, and the coupled BTY argument. With uniform 20.08 this route fails: it needs 4.825, and the method reaches only 4.837.


Output: `out/spot_check_output.txt` (ends with `SPOT CHECK PASSED`).

**Covers.** The spot check reads each cover only from its CSV. It checks contiguity in exact rationals, then re-evaluates the 40 pieces with the largest recorded δ under the model. All re-evaluated δ are rigorously below 1, and they match the recorded values:

| cover | pieces | contiguous | max δ (re-evaluated) |
|---|---|---|---|
| Z₂ = 19.853906 | 3733 | yes | 0.999999771 |
| Z₁ = 4.90875 | 4816 | yes | 0.999999722 |
| `PROF_opt` | 3333 | yes | 0.999795933 |

**Failures** (Prop S, minimum δ over M):

| model | pieces | min δ over M | result |
|---|---|---|---|
| Z₂ = 19.90 | width 1/256, M = 2..6, at L = 3960, 4000, 4050, 4200, 4250 | 1.00042 … 1.01937 | all ≥ 1 |
| Z₂ = 19.90 | width 1/4096, M = 2..8, at L = 3960, 3961, 4250 | 1.00041, 1.00051, 1.00584 | all ≥ 1, so narrower pieces do not help |
| Z₂ = 20.08 | width 1/256, M = 2..6, at L = 3960, 4100, 4300 | 1.0017 … 1.094 | all ≥ 1 |
| Z₂ = 19.854687 (information only) | width 1/256, M = 2..6, at L = 4213, 4214, 4215 | 1.00025, 0.99975, 0.99910 | only L = 4213 still fails |

So fork B's fail value just above Z₂\* depends slightly on its M ≤ 4 restriction: with larger M the true threshold of this method is a little above 19.854. Uniform 19.90 fails robustly.

## 6. Limitations

- "Does not close" applies only to this search space (§1). A finer method, such as more smoothing parameters or narrower pieces, could lower the requirement somewhat. Prop S δ values at the failing heights are 1.0004–1.02, so the gap is not tiny.
- The v3 Prop S `lw` certificate did not exist when fork B started. The v2 one was the starting point, and `repair.py` filled the gap [6989.94, 7219]. Every final cover was re-evaluated on the v3 code, and the priority results came out identical on v2 and v3 code.
- The band runs bisected only 5 steps.
- The plots are SVG, because matplotlib is not installed.

## 7. Files

All scripts run with `python -I <script>` from this directory.

| file | purpose |
|---|---|
| `zfr_model.py` | hypothetical-ZFR model; patches η in the certified code in memory |
| `common.py`, `repair.py`, `reopt.py` | certificate loading, parallel evaluation, cover repair (narrower pieces, M, c/σ\*, junction), bisection |
| `fixed_thresholds.py`, `fixed_hyb_v3.py` | per-piece thresholds for the certificates' own pieces → `out/fixed_*.csv` |
| `bands.py`, `bands_z2.py` | band-localised requirement → `out/bands*.csv/json`, `out/log_bands_*.txt` |
| `priority_z2.py` | uniform 19.90 / 20.08 and fork B's profiles → `out/priority_z2.json` |
| `priority_grid.py` | main thread: full-grid profiles → `out/priority_grid.json` |
| `spot_check.py` | main thread: independent re-check of covers and failures → `out/spot_check_output.txt` |
| `priority_combo.py` | main thread: Z₁ needed with uniform Z₂ = 19.90 / 20.08 → `out/priority_combo.json`, `out/log_priority_combo.txt` |
| `../bty_4.896/check_part6_combo.py` | main thread: BTY's best classical constant at the new crossovers → `../bty_4.896/part6_output.txt` |
| `summarize.py`, `plot_svg.py` | `out/summary.md`, `out/*.svg` |
| `out/cover_*.csv` | the covers behind every "closes" claim (method, a, b, M or c, σ\*, δ upper bound) |
