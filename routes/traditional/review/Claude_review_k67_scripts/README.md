# Claude 审稿报告的独立复算脚本

配套报告：[`../Claude_review_k67_proof_2026-11-06.md`](../Claude_review_k67_proof_2026-11-06.md)

- 这些脚本只按 `proof/manuscript.md` 中的公式独立重写了 δ_H（命题 H）和 δ_S（命题 S 与 Lemma 5），**没有复用项目代码**。
- 唯一的例外是 `check_rj_and_propH.py`：它导入 `proof/code/rigorous_smooth.py`，用来比较项目算出的 R̃_j 上界。
- 所有计算都是**逐点、非严格**的（mpmath 计算，Simpson 求积）。它们的用途只有两个：检验证书的上界不低于公式值，以及评估余量与敏感性。**不能当作证书使用。**

## 文件与报告的对应关系

| 脚本 | 内容 | 对应报告 | 用时（参考） |
|---|---|---|---|
| `indep_check.py` | 核心库：δ_H、δ_S、精确的 R_j、Lemma 5 中的 Φ | — | — |
| `misc_checks.py` | KLN Lemma 3.2 的数值；BTY 的交接点 e^{76.463}；代码中硬编码的 Bellotti 表 2 全部行与 arXiv v2 逐行比对 | §3.5、M3 | 约 20 秒 |
| `check_rj_and_propH.py` | 精确 R_j 与代码 R̃_j 的比较；命题 H 证书抽查 8 段 | §3.6、附录 A.1 | 约 1 分钟 |
| `check_propS.py` | 命题 S 证书抽查 7 段 | 附录 A.2 | 约 2 分钟 |
| `scan_sensitivity.py` | 瓶颈区 L ∈ [3550, 3950] 的逐点 δ_S 与敏感性（4.896 ×1.005/×1.01，B ×1.005/×1.01，C ×1.05）；去掉 19.62 的扫描 | M1、M2、附录 A.3、A.4 | 约 2–5 分钟（16 进程实测 137 秒） |

## 运行方法

在本目录下运行：

```bash
python -B misc_checks.py
```

```bash
python -B check_rj_and_propH.py
```

```bash
python -B check_propS.py
```

```bash
python -B scan_sensitivity.py
```

- **依赖**：Python 3.10 及以上、mpmath（测试版本 1.4.1）；`check_rj_and_propH.py` 另需 python-flint 0.9.0。
- **不写入任何文件**：脚本在开头设置了 `sys.dont_write_bytecode = True`，加上 `-B` 参数，不会在 `proof/code/` 或本目录生成 `__pycache__`。证书和论文按相对路径读取（`../../proof/certificates/`、`../../papers/`）。

## 方法要点

- **δ_H**：手稿 §6 的五项误差 E_triv + E_K + E_B + E_tr + E_pp 在单个 L 处求值。每段用证书给出的 c（μ = c/67）和 σ\*；η 取该段 u 区间上端的值，与证书的做法相同。
- **δ_S**：
  - R_j = ‖φ^{(j)}‖₁/∫φ 用 φ^{(j)} 的变号点精确计算。
  - Φ(t) 取 Lemma 5 中选项 (a)、(b)、(c) 的最小值，σ\* 的候选值与项目代码相同：α₀、α₀ + 0.001、α₀ + 0.003、0.995。
  - ∫Φ d(−g) 在 v = log t 上用 Simpson 法求积，步长 1/256；v ≥ V 的部分用闭式。
- **扰动实验**：每个任务开始前都会重置模块中的常数，再施加扰动。早期草稿在多进程中改了全局变量而没有重置，那批数据已全部丢弃，报告中没有引用。

## 2026-11-06 运行结果摘要

- `misc_checks.py`：
  - KLN 下界的最小值 1.4604157 大于 |ζ(1/2)| = 1.4603545，[0, 3] 上的最大值在 t = 0 处取到；
  - 交接点 log t = 76.463；
  - Bellotti 表 39 行全部一致。
- `check_rj_and_propH.py`：R̃_j 不小于 R_j；8 段命题 H 证书的逐点值都不超过证书上界。
- `check_propS.py`：7 段命题 S 证书的逐点值都不超过证书上界；最紧的一段是 [3708.4, 3712.4]，证书 0.99980，逐点约 0.98。
- `scan_sensitivity.py`：数值与报告附录 A.3、A.4 及 M2 的表一致。
