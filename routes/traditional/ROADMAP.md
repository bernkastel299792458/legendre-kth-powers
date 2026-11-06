# 科研路线图：相邻 k 次方之间的素数

## 现状（2026-11-06，阶段性成果）

- **高置信：** 对所有 k ≥ 70、n ≥ 1，(n^k, (n+1)^k) 中都有素数。依赖 4.896（BTY，arXiv；本项目已独立核实）和已发表的 21.233 等。
- **保守：** 对所有 k ≥ 74 同样成立，只用已发表的输入。
- **已撤回：** k = 67。它依赖博士论文中的 19.62，而该证明有算术错误。
- 已发表的最好结果是 86（Lee，Acta Arith. 2026）。OpenAI 的 7/8 准 RH 声明 ⇒ Visser 的条件性 k = 8。
- 审查包：`proof/`（手稿 v4、证书、Lean `main_k70` / `main_k74`、审查清单），以它为准。

## 下一步
1. **专家审阅：** BTY Thm 1（只影响 k = 70）；JNT 印刷版 Bellotti 表；手稿中的命题 S/H、引理 4/5/6、Lemma T。
2. **把 k 往下推：** 如果能在中等高度（log t ≈ 55–75）证明更强的 Littlewood 型区域（常数 < 21.233），k 可以从 70 降下来。
   参考：常数 20.08 对应 k = 68，19.62 对应 k = 67。
   回到 k = 67 的路线（`proof/zfr_audit/requirement/REPORT.md`，均需新的证明）：
   - (a) 统一的 Littlewood 常数 ≤ 19.854；论文方法修复后约 19.90，不够。
   - (b) **最有希望：** 论文论证按高度变化的版本。log t ≈ 58–85 上的局部常数是 19.3–20.0，按格点估计足以闭合 k = 67。
   - (c) 统一的 19.90，再加上直到 e^61.3 的经典常数 ≤ 4.835；BTY 的耦合路线约给出 4.830（指示值，余量 0.11%）。
3. **δ_S 的第二套严格实现。**

---

（以下为历史记录）
# 科研路线图：相邻 k 次方之间的素数

## 现状（2026-11-06）

**条件性主结果（计算机辅助；数值部分已严格验证；尚未经人工同行评审）：** 若 19.62（博士论文）与 4.896（arXiv）等输入成立，则对所有 k ≥ 67、n ≥ 1，(n^k, (n+1)^k) 中都有素数。
此前已知的最好结果是 k ≥ 86（Lee 2026）。**审查包在 `proof/`（手稿 v3，已吸收 Codex 与 Claude 两份 AI 评审；审查清单、证书、Lean 形式化），以它为准。**
背景：OpenAI 声称证明了 7/8 准 RH（未经同行评审），Visser 以此为前提推出 k = 8；若准 RH 成立，k = 67 就不再是纪录。
v2 经过文献核对，修正了 Lee 转述的输入中的 4 个问题；证明链改为
CHL（下段）→ 光滑化证书 → HYB 证书 → 自证的尾部引理（L ≥ 10^8），不再引用 Lee 的 Prop 3.2/3.3。
最少依赖：Yang 博士论文的 19.62，以及 BTY arXiv:2603.21490 的 4.896。

k = 67 的证明分为四段，各段首尾精确相接：

| L = log x | 方法 | 状态 |
|---|---|---|
| ≤ 2040.63 | Cully-Hugill–Lee 的两对 (Δ, x₀)（Lemma 6，Lean 形式化） | ✅ 文献输入 + `numeric_facts.py` |
| [2040.63, 7219] | 光滑化 + 拼接密度估计 + Bellotti 完整表（JY 常数） | ✅ `proof/certificates/cert_smooth_v3_k67_lw.csv`（v3） |
| [7219, 10^8] | 尖锐截断 + 拼接密度估计（命题 H，JY 常数） | ✅ `proof/certificates/cert_hyb_v3_k67_lw.csv`（v3，max δ 0.966） |
| ≥ 10^8 | 尾部引理 Lemma T（只用已发表的 VK 区域） | ✅ `proof/code/tail.py` |

**关键依赖：** Yang 博士论文中的 Littlewood 零点自由区域常数 19.62（与 Lee 的 k = 86 定理相同）。

## 一、优先：让结果经得起审阅

1. [ ] **人工复核数学推导**：命题 H（`docs/HYB_theorem.md` §2）和命题 S（`docs/smoothing.md` §1）。
   重点是光滑显式公式的严格表述和引用、Stieltjes 分部积分的边界项，以及每个输入的适用范围
   （T 的范围、σ 的范围、x ≥ e^1000、log x ≥ 300 等）。
2. [ ] **独立重算**：用另一套实现（例如 Sage/Arb 的 C 接口，或者 mpmath.iv）重新验证三份证书。
3. [ ] **核实 Yang 博士论文的常数**（19.62，以及适用范围 t ≥ 3）；联系作者，或等论文正式发表。
4. [ ] **严格重做 Lee 的 Prop 3.2**（L ≥ xA）：现在只是引用，加上浮点抽查（δ ≤ 0.71）。
   可以用 KLN 模式严格覆盖到很大的 L，再给出 L → ∞ 时的解析论证。
5. [ ] **写成论文**："Primes between consecutive 67th powers"。
   内容：命题 H、命题 S、完整表的使用、证书与复现说明。

## 二、继续往下：k ≤ 66

- 现有输入下，k = 66 停在 L ≈ 3361.5，k = 65 停在 L ≈ 2050，k = 64 的浮点估计最大 δ ≈ 1.77。
- 可以尝试的改进：
  - 更好的光滑权：Mellin 变换衰减更快的权、B-spline、Beurling–Selberg 型，以及对 g 做更精细的界；
  - 在高度 e^29–e^80 上改进 Bellotti 的常数，或者为 Bellotti 表加密分段；
  - 改进 KLN 估计中 (log T)^{5−2σ} 的常数；
  - 下段：重做 Cully-Hugill–Lee 的区间估计，看能否把 Prop 3.3 的上限从约 k·log(kΔ) 往上推。
- 每做一项改进，就用 `close_gap.py K` 测试，并为 k ≤ 64 补上对应的 HYB 证书和 L → ∞ 段的论证。

## 三、已完成的工作（详见 LOG.md）

- 复现 Lee 的全部计算，并找到其代码的精度 bug 和优化器的次优之处。
- 命题 H（拼接密度估计）：k = 65…85 的严格阈值 L0(k)（定理 A），以及 Lee Theorem 1.4 的改进（定理 B）。
- 命题 S（光滑化）：浮点探索，然后严格化。
- 发现并接入 Bellotti 表中 Lee 没有使用的低高度行 → k = 67 闭合。
- 排除"提高 RH 验证高度"这条路：需要把 H_R 提高到约 e^105。

## 四、文件索引

- `docs/k67_theorem.md`：**主定理**，包括证明结构、输入清单、严格计算方法和待复核事项
- `docs/HYB_theorem.md`：命题 H、定理 A（L0(k) 表）、定理 B（条件版）
- `docs/smoothing.md`：命题 S 的推导、浮点结果与严格结果
- `LOG.md`：研究日志，包括所有 bug 及其修复
- `code/bound.py`：float 版上界（KLN/BEL/HYB；`use_full_bellotti()`）
- `code/smooth.py`：float 版光滑化
- `code/rigorous_hyb.py`、`code/run_all_k.py`、`code/check_certificate.py`：严格 HYB，即定理 A
- `code/rigorous_cond.py`、`code/check_cond_certificate.py`：严格条件版，即定理 B
- `code/rigorous_smooth.py`、`code/close_gap.py`、`code/check_smooth_chain.py`：严格光滑化，即主定理
- `results/`：证书（CSV）与汇总表；`results/superseded/`：被取代的中间证书
- `papers/`：论文 PDF 与提取文本（包括 Bellotti 2405.12545 和 Bellotti–Trudgian–Yang 2603.21490）
