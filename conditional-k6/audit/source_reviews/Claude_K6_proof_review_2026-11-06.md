# Claude 审稿报告：QRH(7/8) 下相邻六次幂之间的素数

- **审阅对象**：`research/K6_PROOF.md`，以及它依赖的全部模块、代码与证书（版本散列见 §8）。
- **审阅人**：Claude（Anthropic，Opus 5.5）。日期 2026-11-06。
- **前提**：按委托方要求，假定 OpenAI 声称的 QRH(7/8) 正确，即 ζ 的每个非平凡零点满足 β≤7/8。本报告不审核其上游证明。
- **方式**：对 `Legendre_k8` 原有文件只读。在临时目录的副本中重放全部四个证书；用独立实现复算关键数值；逐条核对所引文献原文的定理陈述、适用域与常数。没有运行会写文件的 `code/verify_k6.py`。复算脚本随本报告存放（§7）。

## 1. 结论与建议

**结论：在 QRH(7/8) 与 §4.1 所列输入成立的前提下，证明正确。** 对每个整数 n≥1，存在素数

\[
n^6<p<n^6+6n^5<(n+1)^6 .
\]

没有发现数学漏洞、覆盖缺口或计算错误。四个证书全部可重放，独立复算与证书一致。

**定理的真实前提比文中写的多一项。** 中段不可或缺地依赖 Chourasiya–Simonič（下称 CS）预印本 v2 的推论 1。CS 目前只有 arXiv 版本，未见期刊信息。若改用其 v1 版本，最紧单元的总扣除约为 9.08，证明不成立（§5）。因此本结果应陈述为"QRH(7/8) 与 CS v2 推论 1 之下"的条件定理，而不是"QRH(7/8) 加已发表文献"。

**建议：小修后可接受（minor revision）。** 必须修改的是定理陈述与输入文档（§6 A 类）。强烈建议提高中段的认证余量，并整理成自洽稿件（§6 B 类）。

## 2. 领域现状（截至 2026-11-06，仅列公开文献）

| 前提 | 对所有 n 成立的最好结果 | 来源 |
|---|---|---|
| 无条件 | k≥86 | Lee，arXiv:2602.14340（Acta Arith. 待刊）。此前依次为 k≥90（Cully-Hugill–Johnston II）、140、155 |
| 无条件，充分大的 n | 立方：n≥exp(exp(32.892)) | Cully-Hugill（Lee 文中转述） |
| 完整 RH | 对所有实数 x≥1，(x^{2.25},(x+1)^{2.25}) 中有素数，因而 k=3 成立；k=2 仍未解决 | Chamberland–Straub，arXiv:2602.22502 |
| QRH(7/8) | k≥8，另有 (n⁸,n⁸+n⁷) 与 (x,x+x^{7/8}) | Visser，arXiv:2610.20058（2026-10-14） |

- Visser 只使用 Fiori–Jaskari 在 QRH 下给出的 \|ψ(x)−x\|<0.04934x^{3/4}log²x+0.02636425x^{7/8}，没有使用零点密度。
- OpenAI 的 7/8 稿件题为 *A Zero-Free Half-Plane Re(s)>7/8*（2026-09-30）。另有 11/12 的替代证明（2026-10-05）、Liu 的微幅改进（Re ρ≤34999/40000，据 Visser 文献[7]）和 Kintali 的 47/48 短证明。本审阅未检索到公开反驳。
- 本审阅未检索到 QRH 下 k≤7 的公开结果。文档本身未声称新颖性。

**意义评估。** 在 QRH(7/8) 与 Ingham 型密度 \(N(\sigma,T)\ll T^{3(1-\sigma)/(2-\sigma)}\) 下，渐近地对 θ>5/8 都有 (x,x+x^θ) 含素数，所以对充分大的 n，k≥3 都是预期的。k=6 的难点只在中间一段的显式常数。本文的贡献是把 k=6 全范围显式闭合，若成立即改进 Visser 的 k=8。

## 3. 证明结构

取 x=n⁶、h=6n⁵=6x^{5/6}。由 (n+1)⁶−n⁶−6n⁵=15n⁴+20n³+15n²+6n+1>0，只需证明 (x,x+h) 含素数。

| 模块 | 覆盖范围（L=log x） | 方法 | 外部输入 |
|---|---|---|---|
| 下端 | 整数 1≤n≤1242317999994，即 6 log n≤167.088… | 1259 个素数见证，加 CHL Table 2 的 12 行 | CHL v3、Sorenson–Webster；不用 QRH |
| 中段（新） | 实数 x，167≤L≤400 | 梯形权 φ=(1/a)𝟙_{[0,a]}∗(1/b)𝟙_{[0,b]}，a=1/32、b=31/32；四点 Ψ₁ 显式公式；76 个 Arb 单元 | QRH、Platt–Trudgian、CS v2 推论 1 与式(11) |
| 远段（沿用 k=4） | 实数 x，400≤L≤700，区间 (x,x+4x^{3/4}) | φ=v²(1−v)² 平滑权；60 个 Arb 单元 | QRH、CS v2 |
| 尾部（沿用 k=4） | 实数 x，L≥700，同上 | CHJII 定理 1.3、CS 统一界、单调性 | QRH、CS v2、CHJII |

拼接：x≥1 时 4x^{3/4}≤6x^{5/6}（两者之比为 (3/2)x^{1/12}≥1）。167、400、700 三处都是闭区间重叠，没有遗漏的整数或实数点。

## 4. 逐项核验

### 4.1 文献输入（已对照原文）

| 输入 | 证明中实际用到的陈述 | 核对结果 | 发表状态 |
|---|---|---|---|
| QRH(7/8) | 所有非平凡零点 β≤7/8 | 按委托假定 | OpenAI 预印本；据官方材料（项目状态文档转述），ζ 的无零陈述有 Lean 形式化 |
| CS v2 推论 1、Table 1、式(11) | T≥3·10¹²，σ∈[i/32,(i+1)/32]（16≤i≤27）时 N(σ,T)≤B₁T^{p}(log T)^{p+2}+B₂log²T+B₃log T，p=3(1−σ)/(2−σ)。N(σ,T) 计 β≥σ、0<γ≤T 的零点，含重数 | 12 行 B₁、B₂、B₃ 与原文逐一一致；尾部用的统一界 21.77、8.290、147.0 一致；式(11) 一致 | arXiv 预印本：v1 2025-07-21，v2 2025-09-30，无期刊信息 |
| Platt–Trudgian | 0<γ≤3·10¹² 的零点 β=1/2 | 原文定理 1 给出高度 3 000 175 332 800 | Bull. LMS 2021 |
| CHL v3 定理 1、Table 2 | 对 x≥x₀，(x(1−1/Δ),x] 含素数 | 14 行 (x₀,Δ) 与 v3 原文一致；v3 注明"更正了期刊版的错误" | Math. Comp. 2022；表格以 arXiv v3 更正版为准 |
| CHJII 定理 1.3、Table 1 | log x≥40，α=1/2，ω=0，M=2.894；max{51,log²x}<T<(√x−2)/4；两端共用 T*∈[T,2T] | 与原文一致 | Funct. Approx. 2025（arXiv v3 2026-02-23） |
| Sorenson–Webster | 前 12 个素数基的强 Miller–Rabin 对 m<318665857834031151167461 是确定性的 | 与原文一致 | Math. Comp. 2017 |

### 4.2 归约与拼接

二项式展开、开区间端点、167/400/700 三处的闭区间重叠，以及"实变量 k=4 结论蕴含 k=6 远段"的包含关系，均已核对，无误。

### 4.3 下端

- 用 FLINT 的严格素性检验（`fmpz.is_prime`）独立重验全部 1259 个见证，全部通过。这一步不依赖 Sorenson–Webster。
- 独立搜索 n≤1259 时 n⁶ 之后的第一个素数，均落在 (n⁶,n⁶+6n⁵) 内，最大偏移 238。
- 独立重算 CHL 覆盖链：每行 n∈[⌈x₀^{1/6}⌉,⌊6(Δ−1)⌋]，相邻行无缝，终点 n=1242317999994，6 log n=167.08800063186…>167。
- 对使用 CHL 的 n≥1260，y=n⁵(n+6) 为合数，故文献给出的 p≤y 实为 p<y。
- 作者的只读 `--verify` 重放通过。

### 4.4 中段：解析推导

逐条推导核对，均成立：

1. **四点恒等式 (4)。** F(m)=[(x−m)₊−(x+αh−m)₊−(x+bh−m)₊+(Y−m)₊]/(αbh) 在 m<x、x≤m≤Y、m>Y 三段均成立（用到 α+b=1），所以 Σ Λ(m)F(m) 是 Ψ₁ 的四点线性组合。
2. **显式公式 (5)。** 采用 Ingham 专著中的 Ψ₁ 显式公式，其零点级数在紧集上绝对一致收敛，可以与四点组合交换。主项给出 h（因为 1−α²−b²=2αb）；仿射项和常数消去；零点项给出 −Σ_ρ∫F t^{ρ−1}dt；平凡零点项给出 −∫F/(t(t²−1))dt。符号与归一化均正确。
3. **Mellin 包络 (6)。** ‖φ′‖₁=2·max φ=64/31。dφ′ 有四个原子，各为 ±1/(αb)，总变差为 4/(αb)=4096/31。结合 |ρ|≥|γ|、|ρ(ρ+1)|≥γ² 及支撑上的 t^{β+j−1}≤x^{β−1}Y^j，得到 g_q(T)=min{1,R₁q/T,R₂q²/T²}。
4. **单元一致包络 (7)。** g 对 q 非减，且 β<1，因此先逐零点放大到 (L₋,q₊) 再做 Stieltjes 积分。这里没有比较随参数变化的导数测度。
5. **层积分 (9)–(10)。** β≥1/2 时 e^{(β−1)L}=e^{−L/2}+∫_{1/2}^{β}Le^{(σ−1)L}dσ；β<1/2 的零点由基底项放大覆盖；σ 的上限 7/8 来自 QRH。N(σ,T)≤N(s₀,T)，并在 s₀ 处取 CS 界（s₀ 落在对应行的闭区间内）；指数权精确积分。
6. **高度离散 (12)–(13)。** H 以下用有限高度 RH 和 N(H)≤H log H；H 以上用 A(T) 的单调性取右端点上界。Stieltjes 分部积分的边界项为零。
7. **解析尾部 (14)–(15)。** 由 log(u/U)≤(u−U)/U 得到分母 2−p−(p+2)/U；三个初等积分逐一验算正确；系数 4R₂q²=2×2R₂q²。
8. **素数幂与平凡零点 (16)–(17)。** ψ(Y)−θ(Y)≤√Y log²Y/(2 log 2)，乘以 max φ=32/31 再除以 h。由于 F 在两端为零，结论是开区间中有素数。

### 4.5 中段：代码与数值

- 逐行核对 `code/certify_smooth_k6.py`，实现与 §4.4 一致：σ 权精确积分、源表行域检查、H 处的分支、二次尾段起点、Arb 比较以及向上取有理数。
- 在副本中重放 76 个单元，160-bit 下全部通过。最坏单元 [179,180] 的上界为 0.991127253158798…。脚本与证书的 SHA256 与文档一致。
- 独立实现（mpmath；高度方向做连续 Stieltjes 积分，σ 网格更细）：

| 单元 | 证书上界 | 独立复算（σ 网格 1/4096） |
|---|---:|---:|
| [167,168] | 0.6595 | 0.6487 |
| [177,177.5] | 0.9442 | 0.9287 |
| [178,178.5] | 0.9843 | 0.9682 |
| [179,180] | 0.9911 | 0.9748（σ 网格 1/8192 时为 0.9701） |
| [180,181] | 0.9364 | 0.9209 |
| [395,400] | 2.40×10⁻⁶ | 2.34×10⁻⁶ |

- 证书值都高于独立复算的理想值，差额约 2%，与右端点离散化一致。
- 逐点上界的峰值约为 0.927，位于 L≈178.78。这正是平台终点 R₁q 与 H=3·10¹² 相交的位置，在解析上可以预见。

### 4.6 远段与尾部

- **[400,700] 段。** 逐一验算 R₁=15/4、R₂=40/√3<24、R₃=300（dφ″ 的总变差 6+2+2=10，含两个端点跳跃）和 max/mass=15/8。60 个单元重放通过。独立复算 [400,405] 约为 0.633，证书为 0.862。证书偏粗，主要因为 σ 网格用矩形法并取右端指数，约放大 20%，但仍是合法上界。
- **L≥700 尾部。** 逐条核对 CHJII 的适用条件（T=x^{9/32}，U=2T）。重新推导 Z₀、Z₁、Z₂、R、P、B 的表达式，均一致。独立计算 F(700)=0.5572204624，与证书一致；F(750)=0.143，F(1000)=1.4×10⁻⁴。六项的对数导数在 L≥700 均为负，单调性论证成立。作者的只读 `--verify` 重放通过。

## 5. 敏感性分析

| 情形 | 结果 | 说明 |
|---|---:|---|
| 作者算法，B₁ 统一乘 1.005 | [179,180]：0.9961 | 通过 |
| 作者算法，B₁ 统一乘 1.009 | [179,180]：1.00005 | **失败**：现有证书对 CS 常数的容差不到 0.9% |
| 作者算法，[179,180]，σ 网格 1/8192、高度网格 1/128 | 0.9717 | 加密网格即可扩大余量 |
| 作者算法，[178.75,179]，σ 1/4096、高度 1/64 | 0.9397 | 细分单元 |
| 作者算法，[179,179.25]，σ 1/4096、高度 1/64 | 0.9265 | 细分单元 |
| 独立复算，逐点 L=178.78，B₁ 乘 1.07 / 1.08 | 0.992 / 1.0013 | 方法本身约有 7% 余量（未经认证） |
| 独立复算，改用 CS v1（log³T） | [179,180]：9.08；L=178.78 逐点：8.52 | **证书失败**：v2 的对数幂 (7−5σ)/(2−σ) 是承重的 |
| 独立复算，只假定 β≤11/12 | L=179：67.7；200：33.8；250：5.93；300：0.947 | **证书失败**：结论特定于 7/8 版，11/12 版不够 |

上表中"作者算法"一栏用的是作者的 `certify_cell`（Arb 上界），只在内存中改变常数或网格，没有存档为证书。

## 6. 修改意见

### A. 必须修改

**A1. 改写定理陈述，并标明依赖等级。** `K6_PROOF.md` 中"在本证明列明的已发表输入下"不准确：CS v2 是未经同行评审的预印本，而且是承重输入。建议把它列为显式假设，例如：

> 假定 (H1) ζ 的每个非平凡零点满足 β≤7/8；(H2) Chourasiya–Simonič arXiv:2507.15184v2 推论 1（T≥3·10¹²，Table 1 前 12 行）成立。并采用以下经同行评审的结果：Platt–Trudgian、Cully-Hugill–Lee（Table 2 取 arXiv v3 更正版）、Cully-Hugill–Johnston II、Sorenson–Webster。则对每个整数 n≥1……

同时给出一张依赖表，写明每项输入的版本、发表状态、所用位置及其在证明中的作用（参照 §4.1）。

**A2. 改正 `research/INPUTS.md` 的版本矛盾。** 主输入表仍写着 CS v1 的链接和 log³T，与主线实际使用的 v2（对数幂 (7−5σ)/(2−σ)）矛盾。而 v1 无法闭合 k=6（§5），读者若按该表复核会得出"证明失败"。应改为 v2，并在 `K6_PROOF.md` 中写明"必须使用 v2"以及 v1 下的失败数值。

### B. 强烈建议

**B1. 提高中段认证余量，并报告容差。** 现有余量 0.89% 小于"B₁ 上调 0.9% 即失效"的阈值。建议把 [176,182] 细分为宽度不超过 1/4 的单元，σ 网格取 1/4096–1/8192，高度网格取 1/64–1/128，然后重发证书。按作者算法试算，[179,180] 可降到 0.9717，宽 1/4 的单元可降到约 0.93–0.94。建议在证书中报告"B₁（及 B₂、B₃）的统一放大容差"，即所有单元仍通过时的最大放大因子。

**B2. 整理成自洽稿件。** 证明现在分散在多份中英文笔记与脚本中。投稿或外审前应合并为一篇稿件，至少包括：

- 所引定理的精确陈述与适用域；
- 四点恒等式与显式公式交换的引理；
- Mellin 包络引理（含 R₁、R₂ 的推导）；
- 单元一致包络、层积分与 σ 离散的引理；
- 高度离散与解析尾部的引理；
- 素数幂与平凡零点的估计；
- 远段（k=4 平滑核，R₃ 含端点跳跃）与 CHJII 尾部的完整论证；
- 认证算法与区间运算保证的说明。

**B3. 降低对未评审预印本的依赖。**

- 证明只用到极弱的 N(T)≤T log T，可改引任何经同行评审的经典显式 N(T) 上界，不必经由 CS 式(11) 及其所引的 Bellotti–Wong。
- 应评估能否只用经同行评审的密度估计闭合中段。按对数幂粗略比较：(log T)^{5−2σ} 型估计在 σ≈7/8、log T≈30–33 处比 CS v2 的 (log T)^{7/3} 大约 (log T)^{0.92}≈20–25 倍，预计无法替代。若确实不能，应在文中明确这一依赖，并请 CS 作者确认 v2 推论 1，特别是 v1→v2 对数幂的改进。

**B4. 争取人类专家审阅。** 现有"独立审阅"都是同一 AI 系统内子代理之间的交叉复核。投稿前应请显式解析数论方向的专家审阅解析引理与 CS 依赖。

### C. 一般建议与编辑

**C1. 验证脚本会写文件。** `code/verify_k6.py` 会覆盖 `results/k6_verification_summary.json`，不是只读的。建议增加 `--output` 或 `--dry-run` 选项，并在 RUNBOOK 中标明。它的"远段包含"检查只是常数比较，文中应保留解析理由 (3/2)x^{1/12}≥1。

**C2. 补全推导细节与出处。** 包络 (6) 中应写明 |ρ|≥|γ|、|ρ(ρ+1)|≥γ²（ρ≠0,−1），以及 F′ 的跳跃包括两个支撑端点。Ψ₁ 显式公式应注明出处（如 Ingham 专著）。

**C3. 补充文献比较。** 补充 Visser 的 k=8（只用 Fiori–Jaskari 的 ψ 误差界，没有用密度）、Lee 的 k=86，以及 Chamberland–Straub 在 RH 下的 2.25。说明在 QRH(7/8) 加 Ingham 型密度下渐近有 θ>5/8，所以 k=6 属于预期结果，本文的贡献在于显式闭合。说明结论依赖 7/8 版而非 11/12 版（§5）。

**C4. 可选推论。** 中段与远段给出的是实变量结论。由于 k≥6、x≥1 时 kx^{1−1/k}≥6x^{5/6}，只需为每个 k 补齐下端（CHL 加少量见证；k≥62 时 n^k<4·10¹⁸ 只有 n=1），就可能得到"所有 k≥6"的结论，其中 k=7 几乎是现成的。此推论需要逐 k 核验下端，本审阅未做。

**C5. 下端可去掉一项依赖。** 可以用严格素性证明（例如 FLINT 的 `fmpz_is_prime` 或 Pocklington 证书）取代对 Sorenson–Webster 的依赖。本审阅已用 FLINT 复核全部 1259 个见证。

**C6. 说明 CHL 版本。** 已固定引用 CHL v3。建议补一句：v3 更正了期刊版表格，证明使用的是更正后的数值。

## 7. 复现

审阅时的重放都在临时目录的副本上进行，并对每个证书使用只读的 `--verify`。以下脚本随本报告存放于 `review/`，均不写入项目文件：

| 文件 | 内容 | 命令（在 `review/` 目录运行） |
|---|---|---|
| `Claude_indep_bound.py` | 中段、远段与尾部的独立复算，以及 v1、11/12、常数放大的敏感性测试（浮点，仅供对照，不是证书） | `python -I Claude_indep_bound.py all` |
| `Claude_witness_check.py` | 用 FLINT 严格检验全部见证，独立搜索 n≤1259 的首个素数，重算 CHL 覆盖链 | `python -I Claude_witness_check.py` |
| `Claude_sensitivity_authors_code.py` | 在内存中改变作者 `certify_cell` 的常数与网格（§5 的"作者算法"各行） | `python -B Claude_sensitivity_authors_code.py scale` 或 `refine` |

运行环境：Python 3.12.10、python-flint 0.9.0、mpmath 1.4.1。

## 8. 审阅版本（SHA256）

| 文件 | SHA256 |
|---|---|
| `research/K6_PROOF.md` | `58d6405f72e20dacfda06fb693b4522005c1b7c7232691b5d0256669100da034` |
| `research/SMOOTH_K6_CERTIFICATE.md` | `8d293530b5304036cabcd59c3d476389fec755144c36f70e2ecdcc1d0ce55bdc` |
| `research/LOWER_RANGE_K6.md` | `e0473caf168b9acb47271e940e286d08078a19c0a2c51abbc376757589a718bd` |
| `research/SMOOTH_CERTIFICATE.md` | `a035e1a8704dbacf96e5be22644af29c73d46de140c9611bbbdfee4b3c9db96d` |
| `research/TAIL_BOUND_CS.md` | `fc6b4bc41b23cad2717f4d6f20d1e9ae86961254a84832c7f943a3729467e236` |
| `research/INPUTS.md` | `0914dd78b251598701543fc55e278a3b23a7e13d9b3ecabebd974f6795190a97` |
| `code/certify_lower_range_k6.py` | `0d7149060506aa6b18c9c25a14b0e64ba9bbdeade42ba44888c24de6154b2d93` |
| `code/certify_smooth_k6.py` | `9555c1ad6dfb713b84b2d9c3b28938fb353f551d8e517be200a4f8ea4e563ede` |
| `code/certify_smooth_segment.py` | `ec7e6d218e09967d9161f44074c35ecdce09eb6a3a3a3d307db1e5b36083d21e` |
| `code/certify_tail_cs.py` | `162e880b9ad62f6ae47dd16a6b7ea75bce0a34cab35fff2975c169430ee77cb6` |
| `code/verify_k6.py` | `8a2c87b084b80487a13a313c9fd35c5277daba35d3b7f5fe3586f01973c28ad4` |
| `results/lower_range_k6_certificate.json` | `a108bd9166c0c8c137ee5299e1b5a135e825efa6514894be5054872299fd60fc` |
| `results/smooth_k6_certificate.json` | `165988b5642582864ba39bf6415c43776f45a94501a280da8692fe3ae48d69d0` |
| `results/smooth_segment_certificate.json` | `7e3768054da03709927d63a3f2d5766b7d0b26a7f600d4a8005621413e1a2a7f` |
| `results/tail_cs_certificate.json` | `d579daae45c617416d14282b69aa727e0f4b7e10699e73678bfebc6b2b743e84` |
| `results/k6_verification_summary.json` | `2168677712671806097dc5294ab8e3c351a21b0dd643ad4de6cbe095a64da680` |

## 9. 来源

- [Chourasiya–Simonič, An explicit form of Ingham's zero density estimate, arXiv:2507.15184v2](https://arxiv.org/abs/2507.15184v2)
- [Cully-Hugill–Lee, Explicit interval estimates for prime numbers, arXiv:2103.05986v3](https://arxiv.org/abs/2103.05986v3)
- [Cully-Hugill–Johnston, On the error term in the explicit formula of Riemann–von Mangoldt II, arXiv:2402.04272v3](https://arxiv.org/abs/2402.04272v3)
- [Platt–Trudgian, The Riemann hypothesis is true up to 3·10¹², arXiv:2004.09765](https://arxiv.org/abs/2004.09765)
- [Sorenson–Webster, Strong pseudoprimes to twelve prime bases, arXiv:1509.00864](https://arxiv.org/abs/1509.00864)
- [Lee, Minimal zero-free regions for results on primes between consecutive perfect kth powers, arXiv:2602.14340](https://arxiv.org/abs/2602.14340)
- [Chamberland–Straub, Weakening the Legendre Conjecture, arXiv:2602.22502](https://arxiv.org/abs/2602.22502)
- [Visser, Primes between 8th powers?, arXiv:2610.20058](https://arxiv.org/abs/2610.20058)
- [Fiori–Jaskari, Explicit bounds for the prime number theorem, arXiv:2609.23222](https://arxiv.org/abs/2609.23222)
- [OpenAI, The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)
- [Kintali, A Short Proof of the Quasi-Riemann Hypothesis](https://shivakintali.github.io/papers/QRH.pdf)
