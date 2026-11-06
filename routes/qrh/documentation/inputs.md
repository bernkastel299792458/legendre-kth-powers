# 七项精确外部输入

版本日期：2026-11-06。本页是当前论文及 Lean 定理的输入登记，不是对上游七项结果的重新证明。机器可读记录见 [inputs.json](inputs.json)，论文陈述见 [第 2 节](../paper/current/sections/02_inputs.tex)。

[`sixth_powers_from_named_inputs`](../lean/LegendreK6/FinalResult.lean) 的完整参数依次为 H1–H7。它们是显式命题参数，不是七个新增全局公理，也不是待证局部素数区间结论。本库完成的是**从这七项输入到最终六次幂结论的下游形式化**；七项输入本身均未在本库重证。这里“可信”只记录项目采用的证据标准，不表示正确概率或形式化完成率。

| 输入 | Lean 命题 | 证据分类与当前边界 |
|---|---|---|
| H1 QRH(7/8) | `QRHSevenEighths` | 按项目约定接受 OpenAI 的官方证明发布；本库未重建上游 |
| H2 CS v2 | `CSv2` | 固定版本预印本的额外前提；未确认同行评审发表或接受 |
| H3 Rosser 计数 | `RosserZeroCount` | 有正式发表依据；经 Dusart 的重述核对，保留闭矩形约定 |
| H4 积分显式公式 | `IntegratedExplicitFormula` | 正式发表文献的精确特化；接受稿已核对 |
| H5 有限高度 RH | `FiniteRH3e12` | 已发表的严格区间计算定理；本项目没有重跑上游计算 |
| H6 CHJII | `CHJIIShortInterval` | 已发表；指定 arXiv 陈述对应通过，期刊正文逐字比对待补 |
| H7 CHL | `CHLRows` | 已发表及正式勘误；作者修订表对应通过，正式勘误表比对及独立数值认证待补 |

## 共同记号与计数约定

设 `ζ` 是真实的黎曼 ζ 函数，`ρ=β+iγ`，`m(ρ)` 是解析零点重数。Lean 使用 `riemannZeta` 和 `analyticOrderNatAt`，没有假设零点简单。令

\[
\mathcal Z=\{\rho:\zeta(\rho)=0,\ 0<\beta<1\},\qquad
\mathcal Z(T)=\{\rho\in\mathcal Z:|\gamma|\le T\},
\]
\[
N_+(T)=\sum_{\substack{\rho\in\mathcal Z\\0<\gamma\le T}}m(\rho),\quad
N(\sigma,T)=\sum_{\substack{\rho\in\mathcal Z\\\sigma\le\beta,\ 0<\gamma\le T}}m(\rho).
\]

两个上端高度和密度下界 `σ≤β` 都包含等号。`𝒵(T)` 的定义保留零高度；本库另行证明实区间 `(0,1)` 无零点，不把它藏进计数定义。正实底数的复幂使用 `x^s=exp(s log x)`；所有对数均为自然对数。`ψ(x)=Σ_{1≤n≤floor(x)}Λ(n)` 在端点包含整项，采用通常的 von Mangoldt 函数。定义与重数、共轭、有限性、实轴无零点证明见 [ZetaZeros.lean](../lean/LegendreK6/ZetaZeros.lean)。

## H1：QRH(7/8)

**精确前提：**每个 `ρ∈𝒵` 都满足 `Re ρ≤7/8`。不把它加强为 RH，也不附加有限高度限制。对应 [DensityInput.lean / QRHSevenEighths](../lean/LegendreK6/DensityInput.lean)。

- **发表及采用依据：**OpenAI 官方发布 *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8*，日期 2026-09-30。项目依用户指示接受该成果；本页不据此宣称期刊同行评审已经完成。
- **精确版本：**固定仓库提交 `4eaee87548250b2682affda7d05d947c05554bae` 的[论文入口](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)与 [Family 003 Lean 范围说明](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/003.md)。后者报告 ζ 的 `7/8` 无零半平面形式化；本项目只取其 ζ 部分。
- **数值复现：**不是以有限数值扫描替代这个无限域结论。
- **本库 Lean：**H1 是参数；没有导入或独立重建 OpenAI 的整个上游工程。
- **未完成项：**上游独立重建及与本库定义的形式化对接。本库下游编译通过不补足这一步。

## H2：CS v2 的十二行零点密度界

令 `H=3·10¹²`。对表中任一 `j=16,…,27`、整个闭区间 `j/32≤σ≤(j+1)/32` 和每个实数 `T≥H`，要求

\[
N(\sigma,T)\le B_1T^{a(\sigma)}(\log T)^{b(\sigma)}
 +B_2(\log T)^2+B_3\log T,
\quad a(\sigma)=\frac{3(1-\sigma)}{2-\sigma},\quad
b(\sigma)=\frac{7-5\sigma}{2-\sigma}=a(\sigma)+2.
\]

| 来源行 j | σ 的闭区间 | B₁ | B₂ | B₃ |
|---:|---|---:|---:|---:|
| 16 | [16/32,17/32] | 5.069 | 9.461 | 167.8 |
| 17 | [17/32,18/32] | 6.046 | 9.168 | 162.6 |
| 18 | [18/32,19/32] | 7.077 | 8.875 | 157.4 |
| 19 | [19/32,20/32] | 8.185 | 8.582 | 152.2 |
| 20 | [20/32,21/32] | 9.387 | 8.290 | 147.0 |
| 21 | [21/32,22/32] | 10.70 | 7.997 | 141.9 |
| 22 | [22/32,23/32] | 12.11 | 7.704 | 136.7 |
| 23 | [23/32,24/32] | 13.66 | 7.411 | 131.5 |
| 24 | [24/32,25/32] | 15.35 | 7.118 | 126.3 |
| 25 | [25/32,26/32] | 17.21 | 6.826 | 121.1 |
| 26 | [26/32,27/32] | 19.31 | 6.533 | 115.9 |
| 27 | [27/32,28/32] | 21.77 | 6.240 | 110.7 |

表中有限小数在 Lean 中表示精确有理数；Lean 行号为 `i=j−16∈Fin 12`。对应 [DensityInput.lean / CSv2、csB1、csB2、csB3](../lean/LegendreK6/DensityInput.lean)。Lean 的开条带计数是来源计数的限制，重数非负使这种限制只减小左边。

- **发表状态：**Chourasiya–Simonič，[arXiv:2507.15184v2](https://arxiv.org/abs/2507.15184v2)，2025-09-30，Corollary 1、Table 1。现有审查未确认该精确结果已同行评审发表或接受；不把“未查到”写成“确定未评审”。
- **精确版本：**固定 v2；不得用 v1 的统一 `log³T` 替换这里的 `b(σ)`。尾段使用的较粗 `log³T` 界是 Lean 从 v2 在指定子域推导的结果，不是原始 H2。
- **数值复现：**本库认证使用这些常数的下游表达式；这不验证常数的上游推导。早期 Claude 审阅及修订响应保存在 [来源审阅档案](../audit/source_reviews/README.md)。
- **本库 Lean：**H2 是参数；其尾段放宽、行选择和后续估计已经形式化。
- **未完成项：**CS v2 推导及常数来源的独立审查由另一路工作负责，本次不扩大或替代该审查。当前结论始终保留 H2。

## H3：Rosser 的完整零点计数界

这里单独定义来源的**闭矩形**计数

\[
N_R(T)=\sum_{\substack{\zeta(\rho)=0\\0\le\Re\rho\le1,\ 0\le\Im\rho\le T}}m(\rho).
\]

精确前提是对所有实数 `T≥2`，

\[
\left|N_R(T)-\left(\frac{T}{2\pi}\log\frac{T}{2\pi}
-\frac{T}{2\pi}+\frac78\right)\right|
\le\frac{137}{1000}\log T+
\frac{443}{1000}\log\log T+\frac{397}{250}.
\]

对应 [LiteratureInputs.lean / RosserZeroCount、rosserCount](../lean/LegendreK6/LiteratureInputs.lean)。`N₊(T)≤N_R(T)` 是已证的集合包含推论，不在源计数与项目计数之间直接声称相等。

- **发表状态：**Rosser，*American Journal of Mathematics* **63(1) (1941), 211–232**，[DOI](https://doi.org/10.2307/2371291)；卷期及页码与 [JSTOR 原卷目录](https://www.jstor.org/stable/i340750)核对。Dusart 的正式重述发表于 *Mathematics of Computation* **85(298) (2016), 875–888**，[DOI](https://doi.org/10.1090/mcom/3005)，第 877 页式 (10)–(11)。
- **精确映射：**现有核查采用 Dusart 重述；闭矩形约定还对应[作者 HDR](https://www.unilim.fr/pages_perso/pierre.dusart/Documents/HDR_Dusart.pdf)印刷第 34 页式 (2.2)–(2.3)及第 82 页 Theorem 86。未声称逐页复核 Rosser 1941 的原始证明。
- **数值复现：**不是由采样 T 推出全域；无独立上游计算重放。
- **本库 Lean：**原界为参数；从它推出所需的 `N₊(T)≤T log T` 等弱界已证，不再额外接受 CS 的总计数辅助界。
- **未完成项：**原计数定理的本库形式化证明。

## H4：完整积分显式公式

对实数 `x>1`，令

\[
\Psi_1(x)=\sum_{1\le n\le\lfloor x\rfloor}\Lambda(n)(x-n),\quad
P(\rho,x)=\frac{x^{\rho+1}}{\rho(\rho+1)},\quad
V(x)=\sum_{j=1}^{\infty}\frac{x^{1-2j}}{2j(2j-1)}.
\]

精确前提是复数域中的高度截断极限

\[
\lim_{T\to+\infty}\sum_{\rho\in\mathcal Z(T)}m(\rho)P(\rho,x)
=\frac{x^2}{2}-\frac{\zeta'(0)}{\zeta(0)}x
+\frac{\zeta'(-1)}{\zeta(-1)}-V(x)-\Psi_1(x).
\]

对应 [IntegratedExplicitFormula.lean / IntegratedExplicitFormula](../lean/LegendreK6/IntegratedExplicitFormula.lean)。平凡零点级数的符号为负，常数项为 `+ζ′(−1)/ζ(−1)`；没有用未知常数或渐近误差替代它们。

- **发表状态：**Grenié–Molteni，*Explicit smoothed prime ideals theorems under GRH*，*Mathematics of Computation* **85(300) (2016), 1875–1899**，[DOI](https://doi.org/10.1090/mcom3039)。这里使用的一般恒等式不依赖 GRH。
- **精确映射：**大学机构库接受稿及 arXiv v5 已检查。取 `K=Q`，由 (1.3a)、(3.8)、Lemma 3.3 得到上式；绝对收敛支持闭高度截断极限。接受稿留数推导中的局部笔误已单列，主公式和 Lean 的符号一致。
- **数值复现：**这是解析恒等式的纸面特化，不以有限取样验证无限级数。
- **本库 Lean：**H4 是参数；四点有限差分、仿射项消去及权函数后果已由它推出。旧源码注释保留 Hildebrand 课件来源，现有文献依据已补充正式发表的 GM 来源。
- **未完成项：**Perron/留数论证到该完整公式的上游 Lean 重证。详见 [输入 4 来源审查](../audit/input4_source_review_2026-11-06.md)。

## H5：截至 3·10¹² 的有限高度 RH

**精确前提：**对每个 `ρ∈𝒵`，若 `0<Im ρ≤3·10¹²`，则 `Re ρ=1/2`。对应 [FiniteRHInput.lean / FiniteRH3e12](../lean/LegendreK6/FiniteRHInput.lean)。它不要求零点简单，也不把结论延伸到更高高度。

- **发表状态：**Platt–Trudgian，*Bulletin of the London Mathematical Society* **53(3) (2021), 792–797**，[出版社 DOI 页面](https://doi.org/10.1112/blms.12460)。电子发表 2021-01-22，印刷卷期为 2021 年 6 月。
- **精确映射：**出版社摘要明确含闭上端 `0<γ≤3·10¹²`；[arXiv:2004.09765v1](https://arxiv.org/abs/2004.09765v1) Theorem 1 实际达到 `3,000,175,332,800`，足以覆盖本库较小截断。来源另给出的简单性未被假定。
- **数值复现：**来源是采用严格区间算术的已发表计算定理；本项目未重新运行该大规模零点验证。
- **本库 Lean：**H5 是参数；低高度加权零点和的化简与预算已经形式化。
- **未完成项：**该上游计算证明或证书的本库重建。

## H6：CHJII 的共同截断短区间公式

令 `y=x+h`。对所有实数 `x,h,T`，若

\[
x>0,\quad\log x\ge40,\quad h\ge0,\qquad
\max\{51,(\log x)^2\}<T<\frac{\sqrt{x}-2}{4},
\]

则存在**同一个** `T*∈[T,2T]`，使

\[
\left|\psi(y)-\psi(x)-h+
\sum_{\rho\in\mathcal Z(T^*)}m(\rho)\frac{y^\rho-x^\rho}{\rho}\right|
\le\frac{1447}{500T}\bigl(y\log y+x\log x\bigr).
\]

绝对值是复模；分母是 `T`，不是 `T*`；高度范围两侧严格。对应 [LiteratureInputs.lean / CHJIIShortInterval](../lean/LegendreK6/LiteratureInputs.lean)。

- **发表状态：**Cully-Hugill–Johnston，*Functiones et Approximatio Commentarii Mathematici* **73(2) (2025), 223–242**，[DOI](https://doi.org/10.7169/facm/241110-18-11)，出版身份由期刊目录、出版社登记和作者列表核实。
- **精确版本：**[arXiv:2402.04272v3](https://arxiv.org/abs/2402.04272v3) Theorem 1.3、Table 1 首行，`α=1/2,ω=0,M=2.894=1447/500`。相关定理、表格和证明段落在 v2/v3 相同；尚未直接比对期刊正文。`λ=0.43` 是来源内部参数，不是遗漏的使用条件。
- **数值复现：**原创检查器重算 `2.8933994128…<2.894`，并用 Arb 认证所列九个标量比较。其全域归约另有纸面检查；这不等于完整解析定理或全域 Lean 重证。
- **本库 Lean：**H6 是参数；本库证明其无限尾段后果。
- **未完成项：**期刊定稿与指定版本的直接比对，以及上游解析证明形式化。详见 [输入 6 来源审查](../audit/input6_source_review_2026-11-06.md)。

## H7：CHL 的十二个素数短区间结论

对下表每一对 `(X,Δ)` 及所有实数 `y≥X`，要求存在自然数素数 `p` 满足

\[
y(1-1/\Delta)<p\le y.
\]

| Lean 字段 | X | Δ（精确整数） |
|---|---|---:|
| `row0` | 4·10¹⁸ | 39097000 |
| `row43` | exp(43) | 41816800 |
| `row46` | exp(46) | 163940000 |
| `row50` | exp(50) | 1061200000 |
| `row55` | exp(55) | 10288400000 |
| `row60` | exp(60) | 76918400000 |
| `row75` | exp(75) | 174043000000 |
| `row90` | exp(90) | 184304000000 |
| `row105` | exp(105) | 191886000000 |
| `row120` | exp(120) | 197917000000 |
| `row135` | exp(135) | 202553000000 |
| `row150` | exp(150) | 207053000000 |

对应 [Definitions.lean / CHLInterval](../lean/LegendreK6/Definitions.lean) 和 [CHLRange.lean / CHLRows](../lean/LegendreK6/CHLRange.lean)。左端开、右端闭；没有额外的 QRH 条件。最终六次幂结论右端严格的转换由下游 Lean 单独完成。

- **发表状态：**原文 *Mathematics of Computation* **91(336) (2022), 1955–1970**，[DOI](https://doi.org/10.1090/mcom/3719)；正式勘误 **93(346) (2024), 1019–1025**，[DOI](https://doi.org/10.1090/mcom/3884)，电子发表 2023-07-19。
- **精确版本：**固定 [arXiv:2103.05986v3](https://arxiv.org/abs/2103.05986v3)，2022-09-14。Theorem 1、Table 2 的十二行和域已视觉核对，与 Lean 完全一致；正式勘误全文仍未取得，不能称已逐行比对正式表。
- **数值复现：**作者代码重放的判据余量均正。但 Arb 严格确认印刷辅助参数生成的 Δ 在 `log X=50,60,75,90,105,135` 六行略低于表值，最大相对不足约 `3.36·10⁻⁶`。微调辅助参数后数值判据仍正，仅构成非严格可行性佐证；没有独立认证完整 CHL 判据。
- **本库 Lean：**十二个素数区间结论组成 H7 外部参数；其下端覆盖与拼接已经形式化。此处“表与 Lean 一致”不等于“表的上游数值证明已重建”。
- **未完成项：**正式勘误表比对、精确见证参数及完整判据的独立严格认证。差异没有被静默舍入或写入另一套 Lean 常数。详见 [输入 7 来源审查](../audit/input7_source_review_2026-11-06.md)及 [Arb 参数诊断](../audit/chl_rounded_deltas_arb_2026-11-06.json)。

## 解释最终条件结论

在 H1–H7 同时成立的前提下，当前 Lean 定理给出每个自然数 `n≥1` 的严格开区间 `(n⁶,(n+1)⁶)` 中都有素数。H3–H7 的文献身份不会使这些参数从定理类型中自动消失；H1 的 OpenAI 上游发布也不自动证明 H2。固定版本、精确前提、上游检查边界和下游内核证明应一并阅读。
