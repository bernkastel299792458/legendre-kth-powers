# OpenAI 准黎曼猜想最新公开信息

整理者：GPT。资料核查截止：2026 年 11 月 6 日，Asia/Shanghai。本目录另保存 Matt Visser 的 k=8 论文原始 PDF。

**OpenAI 已公开发布准黎曼猜想的证明论文，并为其中的 7/8 结论提供专项 Lean 形式化材料。** 随后，其他作者据此发展显式素数计数估计，Visser 进一步推导了所有正整数 n 的相邻八次幂区间素数结论。本文件记录这些公开材料的内容、版本与依赖关系，不替代对整条证明链的独立审核。

**1. OpenAI 发布了什么**

OpenAI 于 2026 年 10 月 6 日通过官方公告和 openai/math 仓库发布一批数学成果。公告说明同时开放多项成果的 Lean 形式化；10 月 15 日的公告更新增加了支持数学家研究、理解和拓展这些成果的资助安排，该更新本身不是数学定理的修订。[官方公告](https://openai.com/index/sharing-ai-progress-in-mathematics/)

准黎曼猜想属于仓库的 Family 003。需要区分两份论文：

| 稿件 | 署期 | 核心声明与关系 | 官方材料 |
|---|---|---|---|
| The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8 | 2026-09-30 | 声明 ζ、所有 Dirichlet L 函数及 Q(√−3) 上有限阶 Hecke L 函数在 Re(s)>7/8 的半平面无零。 | [论文页面](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)、[PDF](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf) |
| The Quasi-Riemann Hypothesis | 2026-10-05 | 对相同类别 L 函数给出 Re(s)>11/12 的替代证明；该界较弱，官方将它列为 companion/alternate proof。README 说明写作有人类协助。 | [论文页面](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/README.md)、[PDF](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-October-5-2026/paper2.pdf) |

第二份稿件并不是将 7/8 主论文撤回或把其结论改弱。两篇在官方目录中并列，分别提供主结果和较弱界的另一证明。[固定版本官方目录](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/CONTENTS.md)

这里的“无零”允许 ζ 及主特征 L 函数在 s=1 存在极点。就 ζ 的非平凡零点 ρ=β+iγ 而言，7/8 声明给出 β≤7/8；完整黎曼猜想 RH 则要求 β=1/2。准黎曼猜想要求的是一个固定、严格小于 1 的右侧零点界，因此这项工作不是完整 RH 的证明。

**2. 最新版本与更正记录**

本次通过官方 GitHub API 核实的 main 提交为：

```text
4eaee87548250b2682affda7d05d947c05554bae
提交时间：2026-10-30 00:35:35 UTC
上海时间：2026-10-30 08:35:35
```

该提交对应 CM Hodge 的 Comparator 声明调整，不是准黎曼猜想修订。[固定提交](https://github.com/openai/math/commit/4eaee87548250b2682affda7d05d947c05554bae)

截至此次核查，官方 history.md 最近列出的条目日期是 10 月 29 日、10 月 26 日和 10 月 7 日；其中未见针对这两份准黎曼猜想论文的撤回或证明修正公告。10 月 7 日记录的撤稿属于 Hodge/K3 相关工作，不能移用到准黎曼猜想。该观察只说明所查官方记录的内容，不等于断言所有外部审查已经结束。[固定版本更新记录](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/history.md)

两份准黎曼猜想预印本目录、Family 003 形式化说明、QRH Comparator 配置以及下文 solution 入口的路径提交历史，在本次查询中均仅返回最初发布提交。这不意味着整个证明库的所有间接依赖都从未调整。

**3. Lean 形式化具体覆盖什么**

官方 Family 003 专页明确列出以下范围：ζ 的 7/8 无零界；对所有正模数及所有特征的 Dirichlet L 函数同一界；Q(√−3) 上有限阶 Hecke L 函数同一界；以及 Landau–Siegel 实零点的统一对数间隔结论。Dirichlet 与 Hecke 陈述排除主特征在 s=1 的极点。专页同时说明，论文后续应用不包含在该形式化范围内。[专项形式化说明](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/docs/003.md)

该专页对应的是 9 月 30 日的 7/8 主稿及其 Landau–Siegel 配套工作，没有将 10 月 5 日的 11/12 替代证明单独列入形式化范围。不能依据整个仓库“约 42%”的统计判断 QRH 是否形式化；应以专项范围和验证入口为准。

| 材料 | 用途 |
|---|---|
| [Comparator 挑战陈述](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/QuasiRiemannHypothesis.lean) | 独立列出需要比对的 ζ 非消失命题。 |
| [Comparator 配置](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/QuasiRiemannHypothesis.json) | 将挑战对应到 solution 模块及指定定理；允许的公理列为 propext、Quot.sound、Classical.choice。 |
| [实际 solution 入口](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/OAI/NumberTheory/DirichletL/Nonvanishing.lean) | 指向 SevenEighths.ProbeFinalAssemblyUnconditional.zeta_nonzero 及相应证明模块。 |
| [官方运行说明](https://github.com/openai/math/blob/4eaee87548250b2682affda7d05d947c05554bae/lean/ComparatorChallenges/README.md) | 介绍如何运行 Comparator 验证。 |

挑战陈述中的 sorry 是待比对命题的占位符，不能据此判定实际 solution 用了 sorry。反过来，仅阅读配置与入口代码也不能代替运行检查。本次未重新构建完整依赖或运行 Comparator；因此准确状态是“官方已公布专项形式化与验证配置”，而非“本次已完成独立内核验证”。

官方给出的 QRH 验证命令为：

```sh
lake env comparator ComparatorChallenges/QuasiRiemannHypothesis.json
```

**4. 这项成果如何连接到 k=8**

证明依赖可概括为：

```text
OpenAI 的 7/8 无零半平面
    ↓
Fiori–Jaskari 的显式 ψ(x) 误差估计
    ↓
Visser 的相邻八次幂区间素数结论
```

Fiori–Jaskari 的 Explicit bounds for the prime number theorem，arXiv:2609.23222v2，日期为 2026 年 10 月 8 日。其 Theorem 1.4 在相应零点位置约束下，取 σ=7/8 后给出对 x>e³ 成立的估计：

\[
|\psi(x)-x|<0.04934\,x^{3/4}(\log x)^2+0.02636425\,x^{7/8}.
\]

这里 ψ(x)=Σ_{p^m≤x} log p。该文提供从零点限制到具体素数计数误差的中间步骤。[Fiori–Jaskari 原文 Theorem 1.4](https://arxiv.org/html/2609.23222v2)

Matt Visser 的 Primes between 8th powers? 于 2026 年 10 月 14 日提交，arXiv:2610.20058。文章以以上结果为基础，推导所有正整数 n 的结论：

\[
\exists p\text{ 为素数},\qquad n^8<p<(n+1)^8.
\]

它还讨论更短的 (n^8,n^8+8n^7)、(n^8,n^8+n^7) 区间，以及所有实数 x>1 的 (x,x+x^{7/8}) 区间。作者在摘要中明确将这些结果与上游 7/8 准黎曼猜想证明的有效性联系起来。[Visser 论文信息页](https://arxiv.org/abs/2610.20058)、[全文](https://arxiv.org/html/2610.20058v1)

**若 OpenAI 的上游证明以及上述后续推导均正确，k=8 就是无条件定理，不需要再额外假设完整 RH。** Visser 的条件式表述标示了依赖关系；不能因为本次未独立审核整条证明链，就断言它仍只是一个无人证明的假设。与此同时，官方 QRH 形式化的范围不自动包含 Visser 的全部后续推导。

**5. 已下载论文及文件核验**

本目录保存的是 arXiv 提供的原始 PDF，未改写内容：

| 项目 | 内容 |
|---|---|
| 作者 | Matt Visser |
| 标题 | Primes between 8th powers? |
| 版本 | arXiv:2610.20058v1；本次检查的信息页仅列出 v1 |
| 提交日期 | 2026-10-14；下载文件首页另标注排版日期 2026-10-15 |
| 下载日期 | 2026-11-06 |
| 页数 | 11 |
| 文件大小 | 287283 字节 |
| 下载地址 | [arXiv v1 PDF](https://arxiv.org/pdf/2610.20058v1) |
| 本地文件 | [Visser_Primes_between_8th_powers_arXiv_2610.20058v1.pdf](D:/UGit/AI4Math/Legendre_k8/Visser_Primes_between_8th_powers_arXiv_2610.20058v1.pdf) |

下载后检查了 PDF 文件头、作者和标题、全部 11 页的可解析性，并渲染核对首页。文件 SHA256 为：

```text
af0717cf0727451bc842f985e5186521cd2c7fe34799873cc7d7355ecc5d8ba2
```

本文件是截至所列日期的公开信息快照。后续跟进应优先检查 OpenAI 官方 history.md、Family 003 说明与对应配置，以及 Visser 的 arXiv 版本历史。
