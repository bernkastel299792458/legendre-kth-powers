# GPT 对 k67 证明的评审报告

评审者：GPT。本报告记录本次对话中的文献核对、解析审查和数值复核。评审日期：2026 年 11 月 6 日。

评审对象为 [manuscript.md](D:/UGit/AI4Math/legendre_k67/proof/manuscript.md) 所载 v2 稿件及其代码、证书、文献附件和 Lean 文件。目标命题是：对每个整数 k ≥ 67 和 n ≥ 1，存在素数 p 满足 n^k < p < (n+1)^k。

**审稿结论：当前 v2 稿件还不能原样认定为一份完整严密的证明，但本轮没有发现足以推翻其 k=67 结论的致命错误。核心解析推导和主链数值计算基本成立；发现的明确缺口可以修补，其中数值漏项已在内存修正后复算通过。建议修订后复审。**

该判断既不是对结论的否定，也不是对全部上游文献和整篇证明的最终认证。原 proof 目录保持只读；下述内存修正没有保存到原稿或原代码。本次按用户要求，仅在 review 目录新增评审记录。

**1. 最新公开进展与本稿需要解决的问题**

必须区分“所有 n”与“充分大的 n”。经典短区间素数结果已经足以推出每个整数 k ≥ 3 在充分大的 n 时成立；本稿的核心任务是严格覆盖剩余范围，并与两端结果衔接。

| 结果类型 | 本轮核实到的内容 | 来源 |
|---|---|---|
| 已正式发表的全范围基准 | Lee 的 Theorem 1.2 给出所有 n ≥ 1 的 k=86。Acta Arithmetica 225 (2026), 149–162，2026 年 10 月 1 日上线。 | [出版社](https://www.impan.pl/en/publishing-house/journals-and-series/acta-arithmetica/online/116568/minimal-zero-free-regions-for-results-on-primes-between-consecutive-perfect-k-th-powers) |
| Lee 文献中的 k=67 | 包含大变量范围结果，以及足以推出全范围结论的额外无零区域参数；相应表格不能直接当成所有 n 的 k=67 已获证明。 | [Lee 原文](https://arxiv.org/html/2602.14340v2) |
| 2026 年 10 月的新证明链 | OpenAI 发布了 Re(s)>7/8 无零半平面的证明声明；Visser 随后以该成果为输入推导全范围 k=8。若上游证明及后续推导均成立，k=8 即为无条件结果。 | [OpenAI 原稿](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)、[Visser 原稿](https://arxiv.org/abs/2610.20058) |
| 完整 RH 下的结果 | Chamberland–Straub 的 Theorem 1.2 给出所有实数 x ≥ 1、指数至少 2.25 时的相邻幂区间素数结论，并讨论进一步改进。 | [原文](https://arxiv.org/html/2602.22502v1) |

因此，不应无保留地把“86”称为截至评审日期全部公开进展的终点。关于 OpenAI 与 k=8 的依赖关系，另见 [独立说明](D:/UGit/AI4Math/legendre_k67/review/GPT_review_OpenAI_QRH_and_k8_2026-11-06.md)。本轮没有独立认证该准黎曼猜想证明链；这不能反过来作为“该成果尚无人证明”的证据。

**2. 本轮核验通过的主要内容**

命题 H 的零点积分拆分、共轭零点因子 2、KLN 项中的 u³、L/λ_K、L/λ_B、截断误差和素数幂修正均可按所列输入重新推出。命题 S 的 Mellin 变换分部积分、Stieltjes 分部积分、低零点贡献及误差归一化也未发现主要符号、因子或方向错误。

Johnston–Yang 原文的 Lemma 2.6、常数单调性说明和 Table 3 支持 σ ≥ 0.98 时使用 17.418 与 2.231。Bellotti 的逐行零密度估计允许使用低于 e^80 的表格行。CHJ 的原始区间定理直接提供同一个 T*，不存在简单相减两个不同截断高度公式的错误。相关材料位于 [density sources](D:/UGit/AI4Math/legendre_k67/proof/input_verification/sources_density) 和 [CHJ 原始 LaTeX](D:/UGit/AI4Math/legendre_k67/proof/input_verification/sources_explicit/src_2402.04272v3/main.tex:178)。

Lemma T 对尾部上界给出的导数条件和单调性方向正确，确实将整个 log x ≥ 10^8 的范围归约为阈值处检查，并非仅在一个采样点验证不等式。小范围 CHL 推导、θ 增量为正到存在素数的推导，以及向所有 k ≥ 67 的归约未发现错误。

**3. 数值复核记录**

在禁用 Python 字节码写入的条件下完整运行了 [verify_all.py](D:/UGit/AI4Math/legendre_k67/proof/code/verify_all.py)，结果为 ALL CHECKS PASSED。四个证书 CSV 和十个 Python 文件的 SHA256 与已有 [verify_all_output.txt](D:/UGit/AI4Math/legendre_k67/proof/certificates/verify_all_output.txt) 一致。

| 部分 | 核验结果 |
|---|---|
| lw 主链平滑段 S | 1241 段，纯 Arb 复算，最坏上界 δ_S = 0.9997959336403793753225… < 1 |
| lw 主链截断段 H | 1959 段，最坏上界 δ_H = 0.9999989038129665 < 1 |
| H 的独立实现 | 不导入项目模块，按手稿公式另写端点单调上界，以 200 bit Arb 复核全部 1959 段；最坏上界 0.9999988898271364622175… < 1 |
| 小范围数值事实 | numeric_facts.py 的两项检查通过 |
| 无限尾部 | tail.py 检查通过，U(10^8) ≈ 7.326×10^-5 < 1 |
| 精确覆盖 | 用 Fraction 独立核实全部行 k=67、区间长度为正且相邻端点无缝连接 |

主链的精确连接点为：

```text
2089605/1024  ->  14315405/2048  ->  100000000  ->  无穷大
       S                  H                Lemma T
```

S 的最坏区间为 [3797381/1024, 3801477/1024]，M=3。H 的最坏区间为 [1789455/256, 7157867/1024]。

权函数常数计算默认使用 4096 格，中点都是可精确表示的二进有理数，Taylor 包络合法。Abel 单调包络、非负系数累加与尾积分公式方向正确。Bellotti 表覆盖分支虽使用浮点比较，但本轮检查的实际证书网格未发现因此漏行或误接收。

独立重实现覆盖的是 H；S 使用原纯 Arb 检查器复算，并对其上界构造作人工审查，不应把本轮描述成全部计算都已由第二套独立程序验证。备选 thesis 链的检查也通过，但其 S 使用旧浮点累计方式，不能称为全程纯 Arb；主结论依赖的 lw 链不依赖这一备选结果。

**4. 明确需要修补的问题**

**4.1 M=2 不满足已陈述显式公式的正则性条件。**

[manuscript.md 第 170 行](D:/UGit/AI4Math/legendre_k67/proof/manuscript.md:170) 的 Lemma 4 要求 F∈C²，但主证书有 31 段使用 M=2。φ(y)=y²(1−y)² 在 [0,1] 外零延拓后只有 C¹：二阶导数在 0 的内侧极限为 2，外侧为 0。因此，稿件不能按已写出的引理直接证明这些区间。

这是可修复的适用性缺口，不是结论的反例。可以把引理扩展到 F∈C_c¹、F′ 绝对连续且 F″∈L¹。令 Ψ₁(t)=Σ_{n≤t}(t−n)Λ(n)，使用其积分显式公式，与 F″ 配对并分部积分两次，即得到稿件需要的公式。零点项经两次积分后在紧区间绝对一致收敛，从而也避免 [第 177 行](D:/UGit/AI4Math/legendre_k67/proof/manuscript.md:177) 对部分和使用支配收敛时说明不足的问题。修补该引理不需要改变证书的数值上界。

**4.2 平滑积分起点存在极小漏项。**

[rigorous_smooth.py 第 260 行](D:/UGit/AI4Math/legendre_k67/proof/code/rigorous_smooth.py:260) 将起点设为 LOG_HR.upper()，实际略大于真实的 log H_R。29 段主证书走此分支；首段 g(H_R)≈0.164，并非 1，故不能直接声称省略区间没有贡献。

使用 |dg/dv|≤M≤3 和 N(e^v)≤e^v v/(2π)，漏入 δ 的量可界为 1.722×10^-24 以下。仅在内存中将起点改为 LOG_HR.lower() 后，全部 29 段重算通过，最坏上界为 0.80847607319337301280189…，余量超过 0.19。其余 1212 段不受影响，主链全局最坏上界仍为 0.999795933640379…。

因此，该问题必须清理，但不会导致本轮证书失效。原代码未作修改。

**4.3 需要补齐参数条件和端点约定。**

[Lemma 5(c)](D:/UGit/AI4Math/legendre_k67/proof/manuscript.md:205) 应明确要求 λ_K≥1，不能只列 λ_B≥1。代码 [第 142 行](D:/UGit/AI4Math/legendre_k67/proof/code/rigorous_smooth.py:142) 已检查这一条件，因此不是实际证书漏检。

此外，N(σ,T) 的定义使用 γ<T，部分零点求和使用 γ≤T；无零区域输入是严格边界，后文部分位置却写成闭边界。应统一约定，或补充极限及端点处理。积分上界只需排除 β>1−η，相关修补不要求改变主要误差公式。

**5. Lean 验证的实际范围**

本轮运行 [Audit.lean](D:/UGit/AI4Math/legendre_k67/proof/LegendreK67/LegendreK67/Audit.lean)，输出的公理只有 propext、Classical.choice、Quot.sound，没有 sorryAx。另直接检查了 Assembly.lean 和 Combination.lean 源码，检查通过。本轮未执行会产生构建文件的完整 lake build。

但 [Assembly.lean 第 38 行](D:/UGit/AI4Math/legendre_k67/proof/LegendreK67/LegendreK67/Assembly.lean:38) 的 Hypotheses 将 Hsmooth、Hhyb、Htail 直接作为假设字段；最终定理 [第 73 行](D:/UGit/AI4Math/legendre_k67/proof/LegendreK67/LegendreK67/Assembly.lean:73) 仍接收参数 H : Hypotheses。

所以 Lean 证明的是“这些区间结论成立，则主结论成立”，而不是在 Lean 内证明这些区间结论本身。原稿附录已经披露这一点；不能把无 sorry、无自定义公理解读成整篇 k=67 证明已形式化完成。

**6. 对旧 KLN 输入的文献评价需要更正**

[manuscript.md 第 72 行](D:/UGit/AI4Math/legendre_k67/proof/manuscript.md:72) 以 Hiary 旧证明的问题笼统判定旧 KLN 常数不可用，忽略了后续恢复结果。Hiary–Patel–Yang 的 Theorem 1.1 已证明：

```text
|ζ(1/2+it)| ≤ 0.618 t^(1/6) log t，t ≥ 3。
```

这强于旧 KLN 所需的 0.63 输入。论文 §1 明确说明旧论证修正后只能得到 0.77，而新方法恢复并加强了 0.63。来源：[An improved explicit estimate for ζ(1/2+it)](https://arxiv.org/html/2207.02366v1)，后发表于 J. Number Theory 256 (2024), 195–217。

因此，不能仅凭这一历史错误否定旧 KLN 结果；JY 给出较大的另一组上界，也不能证明较小的旧上界必然无效。具体的常数统一化及适用范围仍须单独审查。本轮亦追踪了 CHL 输入对旧 KLN 的间接依赖，不能仅因这种依赖否定 CHL。

这是文献评价失准，不使 v2 使用更保守 JY 常数的主论证失效。

**7. 外部输入与审查边界**

本轮核对了 Yang 博士论文中 19.62 的陈述及依赖结构，未发现循环论证：有限高度经典区域与高处 Littlewood 区域拼接，迭代起点只需既有 Vinogradov–Korobov 区域的存在，不需要反向依赖后面新证明的 51.34。但本轮没有逐项重做该博士论文全部数值极值计算。

BTY 的 4.896 输入核对至 [原论文 Theorem 1](https://arxiv.org/html/2603.21490v1)。对某些已发表版本与预印本之间的对应，本轮仍以取得的原始预印本为核对对象；例如 CHL 正式勘误全文未取得，不能宣称已逐页核对其印刷版本。

引用学位论文或预印本本身不是逻辑错误，未经过同行评审也不等于错误。本报告的判断以所列外部结果作为输入；它没有重新认证所有上游证明。

**8. 修订后复审应完成的事项**

1. 给出适用于 M=2 的平滑显式公式完整证明或精确引用。
2. 修正平滑积分起点漏项，并保存修正后的复核输出。
3. 补齐 Lemma 5(c) 的参数条件，统一零点计数、截断高度及无零区域边界约定。
4. 更正旧 Hiary 错误与 KLN 常数恢复的文献说明。
5. 保持对 Lean 实际覆盖范围的准确陈述，不以公理审计替代核心解析输入证明。
6. 更新最新进展说明，纳入 OpenAI 准黎曼猜想及后续 k=8 工作，并准确标明依赖关系。

在接受所列文献输入并完成这些修补的前提下，本轮审查结果支持 k=67 主体论证。现有稿件的数值覆盖确实闭合；尚存的问题应通过修订消除，而不是以“程序通过”或“Lean 无 sorry”替代。

**9. 被审文件版本指纹**

以下 SHA256 在保存评审记录前读取，用于识别本报告对应的版本。路径以项目目录 D:/UGit/AI4Math/legendre_k67 为基准。

```text
821A7198A19ADCF6FA5C1B624A1DAC7E9BB6B0738D6A56913711F9CD41F1B3B6  proof/manuscript.md
786D27A33540B37441CA7919944D099E87667B93D00B64259E197103867F7901  proof/LegendreK67/LegendreK67/Assembly.lean
6CBB427DEC004717A885ED3B4DF8A3F66A4AE6E953BC3D894CDAE45AF9CBE0C5  proof/code/rigorous_smooth.py
BF9FBEEA5F76CCF8247E8D11C5BFE49EF6364F4C77A41C18D900D82826214756  proof/code/rigorous_hyb.py
```
