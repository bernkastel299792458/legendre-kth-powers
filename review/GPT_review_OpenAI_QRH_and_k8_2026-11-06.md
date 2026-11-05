# GPT 关于 OpenAI 准黎曼猜想与 k8 成果的说明

记录者：GPT。核查日期：2026 年 11 月 6 日。

**OpenAI 已公开发布准黎曼猜想的证明声明；Matt Visser 随后以该成果为输入，推导了相邻八次幂之间存在素数的全范围结论。** 这是评估 k=67 工作最新背景时应单独列出的进展。

**OpenAI 的工作。** OpenAI 于 2026 年 10 月 6 日公开发布的一批数学研究中，包括署期为 2026 年 9 月 30 日的论文 *The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s)>7/8*。其关于黎曼 ζ 函数的声明为：在 Re(s)>7/8 内没有零点；s=1 为极点。这意味着每个非平凡零点 ρ 都满足 Re(ρ)≤7/8。

这不是完整黎曼猜想。完整 RH 要求所有非平凡零点满足 Re(ρ)=1/2；7/8 准黎曼猜想给出的是较弱的零点位置限制。

- [OpenAI 论文官方页面](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/README.md)
- [OpenAI 论文 PDF](https://github.com/openai/math/blob/main/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/paper.pdf)
- [OpenAI 发布集合说明](https://github.com/openai/math)

**后续 k=8 工作。** Matt Visser 于 2026 年 10 月 14 日提交预印本 *Primes between 8th powers?*，编号 arXiv:2610.20058。该文以 7/8 准黎曼猜想结果为输入，借助 Fiori–Jaskari 的显式素数计数误差估计，在 §3 推导：

```text
对每个正整数 n，存在素数 p，使得 n^8 < p < (n+1)^8。
```

其摘要明确将这些结论与上游 7/8 准黎曼猜想证明的有效性联系起来。

- [Visser 论文信息页](https://arxiv.org/abs/2610.20058)
- [Visser 论文全文](https://arxiv.org/html/2610.20058v1)

**这条证明链应如何表述。** 若 OpenAI 的上游证明及后续推导均成立，所得 k=8 结论就是无条件定理，不需要再额外假设完整 RH。Visser 的条件式表述标明其依赖的上游结果；不能因此将整条证明链永久归为仅在未经证明的猜想下成立的结果。

本轮核实了上述文献、日期与声明，没有独立逐行审核整条准黎曼猜想及 k=8 证明链。因此，本说明不作独立正确性认证，也不因尚未独立审核而断言相关成果尚无人证明或已被推翻。

如果接受上述更强结果，相应地需要重新评估 k=67 结果是否仍构成纪录改进；但外部更强定理不能替代对 k=67 稿件自身推理的审查。该稿的具体审查结果见 [GPT 评审报告](D:/UGit/AI4Math/legendre_k67/review/GPT_review_k67_proof_2026-11-06.md)。
