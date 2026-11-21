# RH 发布跟踪与相邻立方推论

记录日期为 2026 年 11 月 21 日。以下形式化及独立复算均归原作者和所列核验者。本项目核对了公开记录，并整理了末节的数学推论。

## 发布材料与可核对的证据

- **原始声明与源码。** Levent Alpöge 于 11 月 20 日宣布与 Claude 合作得到了经典 RH 以及 Dirichlet $L$ 函数的 GRH 的 Lean 证明。四页公告的脚注列出 14 个源码分卷。LUMI 公布的合并归档 SHA-256 为 `9631b4f020199e580ba86178cb56c6e9b09f690c2369a80dc4334aa93f49c7fc`。[原始公告](https://alpo.ge/remark.pdf) · [分卷与复算记录](https://github.com/aapolipponen/rh-lean-check-lumi)
- **核对定理和前提。** Andrew Sutherland 公布的日志显示，顶层定理 `riemannHypothesis : RiemannHypothesis` 引用 Mathlib 的定义。日志逐项打印了五个主定理的公理依赖，均只有 `propext`、`Classical.choice`、`Quot.sound`。[原始日志，第 30–38 行](https://math.mit.edu/~drew/grh/audit.log)
- **核对完整证明。** Sutherland 在 11 月 20 日 22:05 UTC 的记录中报告，175,187 个模块通过编译及逐模块内核重放；nanoda 和 con-leche 均接受完整导出，con-leche 还核对了五项命题。该时间点的端到端 `lake comparator` 流程仍在运行。[核验表与逐项日志](https://math.mit.edu/~drew/grh/)
- **独立构建。** Aapo Lipponen 在 LUMI 超算的无网络沙箱内完成全量编译；两处构建的 `Main.olean` 和 `Statements.olean` 散列一致。[LUMI 构建记录、环境和复现步骤](https://github.com/aapolipponen/rh-lean-check-lumi)

## 为什么经典 RH 推出每对相邻立方之间都有素数

这里只需黎曼 ζ 函数的 RH。Dudek 的显式短区间定理给出：假设 RH，对每个实数 $x>2$，存在素数 $p$ 满足

$$x-\frac{4}{\pi}\sqrt{x}\log x<p\le x.$$

取 $m=n+1$ 和 $x=m^3$，其中 $n\ge1$，对数均为自然对数。右端点 $m^3$ 为合数，因此 $p<m^3$。[Dudek 的定理与原文](https://arxiv.org/abs/1611.07251)

当 $m\ge16$ 时，$\log m/\sqrt m$ 随 $m$ 递减（导数的符号由 $1-\tfrac12\log m$ 决定），故其值至多为 $\log 16/4=\log 2<0.7$。用 $\pi>3$ 得

$$\frac{12}{\pi}m^{3/2}\log m < 2.8m^2 < (3-3/m)m^2+1 = m^3-(m-1)^3.$$

于是定理给出的素数严格落在 $((m-1)^3,m^3)$ 内。余下 $n=1,\ldots,14$ 的素数见证依次为

```text
2, 11, 29, 67, 127, 223, 347, 521, 733, 1009, 1361, 1733, 2203, 2749
```

逐项试除至平方根即可验证素性，同时比较两个立方端点。这样便覆盖了每一个正整数 $n$。

## English summary

Alpöge announced a Lean proof of classical RH and its Dirichlet $L$-function generalization on 20 November 2026. The records above link the author’s archive notice, the printed Mathlib statement and its axiom dependencies, Sutherland’s kernel checks, and Lipponen’s independent sandboxed build.

Classical RH alone implies the cube result. Apply Dudek’s explicit interval theorem above at $x=m^3$, where $m=n+1$. For $m\ge16$, the displayed inequality makes the interval shorter than the gap between the cubes. Its upper endpoint is composite. The listed primes cover $1\le n\le14$ in order, so both endpoints are strict for every positive integer $n$.
