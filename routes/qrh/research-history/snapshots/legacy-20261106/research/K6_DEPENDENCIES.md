# k=6 条件性证明的依赖登记

2026-11-06，按 Claude 审阅 A1、A2 修订。这里区分研究假设、文献定理、文献计算和本地算术证书；不把引用自动等同于本项目已重做原证明。当前结论是：在 H1、H2 及下列明确文献输入下，对所有整数 n≥1，存在 n^6<p<(n+1)^6 的素数。

## 1. 两个显式研究前提

**H1：QRH(7/8)。** 每个黎曼 ζ 函数非平凡零点 ρ=β+iγ 满足 β≤7/8。用户指定接受此假设；本项目不重新审定其上游证明，不把它写成已公认定理。

**H2：CS v2 指定密度界。** Shashi Chourasiya、Aleksander Simonič，*An explicit form of Ingham’s zero density estimate*，[arXiv:2507.15184v2](https://arxiv.org/html/2507.15184v2)，固定版本日期2025-09-30，Corollary 1、Table 1前12行。记

\[
N(\sigma,T)=\sum_{\substack{\rho=\beta+i\gamma\text{ 非平凡零点}\\\beta\ge\sigma,\ 0<\gamma\le T}}1,
\]

零点按重数计算。对 T≥H=3·10^12，i=16,…,27 和**整个闭区间** σ∈[i/32,(i+1)/32]，假定

\[
N(\sigma,T)\le B_{1,i}T^{p(\sigma)}(\log T)^{q(\sigma)}
+B_{2,i}(\log T)^2+B_{3,i}\log T,
\]

\[
p(\sigma)=\frac{3(1-\sigma)}{2-\sigma},\qquad
q(\sigma)=\frac{7-5\sigma}{2-\sigma}=2+p(\sigma).
\]

全部常数以精确十进制有理数列于 [INPUTS.md 的 v2 主线表](INPUTS.md)。H2 不包括 CS 的其他未使用结果，也不自动包括其式(11)的总计数界。

截至本次检索，[arXiv 摘要记录](https://arxiv.org/abs/2507.15184v2)列出v1提交日期2025-07-21和v2日期2025-09-30，未列期刊信息。本项目因此将 H2 登记为**预印本依赖，未独立重证**；不据此断言已经查清所有出版或同行评审渠道。

## 2. 文献输入、精确使用域与状态

| 输入 | 本项目实际使用的陈述与域 | 来源与核查边界 |
|---|---|---|
| Platt–Trudgian 有限 RH | 按重数的全部非平凡零点在 0<γ≤H=3·10^12 上满足 β=1/2；所用 H 低于原核验高度3,000,175,332,800 | [arXiv:2004.09765](https://arxiv.org/abs/2004.09765)，[Bull. London Math. Soc. 2021 DOI](https://doi.org/10.1112/blms.12460)。接受其已发表计算定理，不重跑上游零点核验 |
| CHL 短区间表 | 对 Table 2 每个 (Δ,x0)，所有 y≥x0 的 (y(1−1/Δ),y] 含素数。k=6 使用前12个非空归约行，n=1260,…,1242317999994；完整整数归约见 [LOWER_RANGE_K6.md](LOWER_RANGE_K6.md) | [固定 arXiv:2103.05986v3](https://arxiv.org/html/2103.05986v3)，Theorem 1、Table 2；[Math. Comp. 2022 正文 DOI](https://doi.org/10.1090/mcom/3719)及[订正 DOI](https://doi.org/10.1090/mcom/3884)。使用订正表，不混用早版 |
| Sorenson–Webster 有限基素性 | 对整数 m<318665857834031151167461，前12素数基2,…,37的完整强 Miller–Rabin 检查确定素性。1259个见证全部在此严格域内 | [arXiv:1509.00864v1 Theorem 1.1](https://arxiv.org/html/1509.00864v1)，[Math. Comp. 2017 DOI](https://doi.org/10.1090/mcom/3134)。接受作者穷尽计算结论，本地重验每个见证 |
| Rosser 经典总计数 | 主线只用 N(T)≤TlogT，T≥H；从下节已发表经典界推出，不使用更强系数 | [Rosser 1941 Theorem 19](https://doi.org/10.2307/2371291)，本次具体核对 [Dusart 2016 第877页式(10)–(11)](https://www.ams.org/mcom/2016-85-298/S0025-5718-2015-03005-1/S0025-5718-2015-03005-1.pdf)的明确重述 |
| CHJII 共同截断高度 | 固定 α=1/2、ω=0、M=2.894；log x≥40，非负h，max{51,(log x)^2}<T<(√x−2)/4。有共同 T*∈[T,2T]，两端差分误差绝对值≤M((x+h)log(x+h)+xlogx)/T | [arXiv:2402.04272v3 Theorem 1.3、Table 1](https://arxiv.org/html/2402.04272v3)，[2025期刊页](https://projecteuclid.org/journals/functiones-et-approximatio-commentarii-mathematici/volume-73/issue-2/On-the-error-term-in-the-explicit-formulaof-Riemann-von/10.7169/facm/241110-18-11.short)。作者[研究页](https://sites.google.com/view/danielrjohnston/research)列为2025发表；具体采用固定v3陈述，不宣称已逐字核对期刊版与v3所有差异 |
| ζ 的积分显式公式 | x>1的经典 Ψ1 公式经四点有限差分得到非负梯形权加权和；零点项绝对收敛、端点原子与平凡零点项须保留 | [SMOOTH_K6_CERTIFICATE.md](SMOOTH_K6_CERTIFICATE.md)的本地解析推导；不是由数值证书自动证明 |

CHJII 只用于已有 L≥700 的实变量尾部。实际参数 T=x^(9/32)、h=4x^(3/4) 满足表列域，域验证和无限单调性在 [TAIL_BOUND_CS.md](TAIL_BOUND_CS.md)。400≤L≤700 的已有平滑模块与新167≤L≤400模块均使用 H1、H2和弱总计数界；有限RH用于新中段H以下的贡献。旧400–700段的递减核起点在H以上，无需额外使用有限RH。没有把有限RH延伸到H以上。

## 3. 独立总计数引理

**引理。** 设 N(T) 按重数计 ζ 的正高度非平凡零点 0<γ≤T。对 T≥H=3·10^12，有 N(T)<TlogT。

**证明。** Rosser 1941 Theorem 19 的经典显式界，由上述 Dusart 2016 第877页式(10)–(11)在 T≥2 上明确重述为

\[
\left|N(T)-\frac{T}{2\pi}\log\frac{T}{2\pi e}-\frac78\right|
<0.137\log T+0.443\log\log T+1.588.
\]

该文将 N(T) 定义为0≤γ≤T的临界带零点数；ζ 在实开区间(0,1)无零点，因此与本引理的正高度计数相同，不需乘2。若采用在零点高度的半权或严格高度记号，取避开零点的 T′>T 后令 T′↓T，连续的右侧同样给出含边界计数的非严格上界，足以得到下述严格结论。

由 π>1、log(T/(2πe))<logT，主项小于 (T/2)logT。又 T≥H>e，故 loglogT≤logT、logT≥1。于是

\[
N(T)<\left(\frac T2+0.137+0.443+\frac78+1.588\right)\log T
=\left(\frac T2+3.043\right)\log T<T\log T,
\]

最后一步用 T≥H>6.086。证毕。所有小数均为精确有限小数，不需额外浮点认证。

因此主链总计数不必依赖 CS 式(11)或 Bellotti–Wong 的较新优化。旧代码/JSON保存的 CS 式(11)来源标签不影响算术：它们实际计算的是同一弱界 TlogT。本次只更换这条弱界的论证依据，不改旧k=4源码或证书，也不声称直接用了 Rosser 界的更小右侧。

## 4. 版次与本地计算的边界

CS v1 将主对数幂固定为3，并采用较大的B1；v2改为上述q(σ)并降低B1。[Claude 审阅](../review/Claude_K6_proof_review_2026-11-06.md)报告，旧证书 [179,180] 单元改用完整v1输入后，普通浮点复算δ≈9.08。该结果是**旧证书不可直接换用v1**的诊断，不是对所有v1方法的不可能性证明。v1值在 [INPUTS.md](INPUTS.md)历史区保存。

本地四份证书承担：1259个整数素数见证与CHL覆盖链、167≤L≤400的新六次幂平滑中段、400≤L≤700的既有平滑实变量结论、L≥700的解析单调尾部数值前提。Arb认证有限数值不重证上游论文；复算成功也不等于完成Lean形式化或外部同行评审。

新增常数灵敏度认证只改变 H2 中 B1、B2、B3 的统一乘子，保持 p、q、σ/T域、核和总计数不变。即使允许统一上调6%，也不能据此接受改变对数幂或缩小适用域的未知文献修订。
