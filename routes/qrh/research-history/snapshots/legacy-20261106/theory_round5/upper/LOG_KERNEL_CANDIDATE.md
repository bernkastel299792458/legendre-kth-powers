# 待独立审阅的 L≥360 候选：对数坐标权与区间认证 Fourier 包络

2026-11-06。作者：Codex 子代理 `structured_certificates`。
**状态：解析候选及 Arb 点预算，尚未独立完成解析审阅，不进入本轮正式证明汇编。**
主对话本轮以另外审阅的 L≥362 结果为正式远段。本文件不修改它或任何旧证书。

候选采用与第三轮相同的梯形参数 1/8、7/8，但改变了权的坐标及变换估计，
并非只微调参数。固定 CS v2 重新定基后的密度输入下，在 L=360 的完整点预算为

\[
\Delta_{\mathrm{candidate}}(360)
\le0.997685759240279156726956<1.
\tag{0}
\]

以下给出从权、Mellin 包络到无限段比较的全部拟议连接，以便下一轮独立审核。
这份数值检查本身不能替代这些连接的审阅，也不是 Lean 形式化证明。

## 1. 输入与版本

接受 QRH(7/8)。密度采用 [固定 CS v2](https://arxiv.org/html/2507.15184v2) 的
Theorem 1、Corollary 5 和第一条原 Table 1 行；具体重新定基推导只读调用
`../rebase_density.py`，参数 T₀=e^80、A₀=e^75、H=3×10¹²。
本文件不重新审核该上游推导，而将其输出表及其证明列为独立依赖。
另用 Rosser 的 N(T)≤T log T、经典积分显式公式及
[Platt–Trudgian 有限 RH 至 3×10¹²](https://arxiv.org/abs/2004.09765)。
上游重新定基的完整说明见 [第五轮 PROOF.md](../PROOF.md)；
有限 RH 高度没有被扩大到 e^80。

程序固定旧辅助模块 SHA256：
`665413028150b9eafa96d51071e2864da5408086393b91d6ea8e956798e7ea16`。
它仅复用已记录的 σ 权分解和累计上界，不调用旧文件的写入入口。
重新定基的常数仅注入这个隔离的内存字典；没有修改旧源码。
重新定基程序固定 SHA256：
`82f66c796daa445cf7e8acbe9d768029a733c9f15c0253f844e6cf8fc493cc5f`。
JSON 保存所用完整密度表，以及重新定基程序、上游证明、本程序和本文的散列。

## 2. 对数坐标权及真正的主项

令

\[
L=\log x,\quad y=x+4x^{3/4},\quad
\varepsilon=4e^{-L/4},\quad\ell=\log(1+\varepsilon),\quad q=1/\ell.
\]

取 a=1/8、b=7/8，令 φ 为 [0,a]、[0,b] 两个单位质量均匀密度的卷积。
它非负、支撑 [0,1]、两端为零，质量 1，max φ=8/7，
\(\|\phi'\|_1=16/7\)，零延拓二阶导数测度全变差 R₂=256/7。
现在定义

\[
F_x(t)=\phi\!\left(\frac{\log(t/x)}\ell\right),\qquad
A_x=\int_x^yF_x(t)dt=x\ell M_\phi(\ell),\qquad
M_\phi(z)=\int_0^1\phi(v)e^{zv}dv.
\tag{1}
\]

因此 **Aₓ≥xℓ**；它不等于旧线性坐标权的 h=4x^(3/4)。下面全部误差按 Aₓ 归一化。
F 是连续紧支撑函数，分段光滑，F′ 的分布导数为有限测度，包含折点原子和
光滑的 1/t 因子所产生的普通密度。可将经典 Ψ₁ 公式与 dF′ 配对：
Ψ₁ 的零点级数在 [x,y] 上绝对一致收敛，而 dF′ 有限全变差，因而允许交换。
两次分部积分给出

\[
\sum_m\Lambda(m)F_x(m)
=A_x-\sum_\rho\widehat F_x(\rho)
-\int_x^y\frac{F_x(t)}{t(t^2-1)}dt,
\quad\widehat F_x(\rho)=\int_x^yF_x(t)t^{\rho-1}dt.
\tag{2}
\]

这里没有把对数梯形误作四点 Ψ₁ 差分；只是使用一般 BV 配对。
下面的二次衰减同时保证变换后的零点和绝对收敛。

## 3. 精确 Fourier 核与统一复移误差

写 ρ=β+iγ、w=γℓ。换元给出

\[
\frac{\widehat F_x(\rho)}{A_x}
=x^{\rho-1}\frac{M_\phi(\rho\ell)}{M_\phi(\ell)}.
\]

由于 Mφ(ℓ)≥1、0<β<1，

\[
|M_\phi(\beta\ell+iw)-M_\phi(iw)|
\le\int_0^1\phi(v)(e^{\beta\ell v}-1)dv
\le e^\ell-1=\varepsilon.
\]

又卷积公式精确给出

\[
|M_\phi(iw)|=
\left|\frac{\sin(aw/2)}{aw/2}\frac{\sin(bw/2)}{bw/2}\right|=:|P(w)|.
\]

固定 δ=10⁻³⁸。程序严格验证 ε(360)<δ，ε 对 L 递减，所以所有 L≥360 都有

\[
\frac{|\widehat F_x(\rho)|}{A_x}
\le x^{\beta-1}\min\{1+\delta,|P(w)|+\delta\}.
\tag{3}
\]

这是真正的统一 β 复移估计，不是把 Fourier 变换误当成 Mellin 变换。
在 v 上两次 BV 分部积分另给出

\[
|M_\phi(\rho\ell)|
\le\frac{e^{\beta\ell}R_2}{|\rho\ell|^2},
\qquad
\frac{|\widehat F_x(\rho)|}{A_x}
\le x^{\beta-1}\frac{(1+\delta)R_2}{w^2}.
\tag{4}
\]

边界原子均在 R₂ 内；|ρ|≥|γ|。式 (4) 用于整个无限尾，不留下 δ 的常数平台。

## 4. 有限区间算术生成固定单调包络

固定 j=−512,…,768，wⱼ=exp(j/128)，所以 w_min=e⁻⁴、W=e⁶。
对每个完整闭格 [wⱼ,wⱼ₊₁]，Arb 区间运算包住 sin 商乘积的所有值，
再取绝对值上端并向上舍入至分母 10⁴⁰ 的有理数。记

\[
s_j=\min\{1+\delta,\operatorname{up}_{40}(
\sup_{[w_j,w_{j+1}]}|P|+\delta)\}.
\]

这里的 sup 不通过采样计算，而由覆盖整个实格的 Arb 包围上界代替。
另外取精确有理数

\[
c_{tail}=\operatorname{up}_{40}((1+\delta)R_2/W^2),
\qquad e_j=\max(c_{tail},s_j,s_{j+1},\ldots).
\]

构造 K(w)：w≤w_min 时为 1+δ，各格内部为 eⱼ，w>W 时为
c_tail(W/w)²。**在跳点取左极限**。这不会减弱上界，并与下面使用 N(Tⱼ)
的“包含端点”计数约定一致。K 非负、单调不增，且式 (3)–(4) 保证

\[
|\widehat F_x(\rho)|/A_x\le x^{\beta-1}K(|\gamma|/q)
\quad\text{对所有 }L\ge360.
\tag{5}
\]

K 在 w_min 之前的平坦处理至关重要：它把 −dK 的支持限定在 w≥e⁻⁴，
从而所有后续密度调用高度均有明确下限。
其有限部分只有正原子，质量为相邻精确有理层级之差；本轮有 396 个非零原子。
在 W 处，若最后一层大于 c_tail，额外原子同样保留。
余下的无穷测度是 2c_tail W²w⁻³dw，其总质量是 c_tail。
全部质量相加为 1+δ，没有丢失起点原子或较低零点的尾部权重。

## 5. 一点预算的严格计算

令 \(\mathcal A_L(T)=\sum_{0<\gamma\le T}e^{(\beta-1)L}\)。所需零点预算是

\[
Z(L)\le2\int\mathcal A_L(qw)(-dK(w)).
\tag{6}
\]

在有限原子 wⱼ 处用包含 γ≤qwⱼ 的累计上界，即
2·atom_mass·Φ_L(log q+log wⱼ)。因此即便零点正好落在格点，也不被遗漏。
Φ 的 σ 权分解仍使用每条源表行内的左端 p 值及精确指数权积分。
本次 σ 网格分母 32768，未将浮点求积结果用作判定。
明确地，源行给出
\(N(\sigma,e^u)\le B_1e^{p(\sigma)u}u^{p(\sigma)+2}+B_2u^2+B_3u\)，
其中 \(p(\sigma)=3(1-\sigma)/(2-\sigma)\)。于是

\[
\mathcal A_L(e^u)\le e^{-L/2+u}u+
L\int_{1/2}^{7/8} e^{(\sigma-1)L}
\left[B_1e^{p(\sigma)u}u^{p(\sigma)+2}+B_2u^2+B_3u\right]d\sigma.
\]

对网格小格 [s,t]，令 \(\omega=e^{(t-1)L}-e^{(s-1)L}\)、
\(p_s=p(s)\)、\(C_s=\omega B_1\)，并令 D、E 分别为所有小格的
\(\omega B_2\)、\(\omega B_3\) 之和。程序使用

\[
\Phi_L(u)=\sum_s C_se^{p_su}u^{p_s+2}+Du^2+Eu+e^{-L/2+u}u.
\]

尾部令 U=log q+6。每个主密度项的积分由对数切线给出

\[
\int_U^\infty e^{(p-2)u}u^{p+2}du
\le\frac{e^{(p-2)U}U^{p+2}}{2-p-(p+2)/U},
\]

分母逐项严格认证为正。乘子为 **4c_tail e^(2U)**。
在该乘子内，二次/一次 log 密度项及总计数基底的完整尾积分分别是

\[
e^{-2U}\!\left[D\left(U^2/2+U/2+1/4\right)+E\left(U/2+1/4\right)\right],
\qquad e^{-L/2-U}(U+1).
\]

没有把较低零点的残余核权重删掉。
程序核对 log q(360)−4>80，所有原子和无限尾均落在新密度表的适用域。

## 6. 素数幂与平凡零点的正确归一化

由 max F=8/7、Aₓ≥xℓ 和初等素数幂界，正素数幂贡献至多

\[
P_{pp}(L)=\frac{8/7}{2\log2}
\frac{e^{-L/2+\ell/2}(L+\ell)^2}{\ell}.
\tag{7}
\]

这里分母是 xℓ 的贡献，**没有沿用 h 作为主项**。
平凡零点项则直接利用同一个质量 Aₓ 约去：

\[
\frac1{A_x}\int_x^y\frac{F_x(t)}{t(t^2-1)}dt
\le\frac1{x(x^2-1)}=\frac{e^{-3L}}{1-e^{-2L}}.
\tag{8}
\]

总预算 Z+P_pp+(8) 在 L=360 得到式 (0)。若所有解析连接及上游新密度输入被接受，
式 (2) 的加权和便不可能全由素数幂产生；F 的端点为零，故给出严格开区间内的素数。

## 7. 全 L≥360 的比较，不依赖数值外推

整个 K 固定于上述有理层级和 δ，不随 L 重新优化。令 dμ=−dK，
取 q(L)=1/ℓ(L)。因为

\[
\frac{d\log q}{dL}=
\frac{\varepsilon}{4(1+\varepsilon)\log(1+\varepsilon)}\le\frac14,
\]

所以 q(L₀+D)/q(L₀)≤e^(D/4)，D≥0。
同第三轮固定测度论证，连续密度主项变成

\[
2L\int_{1/2}^{7/8}c(\sigma)e^{(\sigma-1)L}q^{p(\sigma)}
\int w^{p(\sigma)}(\log q+\log w)^{p(\sigma)+2}d\mu(w)d\sigma.
\]

内层 log 高度不低于 u₀=log q(360)−4>80。
利用 σ−1+p(σ)/4≤−1/24，得到相同的正衰减率

\[
\eta_1=1/24-3/(4u_0)-1/360>0.
\]

基底、B₂、B₃ 的率分别为 1/4−1/(4u₀)、1/8−2/(4u₀)−1/360、
1/8−1/(4u₀)−1/360，均由 Arb 检查为正。
网格只负责包住 L₀ 的**连续密度预算**：源行内 p(σ) 递减，u+log u>0，
故左端 p 的冻结值确实包住整格连续积分。随后比较的不是冻结网格随 L 的形状。

对式 (7)，ℓ′<0、(log q)′≤1/4、L+ℓ≥L、0<(L+ℓ)′≤1，
所以 (log P_pp)′≤−1/4+2/L<0。式 (8) 也递减。
因此若式 (0) 及上述证明连接获独立审核，可推出所有 L≥360 的条件性远段结论。
对 x=n⁴，这会对应 n≥e⁹⁰；尚未补齐此界以下的中间缺口。
**当前只将它登记为下一轮待审候选，不据此改写正式覆盖边界。**

## 8. 复算与边界

只读重放：

```powershell
python -B -X utf8 Legendre_k8/theory_round5/upper/log_kernel_candidate.py --L 360 --verify
```

重新生成专属候选 JSON：

```powershell
python -B -X utf8 Legendre_k8/theory_round5/upper/log_kernel_candidate.py --L 360 --save
```

重放忽略纯计时字段，其余字段、完整阶梯层级、常数表与依赖散列逐项一致才通过。
本候选尚无分离数值实现复算或完整独立解析审阅；原代码重放不是这两者的替代品。
本轮在此冻结，不继续扫描更低起点。
