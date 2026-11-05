# 对话记录：勒让德猜想与相邻 k 次方之间的素数（k ≥ 67）

*由 Claude 桌面版导出的会话记录自动转换（`export_to_md.py`）。保留用户消息与助手的文字回答；工具调用只保留一行摘要，工具输出与内部思考未保留。原始完整记录见导出的 zip。*

---

## 用户（第 1 轮）

了解一下勒让德猜想

### 助手

# 勒让德猜想（Legendre's Conjecture）

**猜想内容：** 对每个正整数 n，在 n² 和 (n+1)² 之间至少有一个素数。

这个猜想由勒让德在 19 世纪初提出。1912 年，兰道（Landau）在国际数学家大会上把它列为"兰道四大问题"之一，另外三个是哥德巴赫猜想、孪生素数猜想，以及 n²+1 型素数是否有无穷多个。四个问题至今都没有解决。

## 小例子

| n | 区间 (n², (n+1)²) | 其中的素数 |
|---|---|---|
| 1 | (1, 4) | 2, 3 |
| 2 | (4, 9) | 5, 7 |
| 3 | (9, 16) | 11, 13 |
| 10 | (100, 121) | 101, 103, 107, 109, 113 |

## 为什么大家相信它成立

- **启发式估计：** 区间长度是 2n+1。按素数定理，区间里大约有 n / ln n 个素数，这个数随 n 增大而增长，不像会突然变成 0。
- **数值验证：** 素数间隙已经算到 10¹⁸ 以上的量级，所以对 n 到大约 10⁹ 的量级，猜想都已验证成立。

## 已知的最好结果（离目标还差多少）

把猜想换个说法：需要证明在 x 和 x + 2√x 之间总有素数，也就是间隙指数要做到 **1/2**。

| 结果 | 内容 |
|---|---|
| Bertrand–Chebyshev（1852） | n 和 2n 之间必有素数 |
| Ingham（1937） | n 充分大时，n³ 和 (n+1)³ 之间有素数（"立方版"已经解决） |
| Baker–Harman–Pintz（2001） | x 充分大时，[x, x + x^0.525] 中有素数，是目前最好的指数 |
| 陈景润（1975） | n² 和 (n+1)² 之间总有一个 **P₂ 数**（素数，或两个素数的乘积） |

**难点：** 就算假设黎曼猜想成立，也只能得到 O(√x · log x) 的素数间隙，比需要的 √x 多一个 log 因子。所以黎曼猜想也推不出勒让德猜想。

## 相关猜想（都比它更强，成立的话能推出勒让德猜想）

- **Andrica 猜想：** √pₙ₊₁ − √pₙ < 1。推导很直接：如果 n² 和 (n+1)² 之间没有素数，那么跨过这个区间的两个相邻素数，它们的平方根之差就会大于 1，与 Andrica 猜想矛盾。
- **Oppermann 猜想：** (n²−n, n²) 和 (n², n²+n) 两个区间里各有一个素数。
- **Cramér 猜想：** 素数间隙是 O((log p)²)。成立的话，n 充分大时勒让德猜想成立。

如果你在做 AI4Math 相关的工作，我可以帮你写一段 Python 做数值验证，或者给出这个猜想的 Lean 4 形式化陈述。

## 用户（第 2 轮）

我想问问你，勒让德猜想的更高次方版本，目前有没有被证明的，比如立方、四次方等等

### 助手

有。**立方及更高次方的版本，在 n 充分大时都已经证明了**。只有平方（原版勒让德猜想）还没解决。

## 已知结果

| 版本 | 状态 | 出处 |
|---|---|---|
| 平方 k=2 | **未解决** | — |
| 立方 k=3 | n 充分大时成立 | Ingham（1937） |
| 立方，显式下界 | n ≥ e^(e^33.3) 时成立 | Dudek（2016） |
| 立方，改进的下界 | n ≥ e^(e^32.89) 左右时成立 | Cully-Hugill（2023） |
| 立方，假设黎曼猜想 | **对所有 n 成立** | Caldwell–Cheng（2005） |
| k 次方，对所有 n ≥ 1 无条件成立 | 先是 k ≥ 5×10⁹，后来改进到 k ≥ 1438989，再到 **k ≥ 155** | Dudek → Mattner → Cully-Hugill（2023） |

所以要准确地说：
- **立方：** "n 充分大"的版本已经证明了。但 e^(e^33) 这个下界极其巨大，计算机验证不可能覆盖到那里。所以"对所有 n 成立"在无条件的情况下**还没有完全证明**，假设黎曼猜想的话就成立。
- **4 次方到 154 次方：** n 充分大时成立，这由一般性结果直接推出（见下一节）。"对所有 n"同样还差中间一段没覆盖。
- **155 次方及以上：** 对所有 n ≥ 1 都已无条件证明。

上表的具体数值是我凭记忆写的，没有核对。如果要引用，请查原文。

## 为什么平方是分界线

区间 (nᵏ, (n+1)ᵏ) 的长度约为 k·n^(k−1)。记 x = nᵏ，长度就是 k·x^(1−1/k)。

如果能证明"[x, x + x^θ] 中总有素数"，那么只要 1 − 1/k > θ，k 次方版本就在 n 充分大时成立。

- Ingham 的指数是 θ = 5/8 < 2/3，所以够用来处理立方。
- 目前最好的指数是 θ = 0.525（Baker–Harman–Pintz）。
- 平方需要 θ < 1/2。现有方法都做不到这一点，黎曼猜想也只能给出 √x·log x，仍然差一个 log 因子。

## 一个有意思的应用

**Mills 常数**正是建立在立方版本之上：存在常数 A ≈ 1.3064，使得 ⌊A^(3ⁿ)⌋ 对所有 n 都是素数。Mills（1947）的证明依赖"相邻立方之间总有素数"（n 充分大时）。A 的数值是在假设黎曼猜想的前提下算出来的。

## 用户（第 3 轮）

我说的不是n充分大，我说的是对任意n，n充分大没有意义

<details><summary>工具调用摘要</summary>

- *[工具调用 ToolSearch]* select:WebSearch
- *[工具调用 WebSearch]* primes between consecutive powers n^m (n+1)^m all n smallest m Cully-Hugill
- *[工具调用 WebSearch]* "prime between" "(n+1)^" "for all n" consecutive kth powers 2025 2026 arXiv improvement exponent 90
- *[工具调用 ToolSearch]* select:WebFetch
- *[工具调用 WebFetch]*
- *[工具调用 WebFetch]*

</details>

### 助手

按你说的"对所有 n ≥ 1 都成立"来算，**目前无条件证明的最小指数是 k = 86**，出自 2026 年 2 月的一篇 arXiv 预印本。**立方到 85 次方都还没有对所有 n 无条件证明**。我前面的回答漏了这一点，而且当时引用的最好结果 155 已经过时了。

## 无条件、对所有 n ≥ 1 的结果

| 指数 k | 作者 | 时间 |
|---|---|---|
| 5×10⁹ | Dudek | 2016 |
| 约 1.4×10⁶ | Mattner | 2017 |
| 155 | Cully-Hugill（J. Number Theory） | 2023 |
| 140，后来是 90 | Cully-Hugill & Johnston | 2023–2025 |
| **86** | Ethan S. Lee（arXiv 预印本，未见正式发表） | 2026 |

Lee 的这篇文章还对 70 次方证明了一个部分结果，但只对一部分 n 成立，不是全部 n。

这类方法实际证明的是"区间 [x, x + c·x^(1−1/k)] 对所有 x 都含素数"这种更强的形式，所以对 k 成立通常也意味着对更大的指数成立。

**为什么 k 还这么大：** 渐近方法（Ingham、BHP）给出的下界大到 e^(e^33) 这种量级，计算机验证不可能覆盖。要证明"对所有 n"，就得把显式零点自由区域、显式公式的误差项和数值验证拼接起来，而现有的显式估计只有在 k 很大时才能接上。

## 假设黎曼猜想时

- **立方，对所有 n 成立：** Caldwell–Cheng（2005）。
- **更进一步（2026，arXiv:2602.22502）：** 对指数 2+δ（δ ≥ 1/4）和所有实数 x ≥ 1，x^(2+δ) 和 (x+1)^(2+δ) 之间都有素数。所以在黎曼猜想下，3 次方、4 次方等所有整数次方都对全部 n 成立。
- **平方（勒让德猜想本身）：** 即使假设黎曼猜想也没有证明。

Sources:
- [Cully-Hugill, Primes between consecutive powers (arXiv:2107.14468)](https://arxiv.org/abs/2107.14468)
- [J. Number Theory 版本](https://www.sciencedirect.com/science/article/pii/S0022314X23000112)
- [Cully-Hugill & Johnston, On the error term in the explicit formula of Riemann–von Mangoldt (arXiv:2111.10001)](https://arxiv.org/abs/2111.10001)
- [Lee, Minimal zero-free regions for results on primes between consecutive perfect kth powers (arXiv:2602.14340)](https://arxiv.org/abs/2602.14340)
- [Weakening the Legendre Conjecture (arXiv:2602.22502)](https://arxiv.org/abs/2602.22502)

## 用户（第 4 轮）

有没有一种情况是，对于k次方情景，对于足够大的一个确定值n，这个猜想一定成立，我们只要让计算机计算尽可能接近这个数值就能证明整个猜想？
我的直觉是，k越大，这个间隔越宽松，我们需要让计算机来算的数值就更小，能不能找到一个合适的k，我们靠已知上界和计算更高的下界，让两者碰上，就能证明这个命题。你理解我的意思吗？

### 助手

我理解你的意思，而且这正是现在的标准做法。k = 155、90、86 这些结果就是这么证出来的：先用解析方法证明"x ≥ X₀ 时成立"，并把 X₀ 算成一个具体的数，再用计算覆盖 x < X₀，两段碰上就证完了。你的直觉也对：k 越大，X₀ 越小，越容易碰上。

不过有两点和你想的不太一样。

## 1. "计算"那一段其实分两层，不是直接让计算机去找素数

| 层 | 覆盖范围 | 依据 |
|---|---|---|
| ① 直接计算 | x ≤ 4×10¹⁸（log x ≈ 43） | 素数间隙已被穷举到这个范围（Oliveira e Silva 等，2014） |
| ② 显式短区间定理 | log x 到几千 | 依赖计算机验证过的黎曼 ζ 零点（RH 已验证到高度约 3×10¹²，Platt–Trudgian），推出"[x, x(1+1/Δ)] 中必有素数"这类显式结论 |
| ③ 解析定理 | log x ≥ 某个 L(k) 之后 | 显式零点自由区域、零点密度估计，以及显式公式的误差项 |

直接找素数（第①层）基本只能到 10¹⁹ 到 10²⁰，再往上推一个数量级都非常昂贵。真正起作用的是第②层：计算对象是 ζ 函数的零点，而不是素数。比如 k = 140 的情形，第③层从 log x ≥ 4242 开始成立，第②层能覆盖到 log x ≈ 4367，两者刚好重叠，证明就完成了。

## 2. 对小的 k，两段之间的差距不是"算久一点"能补上的

以立方为例，已知的解析下界是 n ≥ e^(e^32.892)：

- 换算成 x = n³，大约是 log x ≈ 6×10¹⁴，也就是 x 有大约 2.5×10¹⁴ 位数字。
- 计算能覆盖到的是 log x 到几千。

两者在对数尺度上还差大约 10¹¹ 倍。素数要一个一个区间去确认，而 x 以下的区间个数本身就是天文数字，所以无论计算机多快都不可能穷举过去。

## 为什么 k 越小，X₀ 涨得越恐怖

区间 (nᵏ, (n+1)ᵏ) 的长度约为 k·x^(1−1/k)。解析方法能保证"长为 x^θ 的区间里有素数"，这里有两个因素：

1. **余量 (1−1/k) − θ：** 对 k = 3，余量是 2/3 减去 Ingham 的 5/8，只剩 1/24。BHP 的 0.525 虽然更好，但它用的是筛法，几乎无法做成显式常数。余量这么小，所有误差项里的常数都会被放大成双指数级的 X₀。k 很大时 1−1/k 接近 1，余量很宽，粗糙的显式估计也够用。
2. **显式常数的质量：** 零点自由区域和零点密度估计的显式版本，常数都很差。Lee 2026 年那篇论文正是在量化这一点：对每个 k ≥ 65，要让两段碰上，零点自由区域至少需要多大。这相当于把"还差多远"精确地算了出来。

## 结论

- **你的思路就是现行方法。** 推动这件事的有三个杠杆：验证更多 ζ 零点（第②层往上延伸），改进显式零点自由区域和零点密度常数（第③层往下压），以及更精细地拼接中间段。三者都在推进，所以 k 从 155 降到了 86。
- **但这条路很难一路降到 k = 3。** 立方的差距是双指数级的，需要理论上的突破，比如把零点密度估计做成很强的显式版本，单靠算力不够。
- **对 k = 2 这条路完全走不通。** 平方的情形没有"x 充分大时成立"这一段：解析方法本身就证不出来，连黎曼猜想都不够，也就没有可以去碰的解析下界。

## 用户（第 5 轮）

那更大的k呢？比如四次方，或者更高？

<details><summary>工具调用摘要</summary>

- *[工具调用 WebFetch]*
- *[工具调用 WebFetch]*
- *[工具调用 WebSearch]* Ethan Lee "consecutive perfect kth powers" zero-free region 86th powers 70th powers Legendre milestones

</details>

### 助手

四次方也**还没有**对所有 n 证明。目前的情况可以按 k 分成三段：

| k | n 充分大时 | 对所有 n ≥ 1（无条件） | 对所有 n（假设黎曼猜想） |
|---|---|---|---|
| 2 | 未证 | 未证 | 未证 |
| 3 到 85 | ✅ 已证（Ingham 1937 起） | ❌ **未证** | ✅ |
| **86 及以上** | ✅ | ✅ **已证**（Lee 2026） | ✅ |

- **"86 及以上"为什么能一次覆盖所有更大的 k：** 这类论文证明的其实是更强的区间形式："对所有 x ≥ 1，[x, x + c·x^(1−1/k)] 中有素数"。对 x ≥ 1，指数 1−1/k′ 随 k′ 增大而增大，更大的 k′ 对应的区间只会更长。所以对 86 成立，就自动对所有更大的指数成立，不需要逐个验证。
- **70 次方：** Lee 只对一部分 n 证明了（某个特定的整数序列），还不是全部 n。
- **4 到 85 次方的具体差距：** 我没找到 k = 4 这类小指数的显式 X₀ 公开数值。Lee 的论文只对 k ≥ 65 计算了"零点自由区域需要多大才能碰上"，这说明更小的 k 目前离得更远，连定量分析都还没人做。4 次方的情况比立方好（余量是 3/4 − 5/8 = 1/8，立方只有 1/24），但我估计仍然是双指数量级的差距。

我没能打开 Lee 论文的全文，以上关于它的内容来自摘要层面的信息。据 ResearchGate 的记录，这篇论文将发表在 Acta Arithmetica（2026 年 10 月）。

Sources:
- [Lee, Minimal zero-free regions for results on primes between consecutive perfect kth powers (arXiv:2602.14340)](https://arxiv.org/abs/2602.14340)
- [Ethan S. Lee 个人主页](https://sites.google.com/view/ethansleemath/home)
- [ResearchGate 条目](https://www.researchgate.net/publication/377361334_Explicit_zero-free_regions_for_the_Riemann_zeta-function)
- [Cully-Hugill & Johnston (arXiv:2111.10001)](https://arxiv.org/abs/2111.10001)
- [Cully-Hugill, Primes between consecutive powers (arXiv:2107.14468)](https://arxiv.org/abs/2107.14468)

## 用户（第 6 轮）

你认为用我思考的这种上下界互相接近的路线，大概最多能筛到k等于多少？你要看论文的，不能光瞎想

<details><summary>工具调用摘要</summary>

- *[工具调用 update_plan]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Read]* C:\Users\BERNKA~1\AppData\Local\Temp\claude\b655f75746a6057d\90b3c2a2-c8b4-40d3-ab12-83d1bb5bc915\scratchpad\papers\2602.14340.txt

</details>

### 助手

Lee 的论文已经读完，信息很关键。再看一下另外几篇对极限的说法。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 wrap_up]*

</details>

## 用户（第 7 轮）

你要考虑两点，一是能不能优化前人的思想，把这个上界打下来，第二个是思考有没有更好的算法，把计算的下界提上去

*（用户在助手工作过程中发送的消息）*

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*

</details>

### 助手

按这几篇论文的数据，这条"上下界对接"的路线**现在做到 k = 86**。如果在零点自由区域上取得有限的改进，**乐观能推到 k ≈ 67–70**。**k ≤ 10 在现有框架里结构上就做不到，立方被论文作者直接称为"futile"（徒劳）**。

你提的两个方向我都按论文核对了。结论是：**缺口几乎只能从解析那一侧（"上界"）来补，计算那一侧（"下界"）很难有实质贡献。**

## 一、两条线现在各在哪里（Lee 2026 的 Table 3 / 5）

| k | 解析方法成立的起点 log x | 计算能覆盖到的 log x | 结果 |
|---|---|---|---|
| 90 | 1997 | 2767 | ✅ 接上 |
| **86** | **2010** | **2640** | ✅ 接上（Lee 的定理） |
| 85 | 5587 | 2609 | ❌ |
| 75 | 5880 | 2292 | ❌ |
| 70 | 15951 | 2135 | ❌ |
| 67 | 238050 | 2040 | ❌ |
| 65 | 4.1×10⁷ | 1977 | ❌ |

- **计算覆盖到的上限**几乎是 k 的线性函数。我从 Lee 的 Prop. 3.3 推出它满足 log x ≲ k·(log k + log Δ)，其中 Δ = 2.52×10¹¹（Cully-Hugill–Lee 的显式区间估计）。用这个式子算 k = 86 得 2640，算 k = 70 得 2135，和表里的数一致。
- **解析起点**在 k ≤ 85 时突然跳高。原因是论文里有一个技术条件：需要参数 θ > 1/k。k ≥ 86 时可以用一组更好的常数（1/85、12.782），k ≤ 85 就用不上了。k 继续往下，起点一路恶化。

## 二、方向 1：改进前人方法，把解析起点压下来

Lee 把方法拆成三个部件，并逐个评估了改进空间：

1. **显式公式的误差项：** Lee 原话的意思是"现有结果已经相当尖锐，只剩常数上的小修小补"。**这里空间很小。**
2. **零点自由区域：** **这是主要杠杆。** 零点自由区域的形式是 σ ≥ 1 − log log t /(Z log t)，常数 Z 越小区域越大。目前已证的是 Z = 19.62（Yang 2025）。Lee 的 Theorem 1.4 算出了每个 k 需要的 Z，而且**只需要在有限高度内成立**：

   | k | 需要 Z ≤ | 只需在高度 t ≤ … 范围内成立 |
   |---|---|---|
   | 85 | 17.27 | e^75.9 |
   | 70 | 14.06 | e^264 |
   | 67 | 13.41 | e^4121 |
   | 66 | 13.20 | **e^691820** |

   在 67 和 66 之间有一个断崖，这就是我说"极限约 67"的依据。Lee 认为 k = 70 的要求"看起来合理"，是一个重要里程碑。

   我自己的判断：e^264 远远超出直接数值验证零点的能力（黎曼猜想目前只验证到高度 3×10¹² ≈ e^28.7）。所以这一步要靠理论，也就是对中等高度的 ζ 函数给出更好的显式上界，进而得到更好的零点自由区域常数，而不是靠算。

3. **零点密度估计 N(σ, T)：** Lee 用了"组合多个密度估计"的技巧，改进了 67 ≤ k ≤ 85 的结果。他明确指出，如果能证明在 T ≤ e^80 范围内形状合适的更强显式密度估计，还能继续往下推。

**还有两个结构性的墙：**

- **k ≤ 10：** 他们所用的截断显式公式要求 T < x^(1/10)，同时又需要 θ > 1/k，所以 k ≤ 10 在这个框架里根本无法设置参数。要突破，就得把显式公式的有效范围扩大。Cully-Hugill–Johnston 指出这个范围在理论上最多扩到 1/2。
- **立方：** Johnston 等（2026）明确说，把 Ingham 的论证做成显式"appears futile"。要做立方，需要换工具：做出 **Harman 素数探测筛法**或 **Iwaniec 线性筛（带 well-factorable 余项）**的显式版本。他们指出这两者文献中都没有。这才是"改进前人思想"里真正需要原创的部分。

## 三、方向 2：用更好的算法把计算覆盖范围提上去

**直接找素数这条路：** 目前最好的算法是 Sorenson–Webster 的方法，Johnston 等把它推广到了立方。它依赖 BLS 素性证明、在算术级数里筛选，并且把很多区间放在一起批处理。在 Cramér 模型下，验证到 n ≤ N 需要 O(N log N log log N) 时间，已经接近线性，因为每个区间至少要给出一个素数证书。这个算法要求指数 α > 3/2，所以不能用于平方以下的情形。立方做到了 n ≤ 2.55×10¹³，花了约 41.5 万核时。

**用它去补 k 次方的缺口为什么无效（下面是我自己算的）：** 验证到 n ≤ N，只能覆盖到 log x = k·log N。要接上解析起点，需要 N = exp(起点/k)：
- k = 85：N ≈ e^65.7 ≈ 3×10²⁸，是现有能力的 10¹⁵ 倍。
- k = 70：N ≈ e^228 ≈ 10⁹⁹。

而且 k 越大，每个区间里的数位数越多，单次素性证明更贵。

**用解析区间估计（提高 Δ）这条路：** 覆盖上限是 k·(log k + log Δ)，Δ 只以对数的形式进入。k = 85 要接上，需要 log Δ ≈ 61，也就是 Δ ≈ 10²⁶，而现在是 2.5×10¹¹。我推测 Δ 受已验证黎曼猜想的高度限制，这一点论文里没有直接写。如果是这样，就需要把黎曼猜想验证到大约 10²⁶ 量级的高度，不现实。

**立方的对比：** 计算做到了 log n ≈ 31，解析起点在 log n ≈ e^32.5 ≈ 1.3×10¹⁴，差距是 10¹² 倍以上，而且这还是对数尺度上的差距。

## 结论

两侧的增长速度不对称：计算侧的覆盖范围随 k 只是线性增长，对算力和 Δ 都只是对数级的依赖；解析起点却随 k 减小急剧爆炸。所以接点几乎完全由解析侧决定。

我的估计：
- 优化现有思想（主要是中等高度的零点自由区域和零点密度估计）大约能推到 **k ≈ 70，最多到 67 左右**。
- k ≤ 10 需要新的显式公式。
- 立方需要**显式筛法**这一新工具。
- 平方即使假设黎曼猜想也做不到。

Sources:
- [Lee, Minimal zero-free regions for results on primes between consecutive perfect kth powers (arXiv:2602.14340)](https://arxiv.org/abs/2602.14340)
- [Johnston, Sorenson, Thomas, Webster, Primes and almost primes between cubes (arXiv:2601.15564)](https://arxiv.org/abs/2601.15564)
- [Visser, Effective short intervals containing primes (arXiv:2508.18786)](https://arxiv.org/abs/2508.18786)
- [Cully-Hugill & Johnston, On the error term in the explicit formula of Riemann–von Mangoldt (arXiv:2111.10001)](https://arxiv.org/abs/2111.10001)
- [Cully-Hugill, Primes between consecutive powers (arXiv:2107.14468)](https://arxiv.org/abs/2107.14468)

## 用户（第 8 轮）

那你觉得”沿着k逐渐减小一级一级找解法“，最终逼近立方甚至平方，这个思路对吗？还是应该直接做平方或者立方问题

### 助手

我认为这个思路**不对**。沿着 k 一级一级往下走，到不了立方，更到不了平方。原因是一路上遇到的障碍会**换种类**，而不只是变难：每过一道墙都需要一种新工具，而攻克大 k 的那些技巧对下一道墙几乎没有帮助。

## 为什么"逐级下降"走不通

| 区间 | 卡住的地方 | 需要的东西 |
|---|---|---|
| 86 → 约 67 | 零点自由区域、零点密度估计的显式常数 | 常数优化，属于"工程性"改进 |
| 66 附近 | 需要的零点自由区域高度从 e^4121 跳到 e^691820，是断崖 | 零点估计的形状要变好，不只是常数 |
| ≤ 10 | 截断显式公式只在 T < x^(1/10) 内有效，参数无解 | 新的显式公式（理论上限是 x^(1/2)） |
| 3（立方） | ζ 函数路线被作者称为"futile" | **显式的 Harman 筛法或 Iwaniec 线性筛**，文献中都还没有 |
| 2（平方） | 黎曼猜想也不够，还差一个 log 因子 | 超越黎曼猜想的素数间隙理论 |

另外，k 的进展本身也在收敛：155 → 140 → 90 → 86，靠的都是常数上的精修，每一步推进越来越小。证明了 k = 70，对 k = 69 也没有直接帮助，能传递下去的只有改进后的"部件"。

## 更好的做法：按"工具"或"瓶颈"选题，而不是按 k

**1. 做立方：直接攻克真正的瓶颈。**
- 核心是把 Harman 筛法（或 Baker–Harman–Pintz 那一类素数探测筛法）做成显式版本。这很难，但它是通向立方唯一被点名的路，Johnston 等 2026 年的论文明确说了需要它。
- 计算侧的配套：cubes 已经验证到 n ≤ 2.55×10¹³。一旦显式筛法给出的起点落到可计算范围内，两侧就能接上。

**2. 逼近平方：换一个梯子，按 Ω（素因子个数）往下走。**
- 已知结果：平方之间总有 Ω ≤ 4 的数，对所有 n 成立（Dudek–Johnston）；立方之间总有 Ω ≤ 2 的数，对所有 n 成立（Johnston 等，2026）；陈景润证明了 n 充分大时平方之间有 P₂ 数。
- 所以"平方之间 Ω ≤ 3，再到 Ω ≤ 2，对所有 n 成立"是一条直接朝向勒让德猜想、而且可以操作的梯子。
- 但这个梯子在 Ω = 2 处会停下：这就是筛法的**奇偶性障碍**（Selberg），纯筛法无法区分素数和 Ω = 1 以外的情况。要越过它，又得回到 Harman 那类引入双线性型的方法。

**3. 有条件的路线：按实数指数往下走。**
- 假设黎曼猜想，已经知道指数 2 + δ（δ ≥ 1/4）对所有 x 成立（arXiv:2602.22502）。把 δ 往 0 推、并给出显式结果，是一条清晰的条件性梯子。

**4. 直接做平方：** 我不建议把它当作项目，除非目标就是突破级别的工作。它比黎曼猜想还强，目前没有任何已知路线。

## 建议

- **想要可发表、可落地的进展：** 做 k ≈ 70 这一类目标。Lee 已经把需要的零点自由区域常数算出来了，目标非常明确。这类工作的形式是显式不等式、参数搜索和大量验证，很适合用 AI 或 Lean 做自动化。但要清楚，它不会通向立方。
- **想真正接近勒让德猜想：** 做"显式筛法"（为立方做准备），或者"平方之间的 Ω 梯子"。这两条是直接朝向目标的路。

## 用户（第 9 轮）

可以，那你在本地路径下留下科研路线和日志，尝试一下攻克k=67的勒让德猜想

### 助手

先搭好研究目录，再复现 Lee 的计算框架，然后在这个框架里找能把 k=67 缺口补上的改进点。

<details><summary>工具调用摘要</summary>

- *[工具调用 update_plan]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Read]* D:\UGit\AI4Math\legendre_k67\code\lee_code\code.py
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\LOG.md
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\code\bound.py
- *[工具调用 Bash]*

</details>

### 助手

复现成功：在 Lee 给出的 c 值下，δ 恰好在他报告的阈值处越过 1。修一个溢出问题后继续。

<details><summary>工具调用摘要</summary>

- *[工具调用 Edit]* D:\UGit\AI4Math\legendre_k67\code\bound.py
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

等后台计算的同时，先把目前的结果写进日志。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\ROADMAP.md
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 wrap_up]*

</details>

### 助手

**k=67 还没有攻克。** 我把缺口从 2041 < L < 238050 缩小到了 2041 < L < 约 7000（L = log x），并把剩下的缺口精确地归结为一个具体的零点分布问题。所有数值都是浮点计算，还没有用区间算术严格化。

## 取得的进展

**1. 复现了 Lee 的结果。** 用我重写的程序，代入 Lee 的参数，在 k = 67、70、85、86、90 上都在他报告的阈值处越过 1。

**2. 找到一个改进，效果很大。**
- 读 Lee 的代码时发现，他的两种零点密度估计（KLN 和 Bellotti）是分开用的。
- 用 Bellotti 版本时，β < 0.985 的零点只能做平凡估计，这一项把参数卡死了。
- 我把两种估计在同一个积分里分段使用：σ 较小的部分用 KLN，σ 接近 1 的部分用 Bellotti。两者都是同一个量的上界，所以分段使用是合法的。

| k | 下段（计算侧）上限 | Lee 的解析起点 | 改进后的解析起点 |
|---|---|---|---|
| 70 | 2135 | 15 951 | 5950 |
| **67** | **2041** | **238 050** | **约 7000** |
| 65 | 1978 | 41 432 145 | 7900 |

k ≤ 72 时改进了 1 到 4 个数量级，但没有任何 k < 86 能因此闭合。

**3. 精确诊断了剩下的缺口。** 瓶颈在于高度 e^29 到 e^110 范围内 ζ 函数零点的分布信息。

## 你提的两个杠杆

**把计算侧推上去：** 要闭合缺口，需要把黎曼猜想验证到约 10^45.6，而目前只到 10^12.5。这条路行不通。

**把解析侧压下来：** 有三条具体目标，任何一条做到都能闭合缺口。
- **光滑化显式公式：** 在理想模型下，缺口缩到 2041 < L < 约 5300。
- **中等高度的零点自由区域：** 在光滑化的前提下，只需在高度 e^30–e^75 上把 Littlewood 常数从 19.62 改进到约 16.5，差距约 16%。Lee 原来的要求是常数 13.4，而且高度要到 e^4121。
- **中等高度的 log-free 零点密度估计：** 需要常数 C 约为 1.7×10⁴，Bellotti 现有的是 3.7×10⁵，差约 22 倍。

## 文件

- [ROADMAP.md](ROADMAP.md)：科研路线图，包括路线 A–D 的定量目标和下一步清单
- [LOG.md](LOG.md)：研究日志
- [code/bound.py](code/bound.py)：上界计算核心，带三种模式；其他脚本都在 `code/` 下
- [results/](results/)：扫描数据
- `papers/`：6 篇论文的 PDF 和提取的文本
- `code/lee_code/`：Lee 的原始代码

`code/req_density.py` 是一个有 bug 的早期版本，已经被 `code/req_density2.py` 取代。

拼接改进本身如果严格化，就能改进 Lee 论文中的 Table 3 和 Theorem 1.4，可以单独写成一篇短文。

## 用户（第 10 轮）

先严格化然后落档，接着继续研究光滑化

### 助手

先做严格化。我用 arb 球算术重写上界，对 L 做连续区间的覆盖（而不只是取网格点），并逐条检查命题的前提条件。

<details><summary>工具调用摘要</summary>

- *[工具调用 update_plan]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\code\rigorous_hyb.py
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

严格版本与浮点结果吻合，整段上界只比单点值略大一点。现在对 k=67 从 L=238050 向下做完整覆盖。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

全部 21 个 k 都通过了严格验证。下面用检查器对所有证书做复核：逐段重算上界，并确认各段之间首尾相接、没有缝隙。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

条件证书全部通过复核，但每个 k 的最大 δ 都只有约 0.29，这说明二分搜索找到的 z 并不是被 δ 卡住的。可能有某个前提条件在暗中起作用，查一下。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Read]* D:\UGit\AI4Math\legendre_k67\code\rigorous_hyb.py
- *[工具调用 Edit]* D:\UGit\AI4Math\legendre_k67\code\rigorous_hyb.py
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

低高度那一轮没有起作用，结果没变。直接查一下 k=85 窗口顶端的情况。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

## 用户（第 11 轮）

这个arb这么难安装吗？我可以帮你吗？

<details><summary>工具调用摘要</summary>

- *[工具调用 update_plan]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\docs\HYB_theorem.md

</details>

### 助手

定理文档已经写好，Theorem B 里 k=75 和 67 两格等后台算完再补。等待期间开始做光滑化：先写推导和浮点实现。

<details><summary>工具调用摘要</summary>

- *[工具调用 update_plan]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\code\smooth.py
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\docs\smoothing.md
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\code\rigorous_smooth.py
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

`rigorous_hyb` 里的写法都是同一个 Fraction 的分子除以它自己的分母，是正确的，所以 Theorem A 和 B 不受影响。重新测试严格光滑化：

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 WebSearch]* Bellotti "explicit log-free zero density estimate" Riemann zeta arXiv
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

严格覆盖推进到 L = 3191.31 时卡住了，那里 δ 恰好碰到 1。浮点采样之前跳过了这一点。在附近细扫看看：

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

覆盖检查里有一处不够严格：判断格子左端是否被覆盖时，应该用行下界 T0 的**上**端点，而不是下端点。改掉后重跑。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Read]* D:\UGit\AI4Math\legendre_k67\papers\2405.12545.pdf

</details>

### 助手

没有 PDF 渲染工具，改用第二种独立的提取方式（pypdf）重新读取 Table 2，再和我录入的数字逐项比对。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

HTML 版本取自 LaTeX 源码，里面的数值与我录入的完全一致。再用程序逐项比对一遍，并查看证书复核的结果：

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*

</details>

### 助手

22 行全部一致。证书复核在后台还没跑完，我改为在前台重跑一遍：

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 WebSearch]* Andrew Yang thesis "explicit zero-free regions for the Riemann zeta-function" UNSW 2025 4.862 19.62
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\docs\k67_theorem.md
- *[工具调用 Edit]* D:\UGit\AI4Math\legendre_k67\docs\HYB_theorem.md
- *[工具调用 Edit]* D:\UGit\AI4Math\legendre_k67\docs\HYB_theorem.md
- *[工具调用 Edit]* D:\UGit\AI4Math\legendre_k67\docs\smoothing.md
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\ROADMAP.md
- *[工具调用 Bash]*

</details>

### 助手

正在收尾：记录记忆并给出总结。

<details><summary>工具调用摘要</summary>

- *[工具调用 Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\research-grounded-in-papers.md
- *[工具调用 Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\legendre-k67-project.md
- *[工具调用 Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\MEMORY.md
- *[工具调用 wrap_up]*

</details>

### 助手

**k=67 的缺口闭合了：** 我得到了一个计算机辅助证明，**对所有 k ≥ 67 和所有 n ≥ 1，(n^k, (n+1)^k) 中都有素数**。此前已知的最好结果是 k ≥ 86（Lee 2026）。所有证书都用 arb 球算术严格验证并复核过，但这个结论还没有经过人工审阅，而且依赖 Yang 博士论文中的 Littlewood 常数 19.62。Lee 的 k=86 定理也依赖它。如果只用已正式发表的常数 21.233，缺口闭合不了。

另外回答你中途的问题：arb 一条 `pip install` 就装好了，不需要帮忙。慢的是某些计算本身。

## 1. 严格化与落档（HYB 方法）
- 拼接 KLN 和 Bellotti 两种零点密度估计的方法，已经用球算术对连续的 L 区间做了严格覆盖，生成了 21 份证书（k = 65…85），全部通过独立复核。
- 严格阈值：k=67 的解析起点从 Lee 的 238050 降到 6989.94，k=65、66 从约 4×10⁷ 降到约 8000。
- 改进了 Lee 的 Theorem 1.4（条件性零点自由区域）。k=67 所需的零点高度从 e^4121 降到 e^108.8，所需常数基本不变。

## 2. 光滑化研究
- 用光滑权代替尖锐截断，推导出显式上界，然后做成严格版本。
- 只用 Lee 引用的那部分 Bellotti 表，k=67 的缺口缩到 (2343.8, 5535.3)，还不能闭合。
- **关键发现：** Bellotti 的密度估计表其实从高度 3×10¹² 就开始，Lee 只引用了 e^80 以上的行。低高度这 22 行在 Lee 的框架里用不上，但配合拼接方法就能用。我用两种独立来源逐项核对了这 22 行的数值。
- 三样东西合在一起（拼接 + 光滑化 + 完整表），k=67 的整个缺口被 1241 段证书覆盖，最大 δ = 0.937。
- k=66、65 用这个方法闭合不了，所以在现有输入下 67 正好是这个方法的极限。

## 3. 发现并修复的 bug
开发过程中发现了几个 bug，都已修复，所有受影响的结果都已重算并复核：
- 条件版在 KLN 模式下漏算了一段零点积分（之前的条件结果作废并重算）；
- 分数转换时分子分母不匹配；
- 尾部截断点取得太小；
- 跨越 Bellotti 表分界点的格子退回到了很大的上界。

## 4. 尚待审阅的事项
详见 `docs/k67_theorem.md` §6：
- 19.62 这个常数尚未正式发表；
- 光滑显式公式需要给出正式引用或完整证明；
- Lee 的 Prop 3.2 和 3.3 是直接引用的，没有严格重做；
- 最好有人用另一套实现独立复算证书。

## 文件
- [docs/k67_theorem.md](docs/k67_theorem.md)：主定理、证明结构、输入清单、复核方法
- [docs/HYB_theorem.md](docs/HYB_theorem.md)、[docs/smoothing.md](docs/smoothing.md)：两个新命题及证明
- [ROADMAP.md](ROADMAP.md)、[LOG.md](LOG.md)：路线图与研究日志
- `results/`：证书；复核命令写在主定理文档里

Sources:
- [Lee, arXiv:2602.14340](https://arxiv.org/abs/2602.14340)
- [Bellotti, arXiv:2405.12545](https://arxiv.org/abs/2405.12545)
- [Bellotti–Trudgian–Yang, arXiv:2603.21490](https://arxiv.org/abs/2603.21490)
- [Mossinghoff–Trudgian–Yang, arXiv:2212.06867](https://arxiv.org/abs/2212.06867)
- [Yang, arXiv:2301.03165](https://ar5iv.labs.arxiv.org/html/2301.03165)
- [Cully-Hugill–Johnston, arXiv:2111.10001](https://arxiv.org/abs/2111.10001)
- [Visser, arXiv:2508.18786](https://arxiv.org/abs/2508.18786)
- [Johnston 等, arXiv:2601.15564](https://arxiv.org/abs/2601.15564)

## 用户（第 12 轮）

你，真的证明出来了？

### 助手

不能这么说。准确的说法是：我得到了一个**候选证明**。推理链条是完整的，数值部分也经过了严格验证，但它离数学界认可的"证明"还差几道关。在这些关过完之前，不应该对外宣称"证明了 67"。

## 已经做到的
- **证明链条完整：** 四段区间首尾精确相接，覆盖所有 x ≥ 4×10¹⁸。中间两段由我的证书覆盖，两端引用 Lee 的命题。
- **数值部分是严格的：** 用的是 arb 球算术，对 L 的连续区间做覆盖，而不是取网格点抽样。所有证书都经过独立复核器重算。
- **有几项一致性检查：** 程序能逐位复现 Lee 的全部阈值；严格值和浮点值相互吻合；改进幅度有清楚的来源，主要是 Lee 没用 Bellotti 表的低高度行。

## 可能出错的地方（按风险从高到低）
1. **我自己的两个新命题（拼接密度估计、光滑化上界）只有我自己检查过。** 每一步看起来都是标准论证，但还没有数论专家审阅过。
2. **代码可能还有 bug。** 这一轮我就发现并修复了 4 个。其中一个曾让条件版的结果全部作废。这说明出错的概率并不低。
3. **有些输入常数是从 Lee 的论文转引的。** KLN 的 17.253、5.663，显式公式的 1.26，ψ−θ 的界，我没有逐一回到原始论文去核对。只有 Bellotti 的表是我自己对照原文核对过的。
4. **结论依赖一个未正式发表的常数。** Yang 博士论文中的 19.62 只被作者本人在 2026 年的 arXiv 论文里引用过。换成已发表的 21.233，缺口就闭合不了。
5. **Lee 的 Prop 3.2 和 3.3 是直接引用的。** 他自己的代码只在阈值点做了检查，而且有精度设置的 bug。

## 要变成真正的证明，还需要
- 请一位做显式解析数论的人审阅 `docs/k67_theorem.md` 里的两个命题；
- 把每个输入常数都回到原始论文核对一遍；
- 用另一套实现独立重算证书；
- 做几项已知答案的检验。比如用同一套机器去重新推出 Cully-Hugill–Lee 的区间估计常数 Δ：如果算出的结果明显好得离谱，就说明哪里有错；
- 等 19.62 正式发表，或者向作者确认。

我自己的判断：这个结果**有相当可能是对的**。思路站得住，因为这两个技巧都是标准方法，Lee 的框架又恰好用不上那些低高度的表行。但"有相当可能"离"已证明"还很远。我建议先把上面几项做完，再考虑写成论文或联系 Lee、Bellotti 等作者。

## 用户（第 13 轮）

你这样，你先把你的成果写成方便人类审查的文档，把各项条件标清楚，参考引用标清楚，然后走一下lean形式化证明，把这份东西归档到一个"proof"的子文件夹里，我要让其他数学专家和其他审查AI来审查这个结果。

### 助手

我分三块来做：
1. 一份方便审查的手稿：每个前提都编号、标明来源和核实状态，引用写全。
2. Lean 形式化。
3. 把证书、代码和一键复核脚本一起归档到 `proof/` 文件夹。

先看一下本机有没有 Lean 和 TeX。

<details><summary>工具调用摘要</summary>

- *[工具调用 update_plan]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

Lean 4.35.0 已装好。接下来建立依赖 Mathlib 的 Lake 项目，并在后台下载 Mathlib 的预编译缓存。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Agent]* Verify density/counting inputs
- *[工具调用 Agent]* Verify explicit-formula inputs
- *[工具调用 Agent]* Verify zero-free regions, Lee Prop 3.2

</details>

### 助手

三个核对代理已经在后台运行。现在开始 Lean 部分，先确认模板项目能编译，再看一下 Mathlib 里有没有现成的 Chebyshev θ 函数和分部求和引理可以用。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\LegendreK67\LegendreK67\Reduction.lean
- *[工具调用 Bash]*

</details>

### 助手

归约部分一次编译通过，只有一个无害的 linter 警告。接下来写 θ ⇒ 素数、区间拼装、Abel 求和和组合引理。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

改名失败了：Lean 目录正被占用，后面的复制步骤也因此没执行。Lean 项目就保留原名 `proof/LegendreK67`，重新复制文件。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\manuscript.md

</details>

### 助手

手稿主体已写完。等待核对报告期间，先写审查清单和入口 README。

<details><summary>工具调用摘要</summary>

- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\REVIEW_CHECKLIST.md

</details>

### 助手

清单 E2 里提到的"会不会证明太多"，我自己先跑一下：用同一套光滑化代码去算小的 k，预期应该失败。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

归档目录里的一键复核全部通过。再修一下健全性测试：k=3 时下段上限只有 L ≈ 82，低于 (I7) 要求的 log x ≥ 300，所以要从 300 开始取样。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\README.md
- *[工具调用 Bash]*

</details>

### 助手

纯 arb 版本和原版本相差约 3×10⁻⁹（相对误差）。数值上无关紧要，但这比原版本预留的 10⁻¹² 安全系数大得多，必须查清楚来源。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

等待期间更新研究日志。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

手稿、审查清单、Lean 形式化和证书都已归档到 `proof/`。现在在等三个文献核对代理的报告，以及两项后台复核（纯 arb 模式和最新代码的一键复核）。结果回来后，我会把核实状态填进手稿 §3.1，再做最后的汇总。

第一份核对报告（显式公式部分）回来了，有一处需要修正：

- **T\* 的问题已确认没问题：** CHJ II 推论 3.3 是直接对差值 ψ(x+h) − ψ(x) 做的论证，x 与 x+h 用的是同一个 T*。
- **发现 Lee 的转述有误：** CHJ II 实际要求 T > max{51, (log x)²}，而 Lee 写成了 2T > max{51, log x}，条件弱得多。在我们用到的范围里这个更强的条件都成立，余量很大，但我的严格检查代码里沿用了 Lee 的弱条件，必须改成原文的条件，然后重新复核证书。
- 其余输入：(3.4) 通过 BKLNW 得到确认；Costa Pereira 的原文无法访问，但下界可以用 BKLNW 独立推出。CHL 的 14 对 (Δ, x₀) 与修正版一致。Lee Prop 3.3 证明中有一个写错的不等式，不过对 k=67，两对参数就足够了。

先保存报告，再修代码。

<details><summary>工具调用摘要</summary>

- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\input_verification\report_explicit.md
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\input_verification\report_density.md
- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\code\tail.py
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

之前那次改动没写进去，要么是目标字符串没匹配上，要么是因为整条命令转入了后台。直接看文件：

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*

</details>

### 助手

原因是那条命令开头误写了一个 `cat > /dev/null`，它一直在等待标准输入，后面的步骤全都没执行。先停掉这个卡住的后台任务，再重新应用修改。

<details><summary>工具调用摘要</summary>

- *[工具调用 ToolSearch]* select:TaskStop
- *[工具调用 TaskStop]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

Lean 编译通过，所有定理仍然只依赖三个标准公理。下面用 arb 验证 Lean 中用到的两个数值事实，并查看纯 arb 复核的结果。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Bash]*

</details>

### 助手

`tail.py` 和 `numeric_facts.py` 在检查失败时还不会返回非零退出码，这样一键脚本发现不了失败。补上之后再启动完整复核。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*

</details>

### 助手

趁完整复核在后台运行，先保存第三份核对报告，再重写手稿。

<details><summary>工具调用摘要</summary>

- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\input_verification\report_zfr_lee32.md

</details>

### 助手

先快速补算一个数据：只用已发表常数、配合修正后的 KLN 常数时，光滑化在几个采样点上的 δ。手稿的敏感性一节要用到。

<details><summary>工具调用摘要</summary>

- *[工具调用 Bash]*
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\manuscript.md

</details>

### 助手

手稿 v2 写好了。接着更新审查清单和 README，让它们和 v2 的结构一致。

<details><summary>工具调用摘要</summary>

- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\REVIEW_CHECKLIST.md
- *[工具调用 Write]* D:\UGit\AI4Math\legendre_k67\proof\README.md
- *[工具调用 Bash]*
- *[工具调用 Bash]*
- *[工具调用 Edit]* D:\UGit\AI4Math\legendre_k67\ROADMAP.md
- *[工具调用 Bash]*

</details>

### 助手

Update the project memory, then wrap up.

<details><summary>工具调用摘要</summary>

- *[工具调用 Write]* C:\Users\Bernkastel\.claude\projects\D--UGit-AI4Math\memory\legendre-k67-project.md
- *[工具调用 wrap_up]*

</details>

### 助手

审查包已经归档到 [proof/](proof/README.md)，可以交给专家和审查 AI 了。

这次回到原始文献逐条核对输入，发现 Lee 转述的输入有 4 处问题。修正并全部重算之后，k=67 的论证**仍然成立**：在归档目录里一键复核，结果为 `ALL CHECKS PASSED`。

## 核对中发现的问题，以及 v2 的修正
1. **密度估计常数不可靠（影响最大）。** Lee 引用的 KLN 常数 17.253/5.663 依赖一个已被指出"不可靠"的界。我改用 Johnston–Yang 2023 的修正值 17.418/2.231，这组值只覆盖 σ ≥ 0.98，所以把 σ₁ 改成了 0.98，然后所有证书重新生成。
2. **显式公式的适用条件被写错。** 原文要求 T > max{51, log²x}，Lee 写成了一个弱得多的条件。代码现在检查原文的条件。
3. **Lee Prop 3.3 的证明中有一步不等式不成立。** 下段改为直接从 Cully-Hugill–Lee 的区间估计推出，这一推导已在 Lean 中形式化。
4. **Lee Prop 3.2 没有给出单调性论证。** 我改用自己证明的尾部引理（log x ≥ 10⁸）：只用已发表的零点自由区域，并在 arb 中验证了单调性条件。

现在整个证明不再引用 Lee 的 Prop 3.2 和 3.3。

## 必须写清楚的依赖
结论依赖两个**还没有经过同行评审**的常数：
- **19.62**：Yang 博士论文，可公开获取；
- **4.896**：Bellotti–Trudgian–Yang，arXiv:2603.21490。

去掉其中任何一个，方法都闭合不了，手稿 §11 给出了具体数据。其余输入都已正式发表，并对照原文核对过。

## Lean 形式化
- **已证明，没有 sorry：** 归约到所有 k ≥ 67、θ 增量为正与素数存在的等价、下段推导、四段拼装、数值积分用到的 Abel 求和不等式、两个命题的组合步骤。公理审计只列出 Lean 的三个标准公理。
- **以假设字段进入、没有在 Lean 里证明：** 解析数论输入（零点密度、零点自由区域、显式公式）和 arb 数值证书。目前 Mathlib 还没有这部分理论，所以这些需要人工审查。

## 怎么用
- 入口是 [proof/README.md](proof/README.md)，主手稿是 [proof/manuscript.md](proof/manuscript.md)（英文，方便国际审稿）。
- 审查清单 [proof/REVIEW_CHECKLIST.md](proof/REVIEW_CHECKLIST.md) 按风险排序，可以直接发给审查方。
- 复核方法：在 `proof/code` 下运行 `python verify_all.py`，约 10 分钟；Lean 部分在 `proof/LegendreK67` 下运行 `lake build`。
- 分享时不要包含 `LegendreK67/.lake`（约 5 GB），对方用 `lake exe cache get` 自己下载即可。

`docs/HYB_theorem.md` 里 k ≠ 67 的旧结果用的仍是那组有问题的 KLN 常数，已经标注了需要重算，但不影响 k=67 的审查包。

## 用户（第 14 轮）

你可以把勒让德猜想这个主对话可以导出一份md文件，然后写个脚本或者另开一个窗口把我们的对话翻译成英文，准备一起传上去吗？

### 助手

先导出对话记录，再开一个新会话把它翻译成英文。

<details><summary>工具调用摘要</summary>

- *[工具调用 ToolSearch]* select:mcp__ccd_session_mgmt__export_transcript,mcp__ccd_session__start_session

</details>

