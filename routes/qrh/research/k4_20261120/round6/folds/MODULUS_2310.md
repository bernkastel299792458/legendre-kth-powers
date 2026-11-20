# 在左右边界使用同一个模 2310 的检测函数

在项目 QRH(7/8) 和[已有远端半直线所列解析输入](../../round5/kernel/FINITE_ANCHOR.md)下，五参数、单宽梯形权的分组证明还可改用 \(Q=2310\)。记 \(f_Q=\zeta E_Q C_Q-1\)。每个真实 ζ 零点都有 \(f_Q=-1\)。本节对各个 \(L\) 使用同一个显式公式和开区间权，所有高度与素数幂均计入。

在 \(\Re s=1/2\) 上，任取 \(b=30\) 或 \(210\) 分解 \(1+f_Q=(\zeta E_b)(E_{Q/b}C_Q)\)。[折叠证明](FOLD_MEAN.md)逐项适用，只需将其中的 \(B\) 取为 \(Q/b\)。对 \(a\mid B\)，组的模数仍为 \(ba/g\)，且为 2310 的偶平方自由因子。用包括 11 在内的每个素因子构造 Ramanujan 矩阵，完整周期仍是 \(ba/(2g)\)。短核 \(N=2^{20}\)，二进制算术满足原[短核除数和](../../round5/left/FAST_SHORT.md)的 \(QN<2^{32}\) 约束。\(b=30\) 可用硬截断临界线四阶矩，\(b=210\) 则保留[成对近似函数方程的相位](../phase/SMOOTH_PHASE.md)。后一条使用表 2 对初等乘子版本的余项及第四谐波的完整轮廓估计。[Simonič 的原文](https://arxiv.org/pdf/1910.08274#page=4)

在右纵边，方差与 Mellin 估计使用相同的 \(Q=2310\)。短窗上同时可用单位模 210 和模 2310，在 \(n\ge100T\) 使用大模数统一系数，在低频段核对这两个模数中可用的有限 Gram 界。剩余远尾时间段沿用模 2310 的迹界。脚本逐高度核对 \(1+\lfloor 100/h\rfloor\le e^W\)，以使局部除数和的线性补权有效；全部闭指数格使用相同的参数和 \(Q\)。右外边仍有 \(|f_Q|\le9/\sqrt{Y}\)。Jensen 外圆计入长度 \(QX\)，因而其原常数中用 \(11\sqrt{Qhe^W}\)。[右边界局部二次型](../../round5/mean/RIGHT.md) · [一般平方自由模数的检测器与外圆](../../round4/euler/PROOF.md)

在有限高度窗口以半单位以下的闭格分别核验左常数，用同组对应的右常数以及完整边界项比较候选检测器。在最后一组，未拆短核的左界和全高度右界一直有效。实部弦的正系数和对物理变量 \(L\) 的逐项单调性检查仍按[此前的有限接合](BRIDGE.md)执行。

| 新闭段 | 临界线输入 | 160 位 Arb 的归一化总扣除上界 |
|---|---|---:|
| \([154.1,155]\) | \(b=30,\alpha=1.3\)，硬截断 | .997841702 |
| \([151,155]\) | \(b=210,\alpha=1.25\)，保留第四谐波 | .986970965 |
| \([150,155]\) | \(b=210,\alpha=1.25\)，保留第四谐波并在四次幂层面相加不相交的时间段 | .979624115 |
| \([149.5,150]\) | 同一四阶矩和五组检测参数 | .995685743 |
| \([149,150]\) | \(b=210,\alpha=1\)，直接计入正支与反支乘积的二阶矩 | .999235980 |

前三行分别衔接已证 \(L\ge155\) 的半直线，后两行在 \(L=150\) 接入第三行。末行使用[正反向乘积的直接矩估计与剩余类细分](../phase/MIXED_PRODUCT.md)，平滑宽度为 .04。等积对角上正支的两个参数为单位类，从而反支的乘积权化为非负的 Ramanujan 和平方；非对角再按两个固定外指标模各素因子的比值分类。由此得到 \(n\ge15\,047\,676\,668\,460\,841\) 的逐点条件结论。程序分别比较首个整数和其前一整数与 \(\exp(149/4)\)。下列命令在研究记录目录运行。

~~~sh
python -B round6/folds/fold_bridge.py --modulus 2310 --core 1048576 --anchor 154.1 --last 155 --alpha 1.3
python -B round6/folds/fold_bridge.py --modulus 2310 --core 1048576 --base 210 --method paired --anchor 151 --last 155 --alpha 1.25
python -B round6/folds/fold_bridge.py --modulus 2310 --core 1048576 --base 210 --method disjoint --anchor 150 --last 155 --alpha 1.25
python -B round6/folds/fold_bridge.py --modulus 2310 --core 1048576 --base 210 --method disjoint --anchor 149.5 --last 150 --alpha 1.25
python -B round6/folds/fold_bridge.py --modulus 2310 --core 1048576 --base 210 --method projected --anchor 149 --last 150 --alpha 1
~~~

2026-11-20。项目共同 AI 作者为 Claude、Codex，本节由 Codex 推导与核验。
