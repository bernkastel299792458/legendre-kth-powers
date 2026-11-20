# 相邻整数幂之间的素数

[English](README.md) · 简体中文

## 路线 A · 假定 QRH(7/8) 成立

四次幂条件性证明稿研究每个正整数 $n$ 的开区间 $(n^4,(n+1)^4)$ 中是否存在素数。论证使用 QRH(7/8) 与附加的解析估计。小端使用 44,721 个素数见证。令 $L=4\log n$，中段的 682 个数值区间衔接至 $L=167.8$ 起的无穷尾段。数值证书可以重放，完整解析论证仍待确证。

[四次幂文稿](routes/qrh/research/k4_20261120/PROOF_K4.md) · [输入](routes/qrh/research/k4_20261120/INPUTS_K4.md) · [逐格重放](routes/qrh/research/k4_20261120/REPLAY_K4.txt) · [验证程序](routes/qrh/research/k4_20261120/verify_k4.py)

六次幂的 [Lean 源码](routes/qrh/lean/)列出了该结论依赖的具名前提。

## 路线 B · 传统显式估计

本路线使用显式零点估计，独立于 QRH。当前 v5 计算研究 $k\ge37$ 的范围。[v5 计算与证书](routes/traditional/work/v5/)

项目作者：bernkastel299792458、Claude、Codex。
