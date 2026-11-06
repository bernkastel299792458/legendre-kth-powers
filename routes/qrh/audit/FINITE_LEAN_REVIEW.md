# 有限数据与小范围素数的 Lean 内核验证

日期：2026-11-06。环境固定为 `leanprover/lean4:v4.36.0-rc2` 及同版 Mathlib。

本报告记录已实际编译通过的有限部分。**它不声称已经完成从 QRH、CS v2 到全部正整数结论的端到端形式化。** 特别地，有理上界数据的核验与这些数确实包围解析误差表达式，是两项不同义务。

## 1. 1259 个素数见证已由内核证明

主定理位于 [PrimeWitnesses.lean](../lean/LegendreK6/PrimeWitnesses.lean)：

```lean
theorem small_range_prime (n : ℕ) (hn : 1 ≤ n) (hmax : n ≤ 1259) :
  NatSixthShort n
```

其中 `NatSixthShort n` 明确定义为存在自然数素数 `p`，满足严格整数不等式
`n^6 < p ∧ p < n^6 + 6*n^5`。这个定理没有额外素性假设。

生成器从保存的1259个见证出发，对每个 `p-1` 完全分解，并递归处理分解中的素因子，共得到 **5349 个素数节点**。正式证明分成27个 `Pratt/Block000.lean` 至 `Block026.lean` 文件，全部编译通过。对小于1000的节点使用 `norm_num` 的试除证明；其余节点使用 Mathlib 的 `lucas_primality`：给出模 `p` 下阶为 `p-1` 的元素，检查全部素因子对应的幂不等于1。

`reduce_mod_char` 为模幂生成证明项，最终算术由 Lean 内核检查。各个 `p-1` 的乘法分解和严格区间不等式也在 Lean 中证明。未使用 `native_decide`，未把 Python/FLINT 的素性返回值作为公理，没有 `sorry` 或 `admit`。Python和FLINT仅搜索与生成候选数据；错误候选不能绕过内核。

这部分因此不再依赖 Sorenson–Webster 的有限基定理。原计算辅助证明引用该定理，公开包中的 Lean 小范围结果提供了另一套实际完成的素性证明。

## 2. 有理证书的有限逻辑检查

[CertificateData.lean](../lean/LegendreK6/CertificateData.lean)逐字读取冻结 JSON 中的有理端点和向上界。[Certificates.lean](../lean/LegendreK6/Certificates.lean)已实际内核证明：

- 新中段恰有94格，正宽闭区间精确衔接，从167覆盖到400。
- 旧多项式段恰有60格，精确衔接，从400覆盖到700。
- `refined_real_coverage`、`polynomial_real_coverage`保证这些闭单元覆盖区间内**每个实数**；不是采样点覆盖。
- 新94格保存的有理上界均小于47/50，且不超过论文所列最坏有理数。
- 三列CS系数放大6%后保存的94个有理上界均小于1，且不超过论文所列放大后的最坏有理数。
- 旧60格上界整体乘53/50后仍小于1；尾部粗界满足 `(53/50)*(14/25)=371/625<1`。
- 精确认证余量的有理恒等式成立。
- CHL转换得到的12行整数端点构成从1259之后连续覆盖至1242317999994的链。

这里没有将 JSON 的 `passed=true` 当作证据；Lean重新计算精确有理比较、列表长度及连接关系。CHL源阈值的超越函数不等式由另外的 `Thresholds.lean`处理，不隐藏在本列表检查里。

**尚未由这些模块证明的关键事项：** 保存的有理上界确实包围加权零点积分、实部与高度求和、解析尾项及其他超越表达式。导出同一个上界、再检查它小于1，并不能替代该义务。本报告所列有限定理不能单独推出连续短区间素数定理。

## 3. 公理审计与确定性复现

[FiniteAudit.lean](../lean/LegendreK6/FiniteAudit.lean)对关键定理执行 `#print axioms`，原输出保存在 [finite_kernel_axioms.txt](finite_kernel_axioms.txt)。包括最大素数与 `small_range_prime` 在内的结果仅依赖 Lean/Mathlib 的标准逻辑公理 `propext`、`Classical.choice`、`Quot.sound`；整数CHL链检查不依赖任何公理。未出现 `sorryAx`、`Lean.ofReduceBool` 或自定义数学公理。

[生成器](../code/generate_lean_certificates.py)支持：

```powershell
python -X utf8 code/generate_lean_certificates.py --check
```

在 `proof` 目录执行。它在临时目录重生29个Lean源文件及 [Pratt生成数据](../results/pratt_certificate_data.json)，逐字节与保存输出比较。本次实际执行返回 `GENERATED_SOURCES_MATCH`；它不修改保存结果。完整递归素数数据可审查，生成器本身不属于形式化证明的可信计算基础。

此报告由负责有限证书形式化的 AI 代理撰写，属于实现与执行记录，不是第三方人类同行评议。
