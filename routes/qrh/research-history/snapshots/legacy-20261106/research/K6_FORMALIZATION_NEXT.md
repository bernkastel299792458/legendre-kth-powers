# k=6 全量 Lean 形式化的后续实施评估

日期：2026-11-06。状态：**后续研究设计，尚未实施、尚未编译的方案，不属于本次已完成成果。**

本次工作只读检查冻结的 `proof/` 与其固定版本 Mathlib；唯一新增文件是本文。当前完成范围仍以 [`proof/FORMALIZATION_STATUS.md`](../proof/FORMALIZATION_STATUS.md) 为准。46 个模块编译通过，没有消除 `AnalyticSegmentInputs` 的三个局部素数结论前提。

评估边界：承认 H1、H2 以及明确列出的文献定理，不重新证明 CS、Ingham、CHL、CHJII、有限高度 RH 或 Rosser 定理。工作是精确翻译这些输入，并形式化本稿从输入到结论的推导。不能用“某区间含素数”“完整证书可靠”“某加权和已经满足预算”代替尚未证明的本稿结论。

## 1. 独立建议与首先可交付的结果

**最先实施实际素数幂预算；随后先闭合无限尾部，最后推进两个平滑中段。** 不是先扩大当前的装配定理，也不是先重建一般分布理论。

1. `PrimePowerBudget`：从 Mathlib 的实际 `vonMangoldt`、`Chebyshev.psi/theta` 出发证明本稿所需的非素数贡献上界。它不依赖 H1/H2、ζ 零点或任何新的文献输入，且现有 API 已覆盖主要数学内容。
2. `ZetaZeroCount` 与精确文献接口：把重数、两种截断边界、正负高度计数连接到实际 `riemannZeta`。这是真正的公共依赖，应先于三个解析分支。
3. `TailFromLiterature`：用 CHJII 的原短区间公式、H1/H2、总零点计数和已经证明的 `tail_bound_all`，推出 **所有实数 `x>0, log x≥700` 的实际严格开区间素数结论**。它不需要平滑 Ψ₁ 公式、不需要 154 个单元的超越求值、不需要非光滑权的二阶导数测度。因此它是第一个值得要求“完全闭合”的解析里程碑。
4. 平行试做一个困难单元的完整内核数值证书，并发展梯形权、实部层积分和高度求和的通用定理。先证明一个单元的完整语义链，再批量生成其余证明。

第 1 项是最短、最确定的进展；第 3 项是第一个能实际删除一个 `AnalyticSegmentInputs` 字段的进展。尾部仍有若干实质证明，不能把现有标量六项函数界说成这个里程碑已经完成。

## 2. 检查过的 Mathlib 能力

本次使用固定提交 `9d581dfff2e41de989072ea63abf3daf69311520`，对应本包 Lean `v4.36.0-rc2`；结论不依赖未来 Mathlib 版本。

| 所需对象 | 已核查的真实声明 | 对本项目的作用与限制 |
|---|---|---|
| 实际 ζ 零点 | `riemannZetaZeros`、`mem_riemannZetaZeros`、`isDiscrete_riemannZetaZeros`、`IsCompact.inter_riemannZetaZeros_finite` | 零点集合已经存在，紧矩形内零点有限可直接获得；它只是集合，尚不是带重数的 `N(σ,T)`。[源码][zeros] |
| 零点重数 | `analyticOrderAt`、`analyticOrderNatAt`、`Nat.cast_analyticOrderNatAt`、`AnalyticAt.analyticOrderAt_eq_natCast` | 可以定义真实重数；必须先证明在零点处解析且阶不是 `⊤`。直接 `toNat` 会把无限阶变成 0，不能省略这一步。[源码][order] |
| ζ 解析性和条带 | `analyticOn_riemannZeta`；`riemannZeta_ne_zero_of_one_le_re`；`riemannZeta_eq_zero_iff_of_re_nonpos` | 可排除极点处伪零点、证明非平凡零点实部属于 `(0,1)`，无需重新证明函数方程。[解析性][zeta]、[非消失][nonvanishing] |
| 共轭对称 | `riemannZeta_conj` | 位于 `NumberTheory/Harmonic/ZetaAsymp.lean`，不在名称最直观的 ζ 文件中。仍须证明重数在共轭下相等，才能正确使用因子 2。[源码][conj] |
| 实际 Λ 与 ζ | `ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div` | 已证明 `Re s>1` 上的 `L(Λ,s)=-ζ′/ζ`；它不是本稿所用 Ψ₁ 显式公式，不能直接替代移线定理。[源码][dirichlet] |
| 素数幂 | `Chebyshev.psi_sub_theta_eq_sum_not_prime`；`abs_psi_sub_theta_le_sqrt_mul_log`；`psi_eq_theta_add_sum_theta` | 已有实际非素数和的恒等式及 `abs(ψ(Y)−θ(Y))≤2√Y log Y` 的显式界，足够连接当前预算。[源码][chebyshev] |
| Mellin 核 | `hasDerivAt_ofReal_cpow_const`；`Complex.norm_cpow_eq_rpow_re_of_pos` | 正实底数上的复幂导数和模已经可用；仍须证分母非零、支撑区间条件及分部积分边界。[导数][cpowderiv]、[模][cpownorm] |
| 普通分部积分及换序 | `intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt`；`intervalIntegral.sum`；`MeasureTheory.integral_tsum_of_summable_integral_norm` | 能在有限分段上做全部本稿所需分部积分；无限换序要求先证明范数积分可和，不能仅声明形式恒等式。[分部积分][ibp]、[无限换序][tsum] |
| Stieltjes / 一般零点计数 | `StieltjesFunction.measure`；Nevanlinna `logCounting` 与 meromorphic divisor | 基础测度及含重数的圆盘对数计数确实存在，但后者不是 CS 的矩形、无对数权 `N(σ,T)`。不宜为使用它而改写本稿全部计数接口。[测度][stieltjes]、[对数计数][logcount] |
| 经内核检查的指数区间 | `dyadic_interval` 与 `Inclusion.IntervalDyadicReal.exp_mem` | 已可用并在本包尾部成功使用。当前所查扩展没有现成的通用 `log`、实数除法/rpow 整套自动规则；这些可通过已证的单调性、正分母交叉乘和 `rpow=exp(log·)` 编译成受支持表达式。[策略][interval]、[指数][intervalexp] |

在上述固定源树的 `NumberTheory/LSeries`、相关解析/积分文件中未找到本稿 Ψ₁ 积分显式公式或已组装的 ζ 零点密度计数定理。这是本次检索范围内的结果，不是宣称所有可能文件都不存在相关进展。承认精确文献定理作为输入后，无需先从 `−ζ′/ζ` 重建 Perron 积分和移线。

## 3. 第一项：无额外前提的素数幂桥梁

建议首先证明以下数学命题，而不是再次证明抽象 `prime_of_weighted_budget`：若 `S⊆{1,…,⌊Y⌋}`, `0≤w(m)≤W`，则

\[
\operatorname{weightedNonprime}(S,w)
\le W\bigl(\psi(Y)-\theta(Y)\bigr)
\le 2W\sqrt Y\log Y\quad(Y\ge1).
\]

第一步使用 `psi_sub_theta_eq_sum_not_prime`、`vonMangoldt_nonneg` 与有限和包含关系；第二步使用现有 `abs_psi_sub_theta_le_sqrt_mul_log`。在本稿使用的范围 `log Y≥4 log 2`，有

\[
2\sqrt Y\log Y\le\frac{\sqrt Y(\log Y)^2}{2\log2}.
\]

因此可以保持稿件和现有证书的较宽预算，不必重新生成所有数值结果。这里并未用该比较宣称对所有 `Y≥2` 证明稿件 (5)：若坚持形式化 (5) 的完整原始定义域，应改用现成的 `psi_eq_theta_add_sum_theta` 逐层证明；本稿实际需要的大参数范围无需这项额外工作。

验收：定理左端展开后必须是 `ArithmeticFunction.vonMangoldt` 的实际有限和；条件只能是权的非负性、上界、有限支撑与数值定义域。梯形 `W=32/31`、多项式 `W=1/16`（归一化后 `W/I=15/8`）、尾部无权三种实例分别连接到稿件的原预算。另补一个 `theta` 的严格端点引理：无 `(x,y)` 内素数时，`θ(y)−θ(x)≤log y`，保留右端可能为素数的情形。

## 4. 实际零点、重数与文献定理接口

推荐先用“实际零点有限集合 + 重数权”，避免先实现按高度排序的无限序列。

- 定义 `NontrivialZero` 为实际 `riemannZeta ρ=0` 且 `0<ρ.re<1` 的子类型。
- 定义 `multiplicity ρ := analyticOrderNatAt riemannZeta ρ`。证明 `0<multiplicity ρ`：解析性来自已有 ζ 定理；无限阶排除可由离散零点/恒等定理完成，不需要 QRH。
- 由紧矩形 `0≤Re z≤1, |Im z|≤T` 与零点集的交的有限性，构造精确有限零点集。`N(σ,T)` 为其中 `σ≤Re ρ, 0<Im ρ≤T` 的重数之和；`N(T)` 去掉 σ 条件。
- 无限和直接索引 `NontrivialZero`，项乘重数；或使用 `Σ ρ, Fin (multiplicity ρ)` 表示每个重数副本。若为匹配文献另用枚举，必须给出与此实际副本类型的等价，不能仅假设每个枚举值都是零点而遗漏“所有零点均被计入”。
- 证明计数对 T 单调、对 σ 反单调、重数共轭不变与有限和重索引。`riemannZeta_conj` 只解决值的对称，重数对称尚需用局部分解/解析阶唯一性证明。
- 明确处理 `Im ρ=0`：本次未检索到可直接引用的条带内实轴非消失专用声明。不能在定义中删掉这些点后宣布“全部非平凡零点”。需证明该经典事实，或在逐条查明出处后将其列为独立、精确的经典文献输入；这项接口决定应在 tail 里程碑前完成。不能把它混入 QRH 的定义。

只接受下列风格的输入，不使用自由浮动的 `zeroSystem`：

| 输入 | 精确接口应包含什么 | 本稿必须另证什么 |
|---|---|---|
| H1 | 实际非平凡 ζ 零点的 `Re ρ≤7/8` | 正负高度与有限计数转换 |
| H2 | CS v2 推论 1、表 1 前 12 行，真实含重数 `N(σ,T)`、准确行域与 `T≥3·10^12`、原指数和常数 | 表行选择、共同粗常数、层积分、加权和与数值证书 |
| 有限高度 RH | Platt–Trudgian 原陈述适用高度和边界的实际零点命题 | 正负高度/闭边界归约与 `A_a(T)` 等式 |
| Rosser | 原总零点计数界和原边界约定 | `T≥H` 时 `N(T)≤T log T`，包括所需右极限转换 |
| Ingham Ψ₁ 公式 | 本稿 (6) 的原始函数、实际零点重数和、平凡零点和、定义域及收敛含义；采用 `HasSum`/收敛极限而非无条件 `tsum` 等式 | 梯形四点作用、多项式配对、换序、Mellin 核与所有本地估计 |
| CHJII | 定理 1.3 + 表 1 对应行，真实 `Chebyshev.psi`、同一个 `T*∈[T,2T]`、实际有限零点和、正确余项范数和全部适用域 | 本稿选择 T 的适用性、零点估计、余项粗化、素数提取 |
| CHL | 原短区间行及阈值 | 当前下端归约已基本完成，保留显式输入 |

这些接口宜作为命名定理参数，不用新的全局 `axiom`。接口审查必须逐条核对原文，特别是 CHJII 的端点/取整/共同高度约定及 Ψ₁ 级数的收敛方式；本文没有代替这次原文译写审查。H2 上游推导的独立审查仍属于另一项工作。

验收还须检查 `#check` 的完整定理类型。仅 `#print axioms` 不会显示用定理参数偷渡的局部结论。

## 5. 最先闭合的解析分支：L≥700

建议分成以下小模块，名称是设计建议，尚未实现：

1. `FiniteZeroLayer`：对有限带重数实部列表证明层积分不等式，再实例化真实 `N(σ,U)`。先证明 `exp((β−1)L)` 的逐项基底加积分表示，再有限求和换序。复用现有 `exact_sigma_weight`，控制 `β≤5/8` 的基底和 `β=7/8` 的上端边界。
2. `CpowIntervalBound`：从复幂导数、实区间 FTC 和范数积分界证明
   `‖(y^ρ−x^ρ)/ρ‖ ≤ (y−x)*x^(Re ρ−1)`，适用 `0<x≤y`、`Re ρ≤1`、`ρ≠0`。这是连接真实 CHJII 零点项的关键，不能把其结论当作新假设。
3. `TailDomains`：证明 `T=x^(9/32)` 对所有 `L≥700` 满足 CHJII 条件，`U=2T≥H`，`y≤2x`、`log y≤L+1`、`λ>0`。已有 `TailResult` 只证明六项函数衰减，并没有自动完成这些域条件。阈值反射 + 简单导数/单调性是可复用路线。
4. `TailDensity`：从 H2 的第 20–27 行推出稿件 (36)，并把 `FiniteZeroLayer` 的积分精确估计成 `Z0+Z1+Z2`。既有 `cs_density_exponent_bound`、`cs_log_exponent_bound`、指数权积分可直接复用。
5. `TailPrime`：把同一 `T*` 的 CHJII 公式、正负高度重索引、实际素数幂预算与右端点 `log y` 预算组合，证明 `θ(y)−θ(x)>log y`，再用严格端点引理。最后调用 `tail_bound_all`。

验收目标：新尾部定理的类型仅含 H1/H2、精确命名的经典文献输入和 `x>0, log x≥700`；结论为 `ShortInterval4 x`。不得含 `AnalyticSegmentInputs`、`ShortInterval4` 作为前提，也不得含“六项函数已经控制实际素数和”这样的本稿核心中间结论前提。通过后才可删除装配的 `tail` 依赖。

## 6. 两个中段：可避开的基础设施与不可避开的证明

**梯形先用有限四点，不先造一般分布导数库。** 对每个整数 m 证明稿件的正部函数恒等式，交换有限 Λ 和，得到真实加权和与四个 Ψ₁ 值的等式。将精确文献公式代入后，有限个 `HasSum` 的加减给出零点项的四点组合。四个点正好保留全部端点和折点贡献。Mellin 的一次/二次分部积分可以在三个光滑子区间逐段做普通积分，合并边界项；这样仍严格包含四个原子。

多项式权用普通积分与 `F''` 配对，真正证明范数积分可和后调用 `integral_tsum_of_summable_integral_norm`。第三次分部积分保留两个端点项，得到 `6+2+2=10` 的总变差界；不能把两个端点的 2 遗漏。没有必要为了这一固定多项式开发适用于所有 BV 权的通用理论。

实部层积分、有限 RH 分段、统一逐零点包络与高度上和应做成通用实数/有限和引理，最后实例化实际 ζ。现成 `StieltjesFunction` 可用，但本稿的 g 只有少数显式幂函数分段；也可把 `g(t)` 写成非负导数密度的尾积分，先对有限零点和交换积分，再用单调收敛/Tonelli 取极限。这样能直接得到高度格质量差 `g(e^u_i)−g(e^u_(i+1))`，无需假设上界函数 Φ 单调。

这仍要求证明：真实累计计数 A 单调、无限边界消失、近零高度部分正确、所有高度尾积分收敛、有限格与解析尾部没有遗漏。不能把形式上的 Stieltjes 符号当成已经获得的定理。

## 7. 数值桥梁：生成证明项，而不是导入输出数字

当前 `Certificates` 证明的是保存有理数据的比较与覆盖；下一阶段目标应为真实实表达式 `δ(cell)≤savedUpper(cell)<1`。

建议让 Python 只生成未受信任的候选：有理网格、exp/log/rpow 包围端点、各分母正性见证、每个求和块上界。Lean 验证这些见证。无需先形式化整个 Arb 库，也不能把 `ArbSound` 作为无证明假设。

- log 包围用指数的单调反函数性质：证明 `exp l≤a≤exp u` 后推出 `l≤log a≤u`，同时证明 `a>0`。
- 正分母除法经交叉乘改写；平方根给非负候选上下界并平方验证；实幂改写为 `exp(r*log a)`。需要逐步证明解释器或生成规则的实数语义正确。
- 把高度与实部求和拆成共享子项和块；尤其共享 `q(c)`、各 `w_j`、表指数和重复指数包围，避免生成一个反复重算的巨大 tactic 项。
- 起点 floor/终点 ceil 不必在内核运行 Arb：给出候选整数后证明相邻两侧的严格不等式即可。首个非等长高度格、`min` 的分支和指数质量差非负性均要验证。
- 优先选择 refined 网格中最大 δ 对应单元做试点，并再选一个跨越 `log H` 起点分支的单元。先得到实际证明项和内核时间/内存数据，才决定 94+60 的分块规模。

验收：对每个完整单元证明真实表达式界，生成器可被替换而结论仍须内核检查；最终 CI 不依赖 `native_decide`、`+native` 或“保存文件正确”的公理。154 个单元均通过后，复用已有实参数覆盖定理，不能只验证最大值字段。

## 8. 五类缺口的依赖与交付顺序

| 现存缺口 | 实质依赖 | 下一交付与结束标准 |
|---|---|---|
| 1. 实际零点/重数/文献接口 | Mathlib ζ 集合、解析阶、共轭及文献精确译写 | 数学定义明确的真实 `N(σ,T)`；每个谱和与该对象一致；不要求数值算出任何 ζ 零点 |
| 2. 显式公式与权 | 缺口 1 + 精确 Ψ₁ 输入 | 实际 `weightedMangoldt` 的梯形及多项式公式、Mellin 包络和换序证明 |
| 3. 密度与高度求和 | 缺口 1；平滑分支另需缺口 2 | 先有限零点层积分及 tail 三项界，再全部平滑上和与解析高度尾部 |
| 4. 完整超越证书 | 精确定义的实表达式及内核包围规则；可与 1–3 平行 | 一个困难单元端到端通过，再 94+60 个全量通过 |
| 5. 算术/余项/截断语义 | 素数幂部分独立；CHJII 部分依赖 1、3；平凡零点部分依赖 2 | 先实际素数幂界，然后真正闭合 tail；最后与两个权的预算拼接 |

建议里程碑依次为：**实际素数幂预算 → 实际零点接口与 tail 全闭合 → 梯形一个单元全闭合 → 梯形 94 单元 → 多项式 60 单元 → 删除全部局部段结论前提的总定理。** 数值证书试点可与零点/尾部并行。每个里程碑同时审查 theorem type 与 axioms，并把剩余条件逐条记录。

最终成果可以准确称为“在 H1、H2 及所列精确文献定理输入下，本稿推导的端到端 Lean 形式化”；它并不表示 H1/H2 或全部所引经典定理也已在本仓库形式化。当前冻结成果尚未达到该状态。现阶段没有足够的单元试点内核性能数据，不能诚实承诺全链条需要固定几天或几次构建。

[zeros]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/NumberTheory/LSeries/ZetaZeros.lean
[order]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Analytic/Order.lean
[zeta]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/NumberTheory/LSeries/RiemannZeta.lean
[nonvanishing]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/NumberTheory/LSeries/Nonvanishing.lean
[conj]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/NumberTheory/Harmonic/ZetaAsymp.lean
[dirichlet]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/NumberTheory/LSeries/Dirichlet.lean
[chebyshev]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/NumberTheory/Chebyshev.lean
[cpowderiv]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/SpecialFunctions/Pow/Deriv.lean
[cpownorm]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean
[ibp]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Integral/IntervalIntegral/IntegrationByParts.lean
[tsum]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Integral/DominatedConvergence.lean
[stieltjes]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/MeasureTheory/Measure/Stieltjes.lean
[logcount]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Analysis/Complex/ValueDistribution/LogCounting/Basic.lean
[interval]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Tactic.lean
[intervalexp]: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Tactic/Inclusion/Extension/IntervalDyadicReal/Exp.lean
