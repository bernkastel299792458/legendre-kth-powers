# 论文与 Lean 声明对照

由 `code/build_reading_map.py` 从当前论文中的 `\leanref` 标记生成。
检查文件和声明是否存在，并绑定源码散列；数学陈述是否等价由正文与交叉审阅确认。

[完整论文](../../paper/current/main.pdf) · [证明结构](README.md) · [机器记录](reading_map.json)

## 问题、主定理与证明路线

[章节源码](../../paper/current/sections/01_introduction.tex)

| Lean 文件 | 声明 |
|---|---|
| [FinalResult](../../lean/LegendreK6/FinalResult.lean) | `sixth_powers_from_named_inputs` |
| [FinalResult](../../lean/LegendreK6/FinalResult.lean) | `sixth_power_short_from_named_inputs` |

## 七项外部输入

[章节源码](../../paper/current/sections/02_inputs.tex)

| Lean 文件 | 声明 |
|---|---|
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `NontrivialZero` |
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `allZetaZeros` |
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `zetaMultiplicity` |
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `riemannZeta_ne_zero_real_strip` |
| [DensityInput](../../lean/LegendreK6/DensityInput.lean) | `QRHSevenEighths` |
| [DensityInput](../../lean/LegendreK6/DensityInput.lean) | `CSv2` |
| [DensityInput](../../lean/LegendreK6/DensityInput.lean) | `cs_tail_density` |
| [LiteratureInputs](../../lean/LegendreK6/LiteratureInputs.lean) | `RosserZeroCount` |
| [LiteratureInputs](../../lean/LegendreK6/LiteratureInputs.lean) | `totalZeroCount_le_rosserCount` |
| [IntegratedPsi](../../lean/LegendreK6/IntegratedPsi.lean) | `integratedPsi` |
| [TrapezoidKernel](../../lean/LegendreK6/TrapezoidKernel.lean) | `zeroPrimitive` |
| [IntegratedExplicitFormula](../../lean/LegendreK6/IntegratedExplicitFormula.lean) | `trivialZeroPrimitiveSum` |
| [IntegratedExplicitFormula](../../lean/LegendreK6/IntegratedExplicitFormula.lean) | `IntegratedExplicitFormula` |
| [FiniteRHInput](../../lean/LegendreK6/FiniteRHInput.lean) | `FiniteRH3e12` |
| [LiteratureInputs](../../lean/LegendreK6/LiteratureInputs.lean) | `CHJIIShortInterval` |
| [Definitions](../../lean/LegendreK6/Definitions.lean) | `CHLInterval` |
| [CHLRange](../../lean/LegendreK6/CHLRange.lean) | `CHLRows` |
| [FinalResult](../../lean/LegendreK6/FinalResult.lean) | `sixth_powers_from_named_inputs` |

## 实际零点与算术准备

[章节源码](../../paper/current/sections/03_preliminaries.tex)

| Lean 文件 | 声明 |
|---|---|
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `riemannZeta_ne_zero_real_strip` |
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `zetaMultiplicity_conj` |
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `sum_allZetaZeros_eq_twice` |
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `all_zero_multiplicities_eq_twice_total` |
| [CpowInterval](../../lean/LegendreK6/CpowInterval.lean) | `norm_cpow_sub_div_le` |
| [PrimePowerBudget](../../lean/LegendreK6/PrimePowerBudget.lean) | `weightedNonprime_le_sqrt_log` |
| [PrimePowerBudget](../../lean/LegendreK6/PrimePowerBudget.lean) | `weightedNonprime_le_manuscript_budget` |
| [PrimePowerBudget](../../lean/LegendreK6/PrimePowerBudget.lean) | `theta_sub_le_log_of_no_prime` |
| [PrimePowerBudget](../../lean/LegendreK6/PrimePowerBudget.lean) | `prime_of_psi_sub_gt_manuscript_budget` |

## 梯形权与素数提取

[章节源码](../../paper/current/sections/04_trapezoid.tex)

| Lean 文件 | 声明 |
|---|---|
| [IntegratedPsi](../../lean/LegendreK6/IntegratedPsi.lean) | `weightedMangoldt_trapezoid_eq` |
| [IntegratedPsi](../../lean/LegendreK6/IntegratedPsi.lean) | `trapezoidWeight_bounds` |
| [IntegratedPsi](../../lean/LegendreK6/IntegratedPsi.lean) | `trapezoidWeight_pos_support` |
| [TrapezoidKernel](../../lean/LegendreK6/TrapezoidKernel.lean) | `norm_trapezoidKernel_le_base` |
| [TrapezoidKernel](../../lean/LegendreK6/TrapezoidKernel.lean) | `norm_trapezoidKernel_le_first` |
| [TrapezoidKernel](../../lean/LegendreK6/TrapezoidKernel.lean) | `norm_trapezoidKernel_le_second` |
| [TrapezoidKernel](../../lean/LegendreK6/TrapezoidKernel.lean) | `norm_trapezoidKernel_le_min` |
| [IntegratedExplicitFormula](../../lean/LegendreK6/IntegratedExplicitFormula.lean) | `trapezoid_zero_sum_tendsto` |
| [TrapezoidTrivial](../../lean/LegendreK6/TrapezoidTrivial.lean) | `norm_trapezoidTrivialDifference_le` |
| [PrimePowerBudget](../../lean/LegendreK6/PrimePowerBudget.lean) | `weightedNonprime_le_psi_sub_theta` |
| [PrimePowerBudget](../../lean/LegendreK6/PrimePowerBudget.lean) | `weightedNonprime_le_manuscript_budget` |
| [MiddleDomains](../../lean/LegendreK6/MiddleDomains.lean) | `middle_prime_power_normalized_le` |
| [MiddleDomains](../../lean/LegendreK6/MiddleDomains.lean) | `middle_prime_power_le` |
| [FarDomains](../../lean/LegendreK6/FarDomains.lean) | `far_prime_power_le` |
| [TrapezoidPrime](../../lean/LegendreK6/TrapezoidPrime.lean) | `prime_of_trapezoid_budgets` |

## 密度网格与完整高度余项

[章节源码](../../paper/current/sections/05_density.tex)

| Lean 文件 | 声明 |
|---|---|
| [DensityInput](../../lean/LegendreK6/DensityInput.lean) | `CSv2` |
| [DensityInput](../../lean/LegendreK6/DensityInput.lean) | `cs_log_exponent_eq` |
| [LiteratureInputs](../../lean/LegendreK6/LiteratureInputs.lean) | `totalZeroCount_le_mul_log` |
| [FiniteDensityGrid](../../lean/LegendreK6/FiniteDensityGrid.lean) | `exp_le_grid_staircase` |
| [FiniteDensityGrid](../../lean/LegendreK6/FiniteDensityGrid.lean) | `positiveZeroWeight_le_density_grid` |
| [FiniteDensityGrid](../../lean/LegendreK6/FiniteDensityGrid.lean) | `positiveZeroWeight_le_gridPhi` |
| [DensityGridGrowth](../../lean/LegendreK6/DensityGridGrowth.lean) | `densityGridPhi_shift_le` |
| [GeometricHeightTail](../../lean/LegendreK6/GeometricHeightTail.lean) | `finite_quadratic_residual_bound` |
| [TrapezoidHeightBound](../../lean/LegendreK6/TrapezoidHeightBound.lean) | `positive_zero_quadratic_residual_le` |
| [TrapezoidHeightBound](../../lean/LegendreK6/TrapezoidHeightBound.lean) | `positive_zero_envelope_le_heightBudget` |
| [TrapezoidHeightBound](../../lean/LegendreK6/TrapezoidHeightBound.lean) | `norm_truncatedTrapezoidZeroSum_le_heightBudget` |

## 严格数值证书与整数矩

[章节源码](../../paper/current/sections/06_certificates.tex)

| Lean 文件 | 声明 |
|---|---|
| [M2PilotBudgetIdentity](../../lean/LegendreK6/M2PilotBudgetIdentity.lean) | `weightedPhi_eq_twice_heightBudget` |
| [M2PilotBudgetIdentity](../../lean/LegendreK6/M2PilotBudgetIdentity.lean) | `weightedPhi_eq_main_add_aux` |
| [LowRankTaylor](../../lean/LegendreK6/LowRankTaylor.lean) | `exp_le_taylor20` |
| [LowRankTaylor](../../lean/LegendreK6/LowRankTaylor.lean) | `shifted_exp_factorization` |
| [LowRankTaylor](../../lean/LegendreK6/LowRankTaylor.lean) | `shifted_exp_sum_le` |
| [LowRankTaylor](../../lean/LegendreK6/LowRankTaylor.lean) | `lowRankTaylor20_mono` |
| [LowRankInteger](../../lean/LegendreK6/LowRankInteger.lean) | `lowRankTaylor20_eq_rational` |
| [M2PilotConstants](../../lean/LegendreK6/M2PilotConstants.lean) | `start_logKernel_eq_one` |
| [M2PilotGrid](../../lean/LegendreK6/M2PilotGrid.lean) | `sigma_height_product_bounds` |
| [M2PilotFactorBounds](../../lean/LegendreK6/M2PilotFactorBounds.lean) | `sigmaDyadicBounds` |
| [M2PilotFactorBounds](../../lean/LegendreK6/M2PilotFactorBounds.lean) | `heightDyadicBounds` |
| [M2PilotIntegerCertificate](../../lean/LegendreK6/M2PilotIntegerCertificate.lean) | `rationalLowRank20_le` |
| [M3FarGrid](../../lean/LegendreK6/M3FarGrid.lean) | `sigma_height_product_bounds` |
| [M3FarIntegerCertificate](../../lean/LegendreK6/M3FarIntegerCertificate.lean) | `rationalLowRank20_le` |
| [M2PilotAuxiliary](../../lean/LegendreK6/M2PilotAuxiliary.lean) | `auxiliaryBudget_le_small` |
| [M3FarAuxiliary](../../lean/LegendreK6/M3FarAuxiliary.lean) | `auxiliaryBudget_le_small` |
| [M2PilotResult](../../lean/LegendreK6/M2PilotResult.lean) | `pilot_short_interval_from_inputs` |
| [M3FarResult](../../lean/LegendreK6/M3FarResult.lean) | `pilot_short_interval_from_inputs` |

## 连续覆盖及有限高度 RH 比较

[章节源码](../../paper/current/sections/07_coverage.tex)

| Lean 文件 | 声明 |
|---|---|
| [DensityGridTranslation](../../lean/LegendreK6/DensityGridTranslation.lean) | `sigmaGridWeight_translation_le` |
| [DensityGridTranslation](../../lean/LegendreK6/DensityGridTranslation.lean) | `grid_translation_rate_nonpos` |
| [DensityGridTranslation](../../lean/LegendreK6/DensityGridTranslation.lean) | `densityGridPhi_translation_le` |
| [TrapezoidBudgetTranslation](../../lean/LegendreK6/TrapezoidBudgetTranslation.lean) | `trapezoidHeightBudget_translation_le` |
| [M3MiddleUpper](../../lean/LegendreK6/M3MiddleUpper.lean) | `middle_upper_short_interval_from_inputs` |
| [M3FarUpper](../../lean/LegendreK6/M3FarUpper.lean) | `far_short_interval_from_inputs` |
| [TrapezoidLowHeight](../../lean/LegendreK6/TrapezoidLowHeight.lean) | `norm_truncatedTrapezoidZeroSum_le_scaled_heightBudget` |
| [M3LowerConstants](../../lean/LegendreK6/M3LowerConstants.lean) | `middleQ_le_scaling_q` |
| [M3LowerConstants](../../lean/LegendreK6/M3LowerConstants.lean) | `middleQ_linear_le_scaling` |
| [M3LowerComparison](../../lean/LegendreK6/M3LowerComparison.lean) | `scaled_sigma_weight_le` |
| [M3LowerExpression](../../lean/LegendreK6/M3LowerExpression.lean) | `scaled_heightBudget_le` |
| [M3LowerIntegerCertificate](../../lean/LegendreK6/M3LowerIntegerCertificate.lean) | `rational_double_budget` |
| [M3LowerInteger](../../lean/LegendreK6/M3LowerInteger.lean) | `weighted_lowRank_le` |
| [M3LowerMainBound](../../lean/LegendreK6/M3LowerMainBound.lean) | `weightedMain_le` |
| [M3LowerResult](../../lean/LegendreK6/M3LowerResult.lean) | `lower_middle_short_interval_from_inputs` |

## 无限尾部

[章节源码](../../paper/current/sections/08_tail.tex)

| Lean 文件 | 声明 |
|---|---|
| [TailDomains](../../lean/LegendreK6/TailDomains.lean) | `tail_log_sq_lt_T` |
| [TailDomains](../../lean/LegendreK6/TailDomains.lean) | `tail_T_lt_sqrt_limit` |
| [TailDomains](../../lean/LegendreK6/TailDomains.lean) | `tail_height_ge_RH` |
| [LiteratureInputs](../../lean/LegendreK6/LiteratureInputs.lean) | `CHJIIShortInterval` |
| [CpowInterval](../../lean/LegendreK6/CpowInterval.lean) | `norm_cpow_sub_div_le` |
| [CpowInterval](../../lean/LegendreK6/CpowInterval.lean) | `norm_sum_cpow_sub_div_le` |
| [ZetaZeros](../../lean/LegendreK6/ZetaZeros.lean) | `sum_allZetaZeros_eq_twice` |
| [FiniteZeroLayer](../../lean/LegendreK6/FiniteZeroLayer.lean) | `finite_exp_layer_bound` |
| [TailDensity](../../lean/LegendreK6/TailDensity.lean) | `positive_zero_exp_layer` |
| [LiteratureInputs](../../lean/LegendreK6/LiteratureInputs.lean) | `totalZeroCount_le_mul_log` |
| [DensityInput](../../lean/LegendreK6/DensityInput.lean) | `cs_tail_density` |
| [TailDensity](../../lean/LegendreK6/TailDensity.lean) | `integral_cs_tail_envelope_le` |
| [TailZeroSum](../../lean/LegendreK6/TailZeroSum.lean) | `tail_truncated_zero_bound` |
| [TailErrorBudgets](../../lean/LegendreK6/TailErrorBudgets.lean) | `tail_truncation_error_le` |
| [TailErrorBudgets](../../lean/LegendreK6/TailErrorBudgets.lean) | `tail_prime_power_error_le` |
| [TailErrorBudgets](../../lean/LegendreK6/TailErrorBudgets.lean) | `tail_endpoint_error_le` |
| [PrimePowerBudget](../../lean/LegendreK6/PrimePowerBudget.lean) | `prime_of_theta_sub_gt_log` |
| [TailArithmetic](../../lean/LegendreK6/TailArithmetic.lean) | `tailBound` |
| [TailArithmetic](../../lean/LegendreK6/TailArithmetic.lean) | `log_two_bounds` |
| [TailArithmetic](../../lean/LegendreK6/TailArithmetic.lean) | `tail_at_700` |
| [TailMonotonic](../../lean/LegendreK6/TailMonotonic.lean) | `affine_power_exp_antitone` |
| [TailMonotonic](../../lean/LegendreK6/TailMonotonic.lean) | `tail_ratio_antitone` |
| [TailResult](../../lean/LegendreK6/TailResult.lean) | `tailBound_antitone` |
| [TailResult](../../lean/LegendreK6/TailResult.lean) | `tail_bound_all` |
| [TailFromInputs](../../lean/LegendreK6/TailFromInputs.lean) | `tail_short_interval_exp` |
| [TailFromInputs](../../lean/LegendreK6/TailFromInputs.lean) | `tail_short_interval_from_inputs` |

## 整数下段

[章节源码](../../paper/current/sections/09_lower.tex)

| Lean 文件 | 声明 |
|---|---|
| [Pratt/Block005](../../lean/LegendreK6/Pratt/Block005.lean) | `prime_15629` |
| [PrimeWitnesses](../../lean/LegendreK6/PrimeWitnesses.lean) | `small_range_prime` |
| [Definitions](../../lean/LegendreK6/Definitions.lean) | `CHLInterval` |
| [CHL](../../lean/LegendreK6/CHL.lean) | `nat_sixth_short_of_CHL` |
| [Reduction](../../lean/LegendreK6/Reduction.lean) | `sixth_right_endpoint_not_prime` |
| [CHLRange](../../lean/LegendreK6/CHLRange.lean) | `CHLRows` |
| [CHLRange](../../lean/LegendreK6/CHLRange.lean) | `nat_short_of_CHL_integer_row` |
| [CHLRange](../../lean/LegendreK6/CHLRange.lean) | `chl_integer_coverage` |
| [LowerRange](../../lean/LegendreK6/LowerRange.lean) | `lower_range_complete` |
| [Thresholds](../../lean/LegendreK6/Thresholds.lean) | `lower_join_exp` |
| [CHLRange](../../lean/LegendreK6/CHLRange.lean) | `lower_join_of_log` |
| [LowerRange](../../lean/LegendreK6/LowerRange.lean) | `lower_log_range` |

## 主定理总装

[章节源码](../../paper/current/sections/10_assembly.tex)

| Lean 文件 | 声明 |
|---|---|
| [Definitions](../../lean/LegendreK6/Definitions.lean) | `ShortInterval6` |
| [Definitions](../../lean/LegendreK6/Definitions.lean) | `ShortInterval4` |
| [Definitions](../../lean/LegendreK6/Definitions.lean) | `NatSixthShort` |
| [M3LowerResult](../../lean/LegendreK6/M3LowerResult.lean) | `lower_middle_short_interval_from_inputs` |
| [M3MiddleUpper](../../lean/LegendreK6/M3MiddleUpper.lean) | `middle_upper_short_interval_from_inputs` |
| [M3FarUpper](../../lean/LegendreK6/M3FarUpper.lean) | `far_short_interval_from_inputs` |
| [Reduction](../../lean/LegendreK6/Reduction.lean) | `four_length_le_six_length` |
| [Reduction](../../lean/LegendreK6/Reduction.lean) | `short_six_of_short_four` |
| [FinalResult](../../lean/LegendreK6/FinalResult.lean) | `middle_short_interval_from_inputs` |
| [Assembly](../../lean/LegendreK6/Assembly.lean) | `real_short_above_167_of_segment_inputs` |
| [Reduction](../../lean/LegendreK6/Reduction.lean) | `sixth_rpow_five_sixths` |
| [Reduction](../../lean/LegendreK6/Reduction.lean) | `nat_short_of_real_short` |
| [Reduction](../../lean/LegendreK6/Reduction.lean) | `sixth_binomial_gap` |
| [FinalResult](../../lean/LegendreK6/FinalResult.lean) | `sixth_power_short_from_named_inputs` |
| [FinalResult](../../lean/LegendreK6/FinalResult.lean) | `sixth_powers_from_named_inputs` |
| [Definitions](../../lean/LegendreK6/Definitions.lean) | `SixthPowerConclusion` |
| [Assembly](../../lean/LegendreK6/Assembly.lean) | `AnalyticSegmentInputs` |
| [AssemblyWithTail](../../lean/LegendreK6/AssemblyWithTail.lean) | `FiniteAnalyticSegmentInputs` |
| [FinalResult](../../lean/LegendreK6/FinalResult.lean) | `finite_analytic_segments_from_inputs` |
| [TailFromInputs](../../lean/LegendreK6/TailFromInputs.lean) | `tail_short_interval_from_inputs` |
| [FinalCellCoverage](../../lean/LegendreK6/FinalCellCoverage.lean) | `all_94_cells_actual_prime_intervals` |
| [FinalCellCoverage](../../lean/LegendreK6/FinalCellCoverage.lean) | `all_60_far_cells_actual_prime_intervals` |

## 方法贡献与后续研究

[章节源码](../../paper/current/sections/11_methods.tex)

本节承担引言、讨论或研究披露，不另声明新的形式化结果。

## 形式化、复现与 AI 贡献

[章节源码](../../paper/current/sections/12_formalization.tex)

本节承担引言、讨论或研究披露，不另声明新的形式化结果。

## 历史版本与材料索引

[章节源码](../../paper/current/sections/appendix_versions.tex)

本节承担引言、讨论或研究披露，不另声明新的形式化结果。

