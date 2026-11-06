import LegendreK6

/-! Audit both proof dependencies AND the complete theorem parameters. -/

#print axioms LegendreK6.small_range_prime
#print axioms LegendreK6.chl_integer_coverage
#print axioms LegendreK6.lower_log_range
#print axioms LegendreK6.refined_cells_checked
#print axioms LegendreK6.polynomial_cells_checked
#print axioms LegendreK6.refined_real_coverage
#print axioms LegendreK6.polynomial_real_coverage
#print axioms LegendreK6.four_point_quadratic
#print axioms LegendreK6.exact_sigma_weight
#print axioms LegendreK6.log_ratio_bound
#print axioms LegendreK6.common_zero_weight
#print axioms LegendreK6.coefficient_scaling_criterion
#print axioms LegendreK6.prime_of_normalized_weighted_budget
#print axioms LegendreK6.tail_at_700
#print axioms LegendreK6.tail_bound_all
#print axioms LegendreK6.tail_scaled_bound_all
#print axioms LegendreK6.sixth_powers_of_segment_inputs

#check LegendreK6.small_range_prime
#check LegendreK6.lower_log_range
#check LegendreK6.tail_bound_all
#check LegendreK6.prime_of_normalized_weighted_budget
#check LegendreK6.sixth_powers_of_segment_inputs
#print LegendreK6.AnalyticSegmentInputs
#print LegendreK6.CHLRows

/-! Milestone 1: inspect actual tail dependencies and the remaining finite inputs. -/
#print axioms LegendreK6.zetaMultiplicity_pos
#print axioms LegendreK6.zetaMultiplicity_conj
#print axioms LegendreK6.riemannZeta_ne_zero_real_strip
#print axioms LegendreK6.sum_allZetaZeros_eq_twice
#print axioms LegendreK6.weightedNonprime_le_manuscript_budget
#print axioms LegendreK6.prime_of_theta_sub_gt_log
#print axioms LegendreK6.norm_cpow_sub_div_le
#print axioms LegendreK6.finite_exp_layer_bound
#print axioms LegendreK6.cs_tail_density
#print axioms LegendreK6.totalZeroCount_le_mul_log
#print axioms LegendreK6.tail_positive_zero_sum_bound
#print axioms LegendreK6.tail_truncated_zero_bound
#print axioms LegendreK6.tail_short_interval_from_inputs
#print axioms LegendreK6.sixth_powers_of_finite_segment_inputs
#check LegendreK6.riemannZeta_ne_zero_real_strip
#check LegendreK6.tail_truncated_zero_bound
#check LegendreK6.tail_short_interval_from_inputs
#check LegendreK6.sixth_powers_of_finite_segment_inputs
#print LegendreK6.FiniteAnalyticSegmentInputs
#print LegendreK6.QRHSevenEighths
#print LegendreK6.CSv2
#print LegendreK6.RosserZeroCount
#print LegendreK6.CHJIIShortInterval

/-! Milestone 2: complete pilot, without a numerical-budget parameter. -/
#print axioms LegendreK6.M2Pilot.completeBudget_le
#print axioms LegendreK6.M2Pilot.pilot_short_interval_from_inputs
#check LegendreK6.M2Pilot.completeBudget_le
#check LegendreK6.M2Pilot.pilot_short_interval_from_inputs
#print LegendreK6.IntegratedExplicitFormula

/-! Final downstream theorem: seven named inputs, no analytic-segment premise. -/
#check LegendreK6.sixth_powers_from_named_inputs
#print axioms LegendreK6.sixth_powers_from_named_inputs
#check LegendreK6.sixth_power_short_from_named_inputs
#print axioms LegendreK6.sixth_power_short_from_named_inputs
#check LegendreK6.all_94_cells_actual_prime_intervals
#print axioms LegendreK6.all_94_cells_actual_prime_intervals
#check LegendreK6.all_60_far_cells_actual_prime_intervals
#print axioms LegendreK6.all_60_far_cells_actual_prime_intervals
#print LegendreK6.SixthPowerConclusion
#print LegendreK6.FiniteRH3e12
