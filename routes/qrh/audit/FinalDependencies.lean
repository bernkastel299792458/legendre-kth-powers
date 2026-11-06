import LegendreK6.FinalCellCoverage

/-!
Read-only inspection of local constants appearing in actual theorem types and
proof terms. Imported Mathlib declarations cannot refer back to this project,
so traversing project constants suffices for the local dependency inventory.
This diagnostic does not create a mathematical theorem or replace the kernel.
Run with: cd lean; lake env lean ../audit/FinalDependencies.lean
-/

open Lean

private def isProjectConstant (n : Name) : Bool :=
  (n.toString.splitOn ".").contains "LegendreK6"

private partial def collectProject (n : Name) : StateT NameSet CoreM Unit := do
  unless (← get).contains n do
    modify (·.insert n)
    let ci ← getConstInfo n
    for c in ci.type.getUsedConstants do
      if isProjectConstant c then collectProject c
    if let some value := ci.value? true then
      for c in value.getUsedConstants do
        if isProjectConstant c then collectProject c

run_cmd do
  let (_, deps) ← Elab.Command.liftCoreM
    ((collectProject ``LegendreK6.sixth_powers_from_named_inputs).run {})
  for required in [``LegendreK6.middle_short_interval_from_inputs,
      ``LegendreK6.M3Lower.lower_middle_short_interval_from_inputs,
      ``LegendreK6.M3MiddleUpper.middle_upper_short_interval_from_inputs,
      ``LegendreK6.M3FarUpper.far_short_interval_from_inputs,
      ``LegendreK6.M3Lower.scaled_sigma_weight_le,
      ``LegendreK6.M3Lower.scaled_heightBudget_le,
      ``LegendreK6.M3Lower.rational_double_budget,
      ``LegendreK6.M3Lower.weighted_lowRank_le,
      ``LegendreK6.M3Lower.weightedMain_le,
      ``LegendreK6.positive_zero_envelope_le_scaled,
      ``LegendreK6.positiveZeroWeight_eq_finiteRH,
      ``LegendreK6.densityGridPhi_translation_le,
      ``LegendreK6.trapezoidHeightBudget_translation_le,
      ``LegendreK6.M3Far.lowRankTaylor20_le,
      ``LegendreK6.M3Far.sigmaFactor_upper,
      ``LegendreK6.M3Far.heightFactor_upper,
      ``LegendreK6.M2Pilot.lowRankTaylor20_le,
      ``LegendreK6.M2Pilot.rationalLowRank20_le,
      ``LegendreK6.exp_le_taylor20,
      ``LegendreK6.lowRankTaylor20_eq_rational,
      ``LegendreK6.norm_trapezoidKernel_le_min,
      ``LegendreK6.norm_trapezoidTrivialDifference_le,
      ``LegendreK6.weightedMangoldt_trapezoid_eq,
      ``LegendreK6.trapezoid_zero_sum_tendsto,
      ``LegendreK6.finite_quadratic_residual_bound,
      ``LegendreK6.positiveZeroWeight_le_gridPhi,
      ``LegendreK6.tail_short_interval_from_inputs,
      ``LegendreK6.tail_truncated_zero_bound,
      ``LegendreK6.riemannZeta_ne_zero_real_strip,
      ``LegendreK6.zetaMultiplicity_conj,
      ``LegendreK6.lower_log_range,
      ``LegendreK6.small_range_prime,
      ``LegendreK6.chl_integer_coverage] do
    unless deps.contains required do
      throwError "Expected actual proof dependency is absent: {required}"
  if deps.contains ``LegendreK6.PrimeInOpenInterval then
    logInfo "Actual strict prime-interval predicate occurs in the final theorem."
  for n in deps.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"{n}"
  logInfo "FINAL_K6_REQUIRED_PROOF_DEPENDENCIES_PRESENT"

#check LegendreK6.sixth_powers_from_named_inputs
#print axioms LegendreK6.sixth_powers_from_named_inputs
#check LegendreK6.sixth_power_short_from_named_inputs
#print axioms LegendreK6.sixth_power_short_from_named_inputs
#check LegendreK6.all_94_cells_actual_prime_intervals
#print axioms LegendreK6.all_94_cells_actual_prime_intervals
#check LegendreK6.all_60_far_cells_actual_prime_intervals
#print axioms LegendreK6.all_60_far_cells_actual_prime_intervals
#print LegendreK6.SixthPowerConclusion
#print LegendreK6.NatSixthShort
#print LegendreK6.QRHSevenEighths
#print LegendreK6.CSv2
#print LegendreK6.RosserZeroCount
#print LegendreK6.IntegratedExplicitFormula
#print LegendreK6.integratedFormulaValue
#print LegendreK6.FiniteRH3e12
#print LegendreK6.CHJIIShortInterval
#print LegendreK6.CHLRows
