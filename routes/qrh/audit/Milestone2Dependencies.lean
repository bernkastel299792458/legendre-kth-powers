import LegendreK6.M2PilotResult

/-!
Read-only inspection of local constants appearing in actual theorem types and
proof terms. Imported Mathlib declarations cannot refer back to this project,
so traversing project constants suffices for the local dependency inventory.
This diagnostic does not create a mathematical theorem or replace the kernel.
Run with: cd lean; lake env lean ../audit/Milestone2Dependencies.lean
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
    ((collectProject ``LegendreK6.M2Pilot.pilot_short_interval_from_inputs).run {})
  for required in [``LegendreK6.M2Pilot.lowRankTaylor20_le,
      ``LegendreK6.M2Pilot.sigmaFactor_upper,
      ``LegendreK6.M2Pilot.sigmaPower_upper,
      ``LegendreK6.M2Pilot.heightFactor_upper,
      ``LegendreK6.M2Pilot.heightPower_upper,
      ``LegendreK6.M2Pilot.rationalLowRank20_le,
      ``LegendreK6.lowRankTaylor20_eq_rational,
      ``LegendreK6.dyadicMoment_eq_rationalMoment,
      ``LegendreK6.exp_le_taylor20,
      ``LegendreK6.M2Pilot.auxiliaryBudget_le_small,
      ``LegendreK6.M2Pilot.prime_power_budget_small,
      ``LegendreK6.M2Pilot.trivial_budget_small,
      `LegendreK6.norm_truncatedTrapezoidZeroSum_le_heightBudget,
      `LegendreK6.positive_zero_quadratic_residual_le,
      `LegendreK6.finite_quadratic_residual_bound,
      `LegendreK6.densityGridPhi_shift_le,
      `LegendreK6.positiveZeroWeight_le_gridPhi,
      `LegendreK6.finite_exp_grid_bound,
      `LegendreK6.riemannZeta_ne_zero_real_strip,
      `LegendreK6.zetaMultiplicity_conj,
      `LegendreK6.norm_trapezoidKernel_le_min,
      `LegendreK6.norm_trapezoidTrivialDifference_le,
      `LegendreK6.weightedMangoldt_trapezoid_eq,
      `LegendreK6.trapezoid_zero_sum_tendsto,
      `LegendreK6.middle_prime_power_le,
      `LegendreK6.prime_of_weighted_excess,
      `LegendreK6.M2Pilot.analytic_budget_eq_completeBudget] do
    unless deps.contains required do
      throwError "Expected actual proof dependency is absent: {required}"
  if deps.contains ``LegendreK6.PrimeInOpenInterval then
    logInfo "Actual strict prime-interval predicate occurs in the pilot analytic theorem."
  for n in deps.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"{n}"
  logInfo "MILESTONE2_REQUIRED_PROOF_DEPENDENCIES_PRESENT"

#check LegendreK6.M2Pilot.completeBudget_le
#print axioms LegendreK6.M2Pilot.completeBudget_le
#check LegendreK6.M2Pilot.pilot_short_interval_from_inputs
#print axioms LegendreK6.M2Pilot.pilot_short_interval_from_inputs
#print LegendreK6.QRHSevenEighths
#print LegendreK6.CSv2
#print LegendreK6.RosserZeroCount
#print LegendreK6.IntegratedExplicitFormula
#print LegendreK6.M2Pilot.completeBudget

#print LegendreK6.integratedFormulaValue
