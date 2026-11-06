import LegendreK6.TailFromInputs

/-!
Read-only inspection of local constants appearing in actual theorem types and
proof terms. Imported Mathlib declarations cannot refer back to this project,
so traversing project constants suffices for the local dependency inventory.
This diagnostic does not create a mathematical theorem or replace the kernel.
Run with: cd lean; lake env lean ../audit/Milestone1Dependencies.lean
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
    ((collectProject ``LegendreK6.tail_short_interval_from_inputs).run {})
  for required in [``LegendreK6.tail_truncated_zero_bound,
      ``LegendreK6.cs_tail_density, ``LegendreK6.finite_exp_layer_bound,
      ``LegendreK6.riemannZeta_ne_zero_real_strip,
      ``LegendreK6.zetaMultiplicity_conj,
      ``LegendreK6.totalZeroCount_le_mul_log,
      ``LegendreK6.norm_cpow_sub_div_le,
      ``LegendreK6.tail_prime_power_error_le,
      ``LegendreK6.prime_of_theta_sub_gt_log,
      ``LegendreK6.tail_bound_all] do
    unless deps.contains required do
      throwError "Expected actual proof dependency is absent: {required}"
  if deps.contains ``LegendreK6.PrimeInOpenInterval then
    logInfo "Actual strict prime-interval predicate occurs in the tail theorem."
  for n in deps.toList.toArray.qsort (fun a b => a.toString < b.toString) do
    logInfo m!"{n}"
  logInfo "MILESTONE1_REQUIRED_PROOF_DEPENDENCIES_PRESENT"

#check LegendreK6.tail_short_interval_from_inputs
#print axioms LegendreK6.tail_short_interval_from_inputs
#print LegendreK6.QRHSevenEighths
#print LegendreK6.CSv2
#print LegendreK6.RosserZeroCount
#print LegendreK6.CHJIIShortInterval
