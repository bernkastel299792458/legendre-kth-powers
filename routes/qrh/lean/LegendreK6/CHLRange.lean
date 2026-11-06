import LegendreK6.CHL
import LegendreK6.Thresholds

/-!
# The twelve corrected CHL rows and their complete integer coverage

`CHLRows` is a transparent package of precisely the externally cited CHL
statements. All arithmetic, transcendental lower thresholds, interval overlap,
and endpoint conversion are proved in Lean. No local analytic module conclusion
or numerical certificate is included among these literature inputs.
-/

namespace LegendreK6

/-- The exact twelve source rows from CHL, arXiv:2103.05986v3, Table 2. -/
structure CHLRows : Prop where
  row0 : CHLInterval 39097000 (4 * 10 ^ 18)
  row43 : CHLInterval 41816800 (Real.exp 43)
  row46 : CHLInterval 163940000 (Real.exp 46)
  row50 : CHLInterval 1061200000 (Real.exp 50)
  row55 : CHLInterval 10288400000 (Real.exp 55)
  row60 : CHLInterval 76918400000 (Real.exp 60)
  row75 : CHLInterval 174043000000 (Real.exp 75)
  row90 : CHLInterval 184304000000 (Real.exp 90)
  row105 : CHLInterval 191886000000 (Real.exp 105)
  row120 : CHLInterval 197917000000 (Real.exp 120)
  row135 : CHLInterval 202553000000 (Real.exp 135)
  row150 : CHLInterval 207053000000 (Real.exp 150)

theorem nat_short_of_CHL_integer_row {n nlo nhi : ℕ} {Δ X : ℝ}
    (hn : 2 ≤ n) (hΔ : 1 < Δ) (hCHL : CHLInterval Δ X)
    (hlo : nlo ≤ n) (hhi : n ≤ nhi)
    (hthreshold : X ≤ (nlo : ℝ) ^ 6)
    (hupper : (nhi : ℝ) ≤ 6 * (Δ - 1)) : NatSixthShort n := by
  apply nat_sixth_short_of_CHL hn hΔ hCHL
  · exact hthreshold.trans
      (pow_le_pow_left₀ (Nat.cast_nonneg nlo) (by exact_mod_cast hlo) 6)
  · exact le_trans (by exact_mod_cast hhi) hupper

theorem chl_integer_coverage (H : CHLRows) (n : ℕ)
    (hnlo : 1260 ≤ n) (hnhi : n ≤ 1242317999994) : NatSixthShort n := by
  have hn : 2 ≤ n := by omega
  by_cases h0 : n ≤ 234581994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row0 hnlo h0
      (by norm_num) (by norm_num)
  by_cases h43 : n ≤ 250900794
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row43
      (show 1296 ≤ n by omega) h43 chl_threshold_43 (by norm_num)
  by_cases h46 : n ≤ 983639994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row46
      (show 2136 ≤ n by omega) h46 chl_threshold_46 (by norm_num)
  by_cases h50 : n ≤ 6367199994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row50
      (show 4161 ≤ n by omega) h50 chl_threshold_50 (by norm_num)
  by_cases h55 : n ≤ 61730399994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row55
      (show 9573 ≤ n by omega) h55 chl_threshold_55 (by norm_num)
  by_cases h60 : n ≤ 461510399994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row60
      (show 22027 ≤ n by omega) h60 chl_threshold_60 (by norm_num)
  by_cases h75 : n ≤ 1044257999994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row75
      (show 268338 ≤ n by omega) h75 chl_threshold_75 (by norm_num)
  by_cases h90 : n ≤ 1105823999994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row90
      (show 3269018 ≤ n by omega) h90 chl_threshold_90 (by norm_num)
  by_cases h105 : n ≤ 1151315999994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row105
      (show 39824785 ≤ n by omega) h105 chl_threshold_105 (by norm_num)
  by_cases h120 : n ≤ 1187501999994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row120
      (show 485165196 ≤ n by omega) h120 chl_threshold_120 (by norm_num)
  by_cases h135 : n ≤ 1215317999994
  · exact nat_short_of_CHL_integer_row hn (by norm_num) H.row135
      (show 5910522064 ≤ n by omega) h135 chl_threshold_135 (by norm_num)
  exact nat_short_of_CHL_integer_row hn (by norm_num) H.row150
    (show 72004899338 ≤ n by omega) hnhi chl_threshold_150 (by norm_num)

/-- The manuscript's safe joining point follows from a kernel-checked exp bound. -/
theorem lower_join_of_log {n : ℕ} (hn : 1 ≤ n)
    (hlog : Real.log ((n : ℝ) ^ 6) ≤ 167) : n ≤ 1242317999994 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hexp : (n : ℝ) ^ 6 ≤ Real.exp 167 := by
    calc (n : ℝ) ^ 6 = Real.exp (Real.log ((n : ℝ) ^ 6)) :=
      (Real.exp_log (pow_pos hnpos 6)).symm
      _ ≤ Real.exp 167 := Real.exp_le_exp.mpr hlog
  by_contra hbad
  have hNn : (1242317999994 : ℝ) ≤ n := by exact_mod_cast (show 1242317999994 ≤ n by omega)
  have hp : (1242317999994 : ℝ) ^ 6 ≤ (n : ℝ) ^ 6 :=
    pow_le_pow_left₀ (by norm_num) hNn 6
  linarith [lower_join_exp]

end LegendreK6
