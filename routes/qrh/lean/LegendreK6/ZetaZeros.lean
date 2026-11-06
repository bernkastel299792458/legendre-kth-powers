import Mathlib

/-!
# Actual zeta zeros and multiplicity-aware finite counts

All counts in this file refer to Mathlib's `riemannZeta`, with the analytic
order as multiplicity. No zero-density estimate or prime interval is assumed.
The zero at imaginary part zero is not excluded from `NontrivialZero`.
-/

namespace LegendreK6

open scoped BigOperators
open Complex Filter Topology ComplexConjugate

/-- The actual nontrivial zeros; no height restriction is built into this type. -/
def NontrivialZero := {ρ : ℂ // riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1}

/-- The true analytic multiplicity, defined for every complex argument. -/
noncomputable def zetaMultiplicity (ρ : ℂ) : ℕ :=
  analyticOrderNatAt riemannZeta ρ

theorem zeta_order_ne_top {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt riemannZeta ρ ≠ ⊤ := by
  apply analyticOn_riemannZeta.analyticOrderAt_ne_top_of_isPreconnected
    (x := (2 : ℂ))
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (by simp) (by simpa using hρ)
  rw [analyticOrderAt_eq_zero.mpr
    (Or.inr (riemannZeta_ne_zero_of_one_le_re (by norm_num : 1 ≤ (2 : ℂ).re)))]
  exact ENat.zero_ne_top

theorem zetaMultiplicity_pos {ρ : ℂ} (hz : riemannZeta ρ = 0) :
    0 < zetaMultiplicity ρ := by
  have hρ : ρ ≠ 1 := by
    intro h
    exact riemannZeta_one_ne_zero (h ▸ hz)
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ)
  have hne : analyticOrderAt riemannZeta ρ ≠ 0 := han.analyticOrderAt_ne_zero.mpr hz
  have htop := zeta_order_ne_top hρ
  apply Nat.pos_of_ne_zero
  intro h
  apply hne
  rw [← Nat.cast_analyticOrderNatAt htop]
  exact_mod_cast h

/-- All nontrivial zeros up to a closed absolute-height cutoff. -/
def zetaZeroRectangle (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T}

theorem zetaZeroRectangle_finite (T : ℝ) : (zetaZeroRectangle T).Finite := by
  apply ((isCompact_closedBall (0 : ℂ) (|T| + 1)).inter_riemannZetaZeros_finite).subset
  intro ρ hρ
  rcases hρ with ⟨hz, hre0, hre1, him⟩
  constructor
  · simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ |T| + 1 := by rw [abs_of_pos hre0]; linarith [le_abs_self T]
  · exact hz

/-- Actual nontrivial zeros with `|γ| ≤ T`, including any real-axis zeros. -/
noncomputable def allZetaZeros (T : ℝ) : Finset ℂ :=
  (zetaZeroRectangle_finite T).toFinset

@[simp] theorem mem_allZetaZeros {ρ : ℂ} {T : ℝ} :
    ρ ∈ allZetaZeros T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| ≤ T := by
  simp [allZetaZeros, zetaZeroRectangle]

/-- Positive heights, with the upper endpoint included, matching `0 < γ ≤ T`. -/
def positiveZetaZeroSet (T : ℝ) : Set ℂ :=
  {ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T}

theorem positiveZetaZeroSet_finite (T : ℝ) : (positiveZetaZeroSet T).Finite := by
  apply (zetaZeroRectangle_finite T).subset
  intro ρ hρ
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, by simpa [abs_of_pos hρ.2.2.2.1] using hρ.2.2.2.2⟩

noncomputable def positiveZetaZeros (T : ℝ) : Finset ℂ :=
  (positiveZetaZeroSet_finite T).toFinset

@[simp] theorem mem_positiveZetaZeros {ρ : ℂ} {T : ℝ} :
    ρ ∈ positiveZetaZeros T ↔
      riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ 0 < ρ.im ∧ ρ.im ≤ T := by
  simp [positiveZetaZeros, positiveZetaZeroSet]

/-- The actual positive-height zero count, counting multiplicities. -/
noncomputable def totalZeroCount (T : ℝ) : ℕ :=
  ∑ ρ ∈ positiveZetaZeros T, zetaMultiplicity ρ

/-- The actual density count with both `σ ≤ β` and `0 < γ ≤ T`. -/
noncomputable def densityZeroCount (σ T : ℝ) : ℕ := by
  classical
  exact ∑ ρ ∈ (positiveZetaZeros T).filter (fun ρ => σ ≤ ρ.re), zetaMultiplicity ρ

theorem positiveZetaZeros_mono {T U : ℝ} (hTU : T ≤ U) :
    positiveZetaZeros T ⊆ positiveZetaZeros U := by
  intro ρ hρ
  rw [mem_positiveZetaZeros] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.1, hρ.2.2.2.2.trans hTU⟩

theorem totalZeroCount_mono : Monotone totalZeroCount := by
  intro T U hTU
  apply Finset.sum_le_sum_of_subset
  exact positiveZetaZeros_mono hTU

theorem densityZeroCount_mono_height (σ : ℝ) : Monotone (densityZeroCount σ) := by
  classical
  intro T U hTU
  apply Finset.sum_le_sum_of_subset
  exact Finset.filter_subset_filter _ (positiveZetaZeros_mono hTU)

theorem densityZeroCount_antitone_sigma (T : ℝ) : Antitone (fun σ => densityZeroCount σ T) := by
  classical
  intro σ τ hστ
  apply Finset.sum_le_sum_of_subset
  intro ρ hρ
  simp only [Finset.mem_filter] at hρ ⊢
  exact ⟨hρ.1, hστ.trans hρ.2⟩

theorem densityZeroCount_le_total (σ T : ℝ) : densityZeroCount σ T ≤ totalZeroCount T := by
  classical
  exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

theorem totalZeroCount_cast (T : ℝ) :
    (totalZeroCount T : ℝ) = ∑ ρ ∈ positiveZetaZeros T, (zetaMultiplicity ρ : ℝ) := by
  simp [totalZeroCount]

theorem densityZeroCount_cast (σ T : ℝ) :
    (densityZeroCount σ T : ℝ) =
      ∑ ρ ∈ (positiveZetaZeros T).filter (fun ρ => σ ≤ ρ.re), (zetaMultiplicity ρ : ℝ) := by
  classical
  simp [densityZeroCount]

private theorem analyticAt_conjugate {f : ℂ → ℂ} {ρ : ℂ} (hf : AnalyticAt ℂ f ρ) :
    AnalyticAt ℂ (conj ∘ f ∘ conj) (conj ρ) := by
  apply analyticAt_iff_eventually_differentiableAt.mpr
  have hc : Tendsto (conj : ℂ → ℂ) (𝓝 (conj ρ)) (𝓝 ρ) := by
    simpa only [conj_conj] using continuous_conj.tendsto (conj ρ)
  filter_upwards [hc.eventually (analyticAt_iff_eventually_differentiableAt.mp hf)] with z hz
  exact differentiableAt_conj_conj_iff.mpr hz

/-- Conjugation preserves the actual analytic multiplicity of zeta zeros. -/
theorem zetaMultiplicity_conj (ρ : ℂ) (hρ : ρ ≠ 1) :
    zetaMultiplicity (conj ρ) = zetaMultiplicity ρ := by
  have han : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ (by simpa using hρ)
  have hc1 : conj ρ ≠ 1 := (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hρ
  have hanc : AnalyticAt ℂ riemannZeta (conj ρ) :=
    analyticOn_riemannZeta (conj ρ) (by simpa using hc1)
  obtain ⟨g, hg, hg0, hfg⟩ := han.analyticOrderAt_ne_top.mp (zeta_order_ne_top hρ)
  apply (hanc.analyticOrderNatAt_eq_iff (zeta_order_ne_top hc1)).mpr
  refine ⟨conj ∘ g ∘ conj, analyticAt_conjugate hg, ?_, ?_⟩
  · simpa using hg0
  · have hc : Tendsto (conj : ℂ → ℂ) (𝓝 (conj ρ)) (𝓝 ρ) := by
      simpa only [conj_conj] using continuous_conj.tendsto (conj ρ)
    filter_upwards [hfg.comp_tendsto hc] with z hz
    have hh := congrArg (conj : ℂ → ℂ) hz
    simpa [Function.comp_def, riemannZeta_conj, map_mul, map_sub, map_pow,
      smul_eq_mul, zetaMultiplicity] using hh

/-- The negative-height part of the absolute-height truncation. -/
noncomputable def negativeZetaZeros (T : ℝ) : Finset ℂ := by
  classical
  exact (allZetaZeros T).filter (fun ρ => ρ.im < 0)

/-- Real-axis zeros are retained explicitly until their absence is proved. -/
noncomputable def zeroHeightZetaZeros (T : ℝ) : Finset ℂ := by
  classical
  exact (allZetaZeros T).filter (fun ρ => ρ.im = 0)

theorem negativeZetaZeros_eq_conj_image (T : ℝ) :
    negativeZetaZeros T = (positiveZetaZeros T).image conj := by
  classical
  ext ρ
  simp only [negativeZetaZeros, Finset.mem_filter, mem_allZetaZeros, Finset.mem_image,
    mem_positiveZetaZeros]
  constructor
  · rintro ⟨⟨hz, hre0, hre1, himT⟩, him0⟩
    refine ⟨conj ρ, ?_, conj_conj ρ⟩
    simp only [riemannZeta_conj, hz, map_zero, conj_re, conj_im, true_and]
    exact ⟨hre0, hre1, by linarith, by simpa [abs_of_neg him0] using himT⟩
  · rintro ⟨z, ⟨hz, hre0, hre1, him0, himT⟩, rfl⟩
    simp only [riemannZeta_conj, hz, map_zero, conj_re, conj_im, abs_neg, true_and]
    exact ⟨⟨hre0, hre1, by simpa [abs_of_pos him0] using himT⟩, by linarith⟩

theorem allZetaZeros_partition (T : ℝ) :
    allZetaZeros T = positiveZetaZeros T ∪ negativeZetaZeros T ∪ zeroHeightZetaZeros T := by
  classical
  ext ρ
  simp only [Finset.mem_union, negativeZetaZeros, zeroHeightZetaZeros, Finset.mem_filter,
    mem_allZetaZeros, mem_positiveZetaZeros]
  constructor
  · rintro ⟨hz, hre0, hre1, himT⟩
    rcases lt_trichotomy ρ.im 0 with hneg | hzero | hpos
    · exact Or.inl (Or.inr ⟨⟨hz, hre0, hre1, himT⟩, hneg⟩)
    · exact Or.inr ⟨⟨hz, hre0, hre1, himT⟩, hzero⟩
    · exact Or.inl (Or.inl ⟨hz, hre0, hre1, hpos, (le_abs_self _).trans himT⟩)
  · rintro ((hpos | hneg) | hzero)
    · exact ⟨hpos.1, hpos.2.1, hpos.2.2.1,
        by simpa [abs_of_pos hpos.2.2.2.1] using hpos.2.2.2.2⟩
    · exact hneg.1
    · exact hzero.1

/-- Positive and negative heights give equal weighted sums for a conjugation-invariant weight.
The real-axis term is not silently discarded. -/
theorem sum_allZetaZeros_conj_invariant (T : ℝ) (f : ℂ → ℝ)
    (hf : ∀ ρ, f (conj ρ) = f ρ) :
    (∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ) =
      2 * (∑ ρ ∈ positiveZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ) +
        ∑ ρ ∈ zeroHeightZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ := by
  classical
  have hpn : Disjoint (positiveZetaZeros T) (negativeZetaZeros T) := by
    apply Finset.disjoint_left.mpr
    intro ρ hp hn
    have hp0 := (mem_positiveZetaZeros.mp hp).2.2.2.1
    have hn0 := (Finset.mem_filter.mp hn).2
    linarith
  have haxis : Disjoint (positiveZetaZeros T ∪ negativeZetaZeros T) (zeroHeightZetaZeros T) := by
    apply Finset.disjoint_left.mpr
    intro ρ hpn hz
    have hz0 := (Finset.mem_filter.mp hz).2
    rcases Finset.mem_union.mp hpn with hp | hn
    · have hp0 := (mem_positiveZetaZeros.mp hp).2.2.2.1
      linarith
    · have hn0 := (Finset.mem_filter.mp hn).2
      linarith
  have hn : (∑ ρ ∈ negativeZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ) =
      ∑ ρ ∈ positiveZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ := by
    rw [negativeZetaZeros_eq_conj_image, Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro ρ hρ
      have hre := (mem_positiveZetaZeros.mp hρ).2.2.1
      have hne : ρ ≠ 1 := by intro h; simp [h] at hre
      rw [zetaMultiplicity_conj ρ hne, hf]
    · intro a _ b _ h
      exact (starRingEnd ℂ).injective h
  rw [allZetaZeros_partition, Finset.sum_union haxis, Finset.sum_union hpn, hn]
  ring

/-- Exact interface for a separately proved real-axis nonvanishing theorem.
This lemma does not assert that nonvanishing theorem. -/
theorem zeroHeightZetaZeros_eq_empty_of_nonvanishing
    (hreal : ∀ r : ℝ, 0 < r → r < 1 → riemannZeta (r : ℂ) ≠ 0) (T : ℝ) :
    zeroHeightZetaZeros T = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro ρ hρ
  obtain ⟨hall, him⟩ := Finset.mem_filter.mp hρ
  obtain ⟨hz, hre0, hre1, _⟩ := mem_allZetaZeros.mp hall
  have hρreal : (ρ.re : ℂ) = ρ := by
    apply Complex.ext <;> simp [him]
  apply hreal ρ.re hre0 hre1
  simpa [hρreal] using hz

/-- The usual factor of two is justified only after real-axis nonvanishing is supplied. -/
theorem sum_allZetaZeros_eq_twice_of_nonvanishing
    (hreal : ∀ r : ℝ, 0 < r → r < 1 → riemannZeta (r : ℂ) ≠ 0)
    (T : ℝ) (f : ℂ → ℝ) (hf : ∀ ρ, f (conj ρ) = f ρ) :
    (∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ) =
      2 * ∑ ρ ∈ positiveZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ := by
  rw [sum_allZetaZeros_conj_invariant T f hf,
    zeroHeightZetaZeros_eq_empty_of_nonvanishing hreal T]
  simp

private noncomputable def zetaModifiedKernel (t : ℝ) : ℂ :=
  (HurwitzZeta.hurwitzEvenFEPair 0).f_modif t

private theorem evenKernel_sub_one_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ HurwitzZeta.evenKernel 0 t - 1 := by
  have hs := HurwitzZeta.hasSum_int_evenKernel₀ 0 ht
  simp only [add_zero, AddCircle.coe_zero, ite_true] at hs
  exact hs.nonneg (fun n => by split_ifs <;> positivity)

private theorem zetaModifiedKernel_real (t : ℝ) :
    zetaModifiedKernel t = ((zetaModifiedKernel t).re : ℂ) := by
  simp only [zetaModifiedKernel, WeakFEPair.f_modif, Pi.add_apply,
    HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, ite_true,
    one_mul, smul_eq_mul, mul_one, Set.indicator_apply]
  split_ifs <;> simp

private theorem zetaModifiedKernel_nonneg {t : ℝ} (ht : 0 < t) :
    0 ≤ (zetaModifiedKernel t).re := by
  rcases lt_trichotomy t 1 with hlt | heq | hgt
  · have htinv : 0 < 1 / t := one_div_pos.mpr ht
    have hn := evenKernel_sub_one_nonneg htinv
    have hk := HurwitzZeta.evenKernel_functional_equation 0 t
    rw [← HurwitzZeta.evenKernel_eq_cosKernel_of_zero] at hk
    have hp : 0 < t ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos ht _
    have hmul : 0 ≤ (1 / t ^ ((1 : ℝ) / 2)) * (HurwitzZeta.evenKernel 0 (1 / t) - 1) :=
      mul_nonneg (le_of_lt (one_div_pos.mpr hp)) hn
    simp only [zetaModifiedKernel, WeakFEPair.f_modif, Pi.add_apply,
      HurwitzZeta.hurwitzEvenFEPair, Function.comp_apply, ite_true,
      one_mul, smul_eq_mul, mul_one, Set.indicator_apply]
    simp only [Set.mem_Ioi, Set.mem_Ioo, hlt.not_gt, ht, hlt, and_self,
      ite_false, ite_true, zero_add, sub_re, ofReal_re]
    rw [hk, Real.rpow_neg ht.le, one_div]
    simpa [mul_sub] using hmul
  · subst t
    simp [zetaModifiedKernel, WeakFEPair.f_modif]
  · simpa [zetaModifiedKernel, WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair,
      hgt, not_lt.mpr hgt.le, Set.mem_Ioi, Set.mem_Ioo, Set.indicator_apply]
      using evenKernel_sub_one_nonneg (zero_lt_one.trans hgt)

private theorem zetaModifiedKernel_integrable (s : ℂ) :
    MellinConvergent zetaModifiedKernel s := by
  exact ((HurwitzZeta.hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin s).1

private noncomputable def zetaRealKernelPower (s t : ℝ) : ℝ :=
  t ^ (s / 2 - 1) * (zetaModifiedKernel t).re

private theorem zetaRealKernelPower_coe (s : ℝ) {t : ℝ} (ht : 0 < t) :
    (zetaRealKernelPower s t : ℂ) =
      (t : ℂ) ^ ((s : ℂ) / 2 - 1) • zetaModifiedKernel t := by
  rw [zetaRealKernelPower, ofReal_mul, ofReal_cpow ht.le]
  push_cast
  rw [smul_eq_mul, ← zetaModifiedKernel_real]

private theorem zetaRealKernelPower_integrable (s : ℝ) :
    MeasureTheory.IntegrableOn (zetaRealKernelPower s) (Set.Ioi 0) := by
  have hi := zetaModifiedKernel_integrable ((s : ℂ) / 2)
  have hr := hi.re
  apply hr.congr
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
  exact (congrArg Complex.re (zetaRealKernelPower_coe s ht)).symm

private theorem completedZeta₀_re_integral (s : ℝ) :
    (completedRiemannZeta₀ (s : ℂ)).re =
      (∫ t in Set.Ioi 0, zetaRealKernelPower s t) / 2 := by
  have heq : (∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ ((s : ℂ) / 2 - 1) • zetaModifiedKernel t) =
      Complex.ofReal (∫ t in Set.Ioi 0, zetaRealKernelPower s t) := by
    calc
      _ = ∫ t : ℝ in Set.Ioi 0, (zetaRealKernelPower s t : ℂ) := by
        apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        exact (zetaRealKernelPower_coe s ht).symm
      _ = _ := integral_complex_ofReal
  change ((∫ t : ℝ in Set.Ioi 0, (t : ℂ) ^ ((s : ℂ) / 2 - 1) • zetaModifiedKernel t) / 2).re = _
  rw [heq]
  simp

private theorem zetaRealKernelPower_le {s t : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (ht : 0 < t) :
    zetaRealKernelPower s t ≤ zetaRealKernelPower 2 t + zetaRealKernelPower (-1) t := by
  unfold zetaRealKernelPower
  rw [← add_mul]
  apply mul_le_mul_of_nonneg_right _ (zetaModifiedKernel_nonneg ht)
  by_cases ht1 : 1 ≤ t
  · have h := Real.rpow_le_rpow_of_exponent_le ht1 (show s / 2 - 1 ≤ (2 : ℝ) / 2 - 1 by linarith)
    exact h.trans (le_add_of_nonneg_right (Real.rpow_nonneg ht.le _))
  · have h := Real.rpow_le_rpow_of_exponent_ge ht (le_of_not_ge ht1)
      (show (-1 : ℝ) / 2 - 1 ≤ s / 2 - 1 by linarith)
    exact h.trans (le_add_of_nonneg_left (Real.rpow_nonneg ht.le _))

private theorem completedZeta₀_re_le_twice_two {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (completedRiemannZeta₀ (s : ℂ)).re ≤ 2 * (completedRiemannZeta₀ 2).re := by
  have hi := MeasureTheory.setIntegral_mono_on (zetaRealKernelPower_integrable s)
    ((zetaRealKernelPower_integrable 2).add (zetaRealKernelPower_integrable (-1)))
    measurableSet_Ioi (fun t ht => zetaRealKernelPower_le hs0 hs1 ht)
  simp only [Pi.add_apply] at hi
  rw [MeasureTheory.integral_add (zetaRealKernelPower_integrable 2)
    (zetaRealKernelPower_integrable (-1))] at hi
  have heq : completedRiemannZeta₀ (-1) = completedRiemannZeta₀ 2 := by
    convert completedRiemannZeta₀_one_sub (2 : ℂ) using 1; norm_num
  have h0 := completedZeta₀_re_integral s
  have h2 := completedZeta₀_re_integral 2
  have hn := completedZeta₀_re_integral (-1)
  norm_num only [ofReal_ofNat, ofReal_neg, ofReal_one] at h2 hn
  rw [heq] at hn
  linarith

private theorem completedZeta₀_two_value :
    completedRiemannZeta₀ 2 = (Real.pi : ℂ) / 6 - 1 / 2 := by
  have hg : Gammaℝ 2 = (Real.pi : ℂ)⁻¹ := by
    norm_num [Gammaℝ_def, cpow_neg_one, Gamma_one]
  have hc : completedRiemannZeta 2 = (Real.pi : ℂ) / 6 := by
    have hz := riemannZeta_def_of_ne_zero (s := (2 : ℂ)) (by norm_num)
    have hg0 : Gammaℝ 2 ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num)
    have heq := (div_eq_iff hg0).mp hz.symm
    rw [riemannZeta_two, hg] at heq
    rw [heq]
    field_simp
  have heq := completedRiemannZeta_eq (2 : ℂ)
  rw [hc] at heq
  norm_num at heq
  linear_combination -heq

/-- The actual zeta function has no zeros on the real interval `(0,1)`.
The proof uses the positive modified theta kernel defining the completed zeta,
its Mellin integral and the known value at two, without a literature assumption. -/
theorem riemannZeta_ne_zero_real_strip {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    riemannZeta (s : ℂ) ≠ 0 := by
  intro hz
  have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hg0 : Gammaℝ (s : ℂ) ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by simpa using hs0)
  have hc : completedRiemannZeta (s : ℂ) = 0 := by
    have heq := riemannZeta_def_of_ne_zero hsne
    rw [hz] at heq
    exact (div_eq_zero_iff.mp heq.symm).resolve_right hg0
  have heq := completedRiemannZeta_eq (s : ℂ)
  rw [hc] at heq
  have hr0 : completedRiemannZeta₀ (s : ℂ) =
      Complex.ofReal (1 / s + 1 / (1 - s)) := by
    push_cast
    linear_combination -heq
  have hr := congrArg Complex.re hr0
  have hbound := completedZeta₀_re_le_twice_two hs0.le hs1.le
  rw [completedZeta₀_two_value] at hbound
  norm_num [div_re, ofReal_re, ofReal_im] at hbound
  simp only [ofReal_re] at hr
  have hspos : 0 < 1 - s := sub_pos.mpr hs1
  have hbudget : (4 : ℝ) ≤ 1 / s + 1 / (1 - s) := by
    have hid : 1 / s + 1 / (1 - s) = 1 / (s * (1 - s)) := by
      field_simp
      ring
    rw [hid]
    apply (le_div_iff₀ (mul_pos hs0 hspos)).mpr
    nlinarith [sq_nonneg (2 * s - 1)]
  linarith [Real.pi_lt_four]

theorem zeroHeightZetaZeros_eq_empty (T : ℝ) : zeroHeightZetaZeros T = ∅ :=
  zeroHeightZetaZeros_eq_empty_of_nonvanishing
    (fun _ h0 h1 => riemannZeta_ne_zero_real_strip h0 h1) T

/-- Multiplicity-aware positive/negative-height pairing, with the real-axis case proved absent. -/
theorem sum_allZetaZeros_eq_twice (T : ℝ) (f : ℂ → ℝ) (hf : ∀ ρ, f (conj ρ) = f ρ) :
    (∑ ρ ∈ allZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ) =
      2 * ∑ ρ ∈ positiveZetaZeros T, (zetaMultiplicity ρ : ℝ) * f ρ :=
  sum_allZetaZeros_eq_twice_of_nonvanishing
    (fun _ h0 h1 => riemannZeta_ne_zero_real_strip h0 h1) T f hf

theorem nontrivialZero_im_ne_zero (ρ : NontrivialZero) : ρ.1.im ≠ 0 := by
  intro him
  have hreal : (ρ.1.re : ℂ) = ρ.1 := by apply Complex.ext <;> simp [him]
  apply riemannZeta_ne_zero_real_strip ρ.2.2.1 ρ.2.2.2
  simpa [hreal] using ρ.2.1

theorem nontrivialZero_ne_zero (ρ : NontrivialZero) : ρ.1 ≠ 0 := by
  intro h
  have hp := ρ.2.2.1
  simp [h] at hp

theorem allZetaZeros_mono {T U : ℝ} (hTU : T ≤ U) : allZetaZeros T ⊆ allZetaZeros U := by
  intro ρ hρ
  rw [mem_allZetaZeros] at hρ ⊢
  exact ⟨hρ.1, hρ.2.1, hρ.2.2.1, hρ.2.2.2.trans hTU⟩

theorem positiveZetaZeros_subset_all (T : ℝ) : positiveZetaZeros T ⊆ allZetaZeros T := by
  intro ρ hρ
  obtain ⟨hz, hre0, hre1, him0, himT⟩ := mem_positiveZetaZeros.mp hρ
  exact mem_allZetaZeros.mpr ⟨hz, hre0, hre1, by simpa [abs_of_pos him0] using himT⟩

theorem all_zero_multiplicities_eq_twice_total (T : ℝ) :
    (∑ ρ ∈ allZetaZeros T, zetaMultiplicity ρ) = 2 * totalZeroCount T := by
  have h := sum_allZetaZeros_eq_twice T (fun _ => 1) (fun _ => rfl)
  simp only [mul_one] at h
  unfold totalZeroCount
  exact_mod_cast h

end LegendreK6
