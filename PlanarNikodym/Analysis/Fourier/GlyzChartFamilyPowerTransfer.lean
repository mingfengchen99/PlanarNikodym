import PlanarNikodym.Analysis.Fourier.GlyzSmoothChartLpTransport

/-! Transport of finite families through the exact smooth chart model.
The common dilation and Haar factors cancel from the main coefficient. -/
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal ContDiff BigOperators
namespace PlanarNikodym

theorem glyz_lintegral_smul_power
    {E : Type} [MeasurableSpace E] (μ : Measure E) (F : E → ℂ)
    {δ : ℝ} (hδ : 0 < δ) {p : ℝ} (hp : 0 ≤ p) :
    (∫⁻ x, ‖δ • F x‖ₑ ^ p ∂μ) = ENNReal.ofReal δ ^ p * ∫⁻ x, ‖F x‖ₑ ^ p ∂μ := by
  simp_rw [enorm_smul, ← ofReal_norm, Real.norm_eq_abs, abs_of_pos hδ,
    ENNReal.mul_rpow_of_nonneg _ _ hp]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp ENNReal.ofReal_ne_top)]

theorem exists_glyz_chart_family_transfer_factor
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {n : ℕ} (T : E ≃L[ℝ] Aux (n + 1)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ {ι : Type} (I : Finset ι)
      (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1))),
      (∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) →
      ∀ (σ : Aux (n + 1) → ℂ), Function.support σ ⊆ e.target →
      ∀ (b C : ℝ), 0 < b →
      (∀ z ∈ e.source, σ (e z) ≠ 0 →
        b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap| ∧
          |LinearMap.det (fderiv ℝ e z).toLinearMap| ≤ C) →
      ∀ (p δ : ℝ) (_hp : 0 < p) (hδ : 0 < δ),
      ∀ (F : ι → E → ℂ) (O : ι → Aux (n + 1) → ℂ),
      (∀ i ∈ I, ∀ x, δ • F i x =
        σ ((lowerDegreeDilation n δ hδ.ne').symm (T x)) *
          O i (e.symm ((lowerDegreeDilation n δ hδ.ne').symm (T x)))) →
      ∀ (D err : ℝ≥0∞),
      (∫⁻ x, ‖∑ i ∈ I, F i x‖ₑ ^ p) ≤
        D * ∑ i ∈ I, (∫⁻ x, ‖F i x‖ₑ ^ p) + err →
      (∫⁻ z in e.source, ‖∑ i ∈ I, σ (e z) * O i z‖ₑ ^ p) ≤
        (ENNReal.ofReal b)⁻¹ * D * ENNReal.ofReal C *
          ∑ i ∈ I, (∫⁻ z in e.source, ‖σ (e z) * O i z‖ₑ ^ p) +
        (ENNReal.ofReal b)⁻¹ *
          ((c : ℝ≥0∞) * ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|)⁻¹ *
          ENNReal.ofReal δ ^ p * err := by
  obtain ⟨c, hc, htransport⟩ := exists_glyz_euclidean_chart_transport_factor T
  refine ⟨c, hc, fun I e he σ hσ b C hb hJ p δ hp hδ F O hrep D err hbound => ?_⟩
  let S : ℝ≥0∞ := ENNReal.ofReal δ ^ p
  let κ : ℝ≥0∞ := c * ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n|
  have hκ0 : κ ≠ 0 := by
    apply mul_ne_zero
    · exact_mod_cast hc.ne'
    · apply ENNReal.ofReal_ne_zero_iff.mpr
      apply abs_pos.mpr
      exact Finset.prod_ne_zero_iff.mpr fun i _ => div_ne_zero (pow_ne_zero _ hδ.ne') (pow_ne_zero _ hδ.ne')
  have hκT : κ ≠ ⊤ := ENNReal.mul_ne_top ENNReal.coe_ne_top ENNReal.ofReal_ne_top
  have hscaled (f : E → ℂ) (o : Aux (n + 1) → ℂ)
      (hr : ∀ x, δ • f x = σ ((lowerDegreeDilation n δ hδ.ne').symm (T x)) *
        o (e.symm ((lowerDegreeDilation n δ hδ.ne').symm (T x)))) :
      S * (∫⁻ x, ‖f x‖ₑ ^ p) = κ * ∫⁻ z in e.source,
        ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| * ‖σ (e z) * o z‖ₑ ^ p := by
    rw [← glyz_lintegral_smul_power volume f hδ hp.le]
    simp_rw [hr]
    exact htransport e he σ hσ o p hp δ hδ.ne'
  have hsumrep (x : E) : δ • (∑ i ∈ I, F i x) =
      σ ((lowerDegreeDilation n δ hδ.ne').symm (T x)) *
        (∑ i ∈ I, O i (e.symm ((lowerDegreeDilation n δ hδ.ne').symm (T x)))) := by
    rw [Finset.smul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i hi => hrep i hi x
  have hsum : (∫⁻ z in e.source, ‖∑ i ∈ I, σ (e z) * O i z‖ₑ ^ p) =
      ∫⁻ z in e.source, ‖σ (e z) * (∑ i ∈ I, O i z)‖ₑ ^ p := by
    simp_rw [Finset.mul_sum]
  rw [hsum]
  apply glyz_transport_power_bound I _ _ D err S κ (ENNReal.ofReal b) (ENNReal.ofReal C)
    (fun i => ∫⁻ z in e.source, ‖σ (e z) * O i z‖ₑ ^ p)
    (fun i => ∫⁻ x, ‖F i x‖ₑ ^ p) hκ0 hκT
    (ENNReal.ofReal_ne_zero_iff.mpr hb) ENNReal.ofReal_ne_top
  · rw [hscaled (fun x => ∑ i ∈ I, F i x) (fun z => ∑ i ∈ I, O i z) hsumrep]
    apply mul_le_mul_right
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' e.open_source.measurableSet
    intro z hz
    by_cases hsz : σ (e z) = 0
    · simp only [hsz, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hp, mul_zero, le_refl]
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ z hz hsz).1) _
  · intro i hi
    rw [hscaled (F i) (O i) (hrep i hi)]
    apply mul_le_mul_right
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' e.open_source.measurableSet
    intro z hz
    by_cases hsz : σ (e z) = 0
    · simp only [hsz, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hp, mul_zero, le_refl]
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ z hz hsz).2) _
  · exact hbound

end PlanarNikodym
