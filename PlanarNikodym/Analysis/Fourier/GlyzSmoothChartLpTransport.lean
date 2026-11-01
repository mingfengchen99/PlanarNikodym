import PlanarNikodym.Analysis.Fourier.GlyzSmoothChartBounds
import Mathlib.MeasureTheory.Measure.Haar.Disintegration

/-! Exact transport of output cutoffs through a smooth nonlinear chart,
anisotropic dilation, and arbitrary fixed Euclidean coefficient coordinates. -/
noncomputable section
open Set Filter MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal ContDiff
namespace PlanarNikodym

theorem exists_glyz_linear_equiv_lintegral_factor
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (T : E ≃L[ℝ] F) (μ : Measure E) (ν : Measure F)
    [IsAddHaarMeasure μ] [IsAddHaarMeasure ν] :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ f : F → ℝ≥0∞,
      (∫⁻ x, f (T x) ∂μ) = c * ∫⁻ y, f y ∂ν := by
  let c := addHaarScalarFactor (μ.map T) ν
  have hc : 0 < c := addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map T) ν
  refine ⟨c, hc, fun f => ?_⟩
  have h := lintegral_map_equiv f T.toHomeomorph.toMeasurableEquiv (μ := μ)
  change (∫⁻ y, f y ∂μ.map T) = ∫⁻ x, f (T x) ∂μ at h
  rw [isAddLeftInvariant_eq_smul (μ.map T) ν, lintegral_smul_measure] at h
  exact h.symm

theorem exists_glyz_retained_cutoff_jacobian_bounds
    {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [CompleteSpace P] {m : ℕ}
    (e : OpenPartialHomeomorph (P × Aux m) (P × Aux m))
    (he : ∀ x, (e x).1 = x.1)
    (ha : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x)
    (hb : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x)
    (ρ : P × Aux m → ℝ) (hcρ : HasCompactSupport ρ) (hρT : tsupport ρ ⊆ e.target) :
    ∃ b C : ℝ, 0 < b ∧ 0 < C ∧ ∀ q z, (q, z) ∈ e.source →
      ρ (q, (e (q, z)).2) ≠ 0 →
      b ≤ |LinearMap.det (fderiv ℝ (retainedParameterFiber e he q) z).toLinearMap| ∧
        |LinearMap.det (fderiv ℝ (retainedParameterFiber e he q) z).toLinearMap| ≤ C := by
  let K := e.symm '' tsupport ρ
  have hK : IsCompact K := hcρ.isCompact.image_of_continuousOn (e.symm.continuousOn.mono hρT)
  have hKS : K ⊆ e.source := by
    rintro _ ⟨y, hy, rfl⟩
    exact e.map_target (hρT hy)
  obtain ⟨b, C, hb0, hC0, hJ⟩ := exists_glyz_uniform_fiberChartJacobian_bounds e he ha hb hK hKS
  refine ⟨b, C, hb0, hC0, fun q z hz hρ => ?_⟩
  have hmem : (q, z) ∈ K := by
    refine ⟨e (q, z), ?_, e.left_inv hz⟩
    have hp : (q, (e (q, z)).2) = e (q, z) := Prod.ext (he (q, z)).symm rfl
    rw [← hp]
    exact subset_tsupport _ hρ
  exact hJ (q, z) hmem

theorem glyz_lintegral_scaled_chart_cutoff {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x)
    (σ : Aux (n + 1) → ℂ) (hσ : Function.support σ ⊆ e.target)
    (O : Aux (n + 1) → ℂ) {p : ℝ} (hp : 0 < p) (δ : ℝ) (hδ : δ ≠ 0) :
    (∫⁻ w, ‖σ ((lowerDegreeDilation n δ hδ).symm w) *
      O (e.symm ((lowerDegreeDilation n δ hδ).symm w))‖ₑ ^ p) =
      ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| *
        ∫⁻ z in e.source, ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| *
          ‖σ (e z) * O z‖ₑ ^ p := by
  let D := lowerDegreeDilation n δ hδ
  let F := fun w : Aux (n + 1) => ‖σ (D.symm w) * O (e.symm (D.symm w))‖ₑ ^ p
  have hs : Function.support F ⊆ D '' e.target := by
    intro w hw
    have hσw : σ (D.symm w) ≠ 0 := by
      intro hz
      apply hw
      simp only [F, hz, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hp]
    exact ⟨D.symm w, hσ hσw, D.apply_symm_apply w⟩
  change (∫⁻ w, F w) = _
  rw [← setLIntegral_eq_of_support_subset hs,
    glyz_lintegral_scaled_smooth_chart_target e he δ hδ F]
  congr 1
  apply setLIntegral_congr_fun e.open_source.measurableSet
  intro z hz
  simp only [F, D, ContinuousLinearEquiv.symm_apply_apply, e.left_inv hz]

theorem exists_glyz_euclidean_chart_transport_factor
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasureSpace E] [BorelSpace E] [IsAddHaarMeasure (volume : Measure E)]
    {n : ℕ} (T : E ≃L[ℝ] Aux (n + 1)) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1))),
      (∀ x ∈ e.source, ContDiffAt ℝ ∞ e x) →
      ∀ (σ : Aux (n + 1) → ℂ), Function.support σ ⊆ e.target →
      ∀ (O : Aux (n + 1) → ℂ) (p : ℝ), 0 < p → ∀ (δ : ℝ) (hδ : δ ≠ 0),
      (∫⁻ x, ‖σ ((lowerDegreeDilation n δ hδ).symm (T x)) *
        O (e.symm ((lowerDegreeDilation n δ hδ).symm (T x)))‖ₑ ^ p) =
        c * ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| *
          ∫⁻ z in e.source, ENNReal.ofReal |LinearMap.det (fderiv ℝ e z).toLinearMap| *
            ‖σ (e z) * O z‖ₑ ^ p := by
  obtain ⟨c, hc, hmap⟩ := exists_glyz_linear_equiv_lintegral_factor T volume volume
  refine ⟨c, hc, fun e he σ hσ O p hp δ hδ => ?_⟩
  rw [hmap (fun w => ‖σ ((lowerDegreeDilation n δ hδ).symm w) *
    O (e.symm ((lowerDegreeDilation n δ hδ).symm w))‖ₑ ^ p),
    glyz_lintegral_scaled_chart_cutoff e he σ hσ O hp δ hδ, mul_assoc]

theorem glyz_lintegral_scaled_chart_cutoff_bounds {n : ℕ}
    (e : OpenPartialHomeomorph (Aux (n + 1)) (Aux (n + 1)))
    (he : ∀ x ∈ e.source, ContDiffAt ℝ ∞ e x)
    (σ : Aux (n + 1) → ℂ) (hσ : Function.support σ ⊆ e.target)
    (O : Aux (n + 1) → ℂ) {p : ℝ} (hp : 0 < p) (δ : ℝ) (hδ : δ ≠ 0)
    (b C : ℝ)
    (hJ : ∀ z ∈ e.source, σ (e z) ≠ 0 →
      b ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap| ∧
        |LinearMap.det (fderiv ℝ e z).toLinearMap| ≤ C) :
    ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| *
      (ENNReal.ofReal b * ∫⁻ z in e.source, ‖σ (e z) * O z‖ₑ ^ p) ≤
        (∫⁻ w, ‖σ ((lowerDegreeDilation n δ hδ).symm w) *
          O (e.symm ((lowerDegreeDilation n δ hδ).symm w))‖ₑ ^ p) ∧
    (∫⁻ w, ‖σ ((lowerDegreeDilation n δ hδ).symm w) *
      O (e.symm ((lowerDegreeDilation n δ hδ).symm w))‖ₑ ^ p) ≤
      ENNReal.ofReal |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| *
        (ENNReal.ofReal C * ∫⁻ z in e.source, ‖σ (e z) * O z‖ₑ ^ p) := by
  rw [glyz_lintegral_scaled_chart_cutoff e he σ hσ O hp δ hδ]
  constructor
  · apply mul_le_mul_right
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' e.open_source.measurableSet
    intro z hz
    by_cases hs : σ (e z) = 0
    · simp only [hs, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hp, mul_zero, le_refl]
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ z hz hs).1) _
  · apply mul_le_mul_right
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    apply setLIntegral_mono' e.open_source.measurableSet
    intro z hz
    by_cases hs : σ (e z) = 0
    · simp only [hs, zero_mul, enorm_zero, ENNReal.zero_rpow_of_pos hp, mul_zero, le_refl]
    · exact mul_le_mul_left (ENNReal.ofReal_le_ofReal (hJ z hz hs).2) _

theorem glyz_lowerDegreeDilation_abs_det_ge_one (n : ℕ) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ |∏ i : Fin (n + 1), δ ^ (i : ℕ) / δ ^ n| := by
  apply le_trans _ (le_abs_self _)
  exact Finset.one_le_prod fun i _ => one_le_lowerDegreeWeight n hδ hδ1 i

/-- Cancellation of the common chart and parabolic scale factors is
valid also for zero and infinite energies. Only geometric factors must
be finite and positive. -/
theorem glyz_transport_power_bound {ι : Type*} (I : Finset ι)
    (X L D err S κ b C : ℝ≥0∞) (Y P : ι → ℝ≥0∞)
    (hκ0 : κ ≠ 0) (hκT : κ ≠ ⊤) (hb0 : b ≠ 0) (hbT : b ≠ ⊤)
    (hlow : κ * (b * X) ≤ S * L)
    (hupp : ∀ i ∈ I, S * P i ≤ κ * (C * Y i))
    (hbound : L ≤ D * ∑ i ∈ I, P i + err) :
    X ≤ b⁻¹ * D * C * ∑ i ∈ I, Y i + b⁻¹ * κ⁻¹ * S * err := by
  have h : κ * (b * X) ≤ κ * (D * C * ∑ i ∈ I, Y i) + S * err := by
    apply hlow.trans
    calc
      S * L ≤ S * (D * ∑ i ∈ I, P i + err) := mul_le_mul_right hbound S
      _ = D * (∑ i ∈ I, S * P i) + S * err := by
        rw [mul_add, ← Finset.mul_sum]
        ac_rfl
      _ ≤ D * (∑ i ∈ I, κ * (C * Y i)) + S * err :=
        add_le_add (mul_le_mul_right (Finset.sum_le_sum hupp) D) le_rfl
      _ = _ := by
        rw [← Finset.mul_sum, ← Finset.mul_sum]
        ac_rfl
  calc
    X = b⁻¹ * (κ⁻¹ * (κ * (b * X))) := by
      rw [ENNReal.inv_mul_cancel_left hκ0 hκT, ENNReal.inv_mul_cancel_left hb0 hbT]
    _ ≤ b⁻¹ * (κ⁻¹ * (κ * (D * C * ∑ i ∈ I, Y i) + S * err)) := by gcongr
    _ = _ := by
      rw [mul_add, ENNReal.inv_mul_cancel_left hκ0 hκT, mul_add]
      ac_rfl

end PlanarNikodym
