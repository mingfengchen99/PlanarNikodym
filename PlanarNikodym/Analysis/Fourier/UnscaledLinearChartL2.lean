import PlanarNikodym.Analysis.Fourier.DilatedAmplitudeConeL2
import PlanarNikodym.Analysis.Fourier.UnscaledLinearTimeSlice
import PlanarNikodym.Analysis.Fourier.UnscaledChartLp
import PlanarNikodym.Analysis.Fourier.TimeDataL2Rescaling

/-! Pullback of the proved variable-amplitude estimate through a genuine
nonlinear lower-jet chart. The actual time Jacobian and the input and
output inverse Jacobians cancel, leaving no loss in the time scale. -/

noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem stronglyMeasurable_dilatedAmplitudeConeExtension
    (b : SchwartzMap (Plane × Plane) ℂ) {h : Plane → ℂ}
    (hh : Measurable h) (r δ : ℝ) :
    StronglyMeasurable (dilatedAmplitudeConeExtension (fun w x => b (w, x)) h r δ) := by
  have hb : Continuous (fun x : (Plane × ℝ) × ℝ => b (x.1.1, (x.2, x.1.2))) :=
    b.continuous.comp (by fun_prop)
  have harg : Continuous (fun x : (Plane × ℝ) × ℝ =>
      (r • coneOutputDilation δ x.1.1, (x.1.2, x.1.2 * x.2))) := by
    unfold coneOutputDilation
    fun_prop
  have hp : Continuous (fun x : (Plane × ℝ) × ℝ =>
      planeFourierCharacter (r • coneOutputDilation δ x.1.1) (x.1.2, x.1.2 * x.2)) :=
    continuous_planeFourierCharacter.comp harg
  have hf := (hb.stronglyMeasurable.mul (hh.stronglyMeasurable.comp_measurable
    (measurable_snd.prodMk measurable_fst.snd))).mul hp.stronglyMeasurable
  exact hf.integral_prod_right'.integral_prod_right'

/-- Exact original-slice representation using a supplied actual smooth
amplitude, requiring agreement only where the genuine input is nonzero. -/
theorem Family.timeSliceExtension_eq_dilatedAmplitudeConeExtension
    {d : ℕ} (G : Family 2 d) (hm : 2 ≤ d + 2)
    (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (e : OpenPartialHomeomorph (Aux 2) (Aux 2))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (h : Plane → ℂ) (r : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (b : SchwartzMap (Plane × Plane) ℂ)
    {y : Aux 2} (hy : y ∈ e.target)
    (hb : ∀ τ η, h (c + δ * τ, η) ≠ 0 →
      b (((y 0, y 1) : Plane), (τ, η)) =
        actualTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          1 (2 * Real.pi * r) c δ
          (parameterFrame d (v + coordinateInsertion σ (e.symm y))) τ η) :
    timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h
      (2 * Real.pi * r) c δ (parameterFrame d (v + coordinateInsertion σ (e.symm y))) =
      δ • dilatedAmplitudeConeExtension (fun w x => b (w, x))
        (fun x => h (timeDataRescaling c δ x)) r δ (y 0, y 1) := by
  rw [G.timeSliceExtension_in_unscaled_linear_chart hm σ v c e he ha a h r hδ hy]
  congr 1
  unfold dilatedAmplitudeConeExtension
  apply integral_congr_ae
  filter_upwards [] with η
  apply integral_congr_ae
  filter_upwards [] with τ
  by_cases hh : h (c + δ * τ, η) = 0
  · simp only [timeDataRescaling, hh, mul_zero, zero_mul]
  · rw [hb τ η hh]
    rfl

/-- Squared L² pullback for the actual last-stage slice. The amplitude
agreement is a geometric identity, while the operator bound is proved
from Fourier inversion, the cone Jacobian and Plancherel. -/
theorem Family.lintegral_timeSliceExtension_unscaled_linear_chart_sq_le
    {d : ℕ} (G : Family 2 d) (hm : 2 ≤ d + 2)
    (σ : Fin 2 ↪ Fin (d + 2)) (v : Aux (d + 2)) (c : ℝ)
    (e : OpenPartialHomeomorph (Aux 2) (Aux 2))
    (he : ∀ z, e z = G.lowerCinematicJetMap hm σ c v z)
    (hea : AnalyticOnNhd ℝ e e.source)
    (ha : ∀ z ∈ e.source, AnalyticAt ℝ (fun x : ℝ × Parameters 2 d => G.γ x.1 x.2)
      (c, parameterFrame d (v + coordinateInsertion σ z)))
    {K : Set (Aux 2)} (hK : MeasurableSet K) (hKS : K ⊆ e.source)
    {β : ℝ} (hβ : 0 ≤ β)
    (hJ : ∀ z ∈ K, β ≤ |LinearMap.det (fderiv ℝ e z).toLinearMap|)
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (h : Plane → ℂ)
    (hh : Measurable h) (h1 : Integrable h) (h2 : MemLp h 2 volume)
    {ε r δ : ℝ} (hε : 0 < ε) (hr : 0 < r) (hδ : 0 < δ)
    (hgap : ∀ x : Plane, |x.2| < ε → h x = 0)
    (b : SchwartzMap (Plane × Plane) ℂ)
    (hb : ∀ y ∈ e '' K, ∀ τ η, h (c + δ * τ, η) ≠ 0 →
      b (((y 0, y 1) : Plane), (τ, η)) =
        actualTaylorAmplitude a (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1)
          1 (2 * Real.pi * r) c δ
          (parameterFrame d (v + coordinateInsertion σ (e.symm y))) τ η) :
    ENNReal.ofReal β * (∫⁻ z in K,
      ‖timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h
        (2 * Real.pi * r) c δ (parameterFrame d (v + coordinateInsertion σ z))‖ₑ ^ (2 : ℕ)) ≤
      (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) ^ (2 : ℕ) *
        (ENNReal.ofReal (ε⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ)) := by
  let g : Plane → ℂ := fun x => h (timeDataRescaling c δ x)
  have hg : Measurable g := hh.comp (by unfold timeDataRescaling; fun_prop)
  have hg1 : Integrable g := integrable_timeDataRescaling hh h1 c hδ
  have hg2 : MemLp g 2 volume := memLp_timeDataRescaling_two hh h2 c hδ
  have hggap : ∀ x : Plane, |x.2| < ε → g x = 0 := by
    intro x hx
    exact hgap _ hx
  let F : Aux 2 → ℂ := fun y => δ •
    dilatedAmplitudeConeExtension (fun w x => b (w, x)) g r δ (y 0, y 1)
  have hslice (z : Aux 2) (hz : z ∈ K) :
      timeSliceExtension (fun x : Parameters 2 d × ℝ => G.γ x.2 x.1) a h
        (2 * Real.pi * r) c δ (parameterFrame d (v + coordinateInsertion σ z)) = F (e z) := by
    have hy : e z ∈ e.target := e.map_source (hKS hz)
    have hs := G.timeSliceExtension_eq_dilatedAmplitudeConeExtension hm σ v c e he ha
      a h r hδ b hy (hb (e z) (mem_image_of_mem e hz))
    rw [e.left_inv (hKS hz)] at hs
    exact hs
  have hFnorm : Measurable (fun w : Plane =>
      ‖δ • dilatedAmplitudeConeExtension (fun w x => b (w, x)) g r δ w‖ₑ ^ (2 : ℕ)) :=
    ((stronglyMeasurable_dilatedAmplitudeConeExtension b hg r δ).const_smul δ).measurable.enorm.pow_const _
  have hFmass : (∫⁻ y : Aux 2, ‖F y‖ₑ ^ (2 : ℕ)) =
      ENNReal.ofReal (δ ^ (2 : ℕ)) *
        ∫⁻ w : Plane, ‖dilatedAmplitudeConeExtension (fun w x => b (w, x)) g r δ w‖ₑ ^ (2 : ℕ) := by
    calc
      _ = ∫⁻ w : Plane,
          ‖δ • dilatedAmplitudeConeExtension (fun w x => b (w, x)) g r δ w‖ₑ ^ (2 : ℕ) :=
        (volume_preserving_finTwoArrow ℝ).lintegral_comp hFnorm
      _ = _ := by
        simp_rw [enorm_smul, Real.enorm_eq_ofReal hδ.le, mul_pow,
          ← ENNReal.ofReal_pow hδ.le]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  calc
    _ = ENNReal.ofReal β * ∫⁻ z in K, ‖F (e z)‖ₑ ^ (2 : ℕ) := by
      congr 1
      apply setLIntegral_congr_fun hK
      intro z hz
      dsimp only
      rw [hslice z hz]
    _ ≤ ∫⁻ y in e '' K, ‖F y‖ₑ ^ (2 : ℕ) :=
      chart_lintegral_lower_bound e hea hK hKS hβ hJ _
    _ ≤ ∫⁻ y : Aux 2, ‖F y‖ₑ ^ (2 : ℕ) :=
      lintegral_mono' Measure.restrict_le_self le_rfl
    _ = _ := hFmass
    _ ≤ ENNReal.ofReal (δ ^ (2 : ℕ)) *
        ((∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) ^ (2 : ℕ) *
          (ENNReal.ofReal δ⁻¹ * (ENNReal.ofReal (ε⁻¹ * r⁻¹ ^ (2 : ℕ)) *
            ∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ)))) :=
      mul_le_mul_right (lintegral_dilatedAmplitudeConeExtension_sq_le b g hg hg1 hg2
        hε hr hδ hggap) _
    _ = _ := by
      rw [show (∫⁻ x : Plane, ‖g x‖ₑ ^ (2 : ℕ)) =
        ENNReal.ofReal δ⁻¹ * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ) from
          lintegral_timeDataRescaling_sq hh c hδ]
      calc
        _ = (ENNReal.ofReal (δ ^ (2 : ℕ)) * ENNReal.ofReal δ⁻¹ * ENNReal.ofReal δ⁻¹) *
            ((∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier b ζ‖ₑ) ^ (2 : ℕ) *
              (ENNReal.ofReal (ε⁻¹ * r⁻¹ ^ (2 : ℕ)) * ∫⁻ x : Plane, ‖h x‖ₑ ^ (2 : ℕ))) := by
          ac_rfl
        _ = _ := by rw [timeSlice_L2_scale_cancel hδ, one_mul]

end PlanarNikodym
