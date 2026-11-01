import PlanarNikodym.Analysis.Fourier.LocalComplexAmplitudeExtension
import PlanarNikodym.Analysis.Fourier.InverseChartAmplitude
import PlanarNikodym.Analysis.Fourier.LocalAmplitudeExtension

/-! Actual uniformly compact amplitudes in the fixed inverse jet chart.
A joint smooth compact extension constructs the output and vertical
frequency cutoffs; freezing the center, auxiliary parameters and scales
therefore gives one fixed four-variable amplitude family. -/
noncomputable section
open Set
open scoped ContDiff
namespace PlanarNikodym

abbrev LinearAmplitudeParameters (d : ℕ) := (ℝ × Aux (d + 2)) × Plane

def freezeLinearAmplitudeVariables {d : ℕ}
    (z : CinematicAmplitudeVariables d 1 × Plane) :
    (Plane × Plane) × LinearAmplitudeParameters d :=
  (((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) z.1.1.2, z.1.2), (z.1.1.1, z.2))

theorem continuous_freezeLinearAmplitudeVariables (d : ℕ) :
    Continuous (freezeLinearAmplitudeVariables (d := d)) := by
  unfold freezeLinearAmplitudeVariables
  fun_prop

def unscaledInverseChartAmplitude {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (Φ : Parameters 2 d × ℝ → ℝ)
    (z : (Plane × Plane) × LinearAmplitudeParameters d) : ℂ :=
  inverseChartTaylorAmplitude e σ a Φ
    ((((z.2.1, (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm z.1.1), z.1.2), z.2.2))

theorem unscaledInverseChartAmplitude_freeze {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2)) (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (Φ : Parameters 2 d × ℝ → ℝ)
    (z : CinematicAmplitudeVariables d 1 × Plane) :
    unscaledInverseChartAmplitude e σ a Φ (freezeLinearAmplitudeVariables z) =
      inverseChartTaylorAmplitude e σ a Φ z := by
  simp only [unscaledInverseChartAmplitude, freezeLinearAmplitudeVariables,
    ContinuousLinearEquiv.symm_apply_apply]

theorem contDiffAt_unscaledInverseChartAmplitude {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2)) (σ : Fin 2 ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (z : (Plane × Plane) × LinearAmplitudeParameters d)
    (hi : AnalyticAt ℝ e.symm
      (z.2.1, (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm z.1.1)) :
    ContDiffAt ℝ ∞ (unscaledInverseChartAmplitude e σ a Φ) z := by
  have harg : ContDiff ℝ ∞ (fun z : (Plane × Plane) × LinearAmplitudeParameters d =>
      (((z.2.1, (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm z.1.1), z.1.2), z.2.2)) := by
    fun_prop
  exact (contDiffAt_inverseChartTaylorAmplitude e σ ha hΦ _ hi).comp z harg.contDiffAt

theorem unscaledInverseChartAmplitude_eq_zero_of_window {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2)) (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) (Φ : Parameters 2 d × ℝ → ℝ)
    (z : (Plane × Plane) × LinearAmplitudeParameters d)
    (hw : timePartitionWindow z.1.2.1 = 0) :
    unscaledInverseChartAmplitude e σ a Φ z = 0 := by
  simp only [unscaledInverseChartAmplitude, inverseChartTaylorAmplitude,
    rescaledTaylorAmplitude, hw, Complex.ofReal_zero, mul_zero, zero_mul]

theorem unscaledInverseChartAmplitude_eq_actualTaylorAmplitude {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2)) (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) {Φ : Parameters 2 d × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ) (q : ℝ × Aux (d + 2)) (y : Aux 2) (r δ τ η : ℝ) :
    unscaledInverseChartAmplitude e σ a Φ
      (((y 0, y 1), (τ, η)), (q, (r * δ ^ (2 : ℕ), δ))) =
      actualTaylorAmplitude a Φ 1 r q.1 δ
        (parameterFrame d (q.2 + coordinateInsertion σ (e.symm (q, y)).2)) τ η := by
  have he : (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm (y 0, y 1) = y :=
    (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm_apply_apply y
  simp only [unscaledInverseChartAmplitude, inverseChartTaylorAmplitude, he]
  exact rescaledTaylorAmplitude_eq_actualTaylorAmplitude a hΦ 1 _ r q.1 δ τ η

/-- This constructs an actual globally smooth compact amplitude on all
four operator variables and all frozen parameters. Its support and jets
come from one fixed joint function, independently of the frequency. -/
theorem exists_compact_unscaled_inverseChartAmplitude_extension {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : AnalyticOnNhd ℝ e.symm e.target) (σ : Fin 2 ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hK : IsCompact K) (hKT : K ⊆ e.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ B : ((Plane × Plane) × LinearAmplitudeParameters d) → ℂ,
      ContDiff ℝ ∞ B ∧ HasCompactSupport B ∧
      (∀ q y, (q, y) ∈ K → ∀ τ : ℝ, ∀ η ∈ J, ∀ α ∈ Icc (0 : ℝ) 1,
        ∀ δ ∈ Icc (0 : ℝ) 1,
          B (((y 0, y 1), (τ, η)), (q, (α, δ))) =
            unscaledInverseChartAmplitude e σ a Φ (((y 0, y 1), (τ, η)), (q, (α, δ)))) ∧
      ∀ z, timePartitionWindow z.1.2.1 = 0 → B z = 0 := by
  let H := unscaledInverseChartAmplitude e σ a Φ
  let L : Set (CinematicAmplitudeVariables d 1 × Plane) :=
    (K ×ˢ (Icc (-1 : ℝ) 1 ×ˢ J)) ×ˢ (Icc (0 : ℝ) 1 ×ˢ Icc (0 : ℝ) 1)
  have hL : IsCompact L :=
    (hK.prod (isCompact_Icc.prod hJ)).prod (isCompact_Icc.prod isCompact_Icc)
  let S : Set ((Plane × Plane) × LinearAmplitudeParameters d) :=
    {z | (z.2.1, (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm z.1.1) ∈ e.target}
  have hS : IsOpen S := e.open_target.preimage (by fun_prop)
  have hLS : freezeLinearAmplitudeVariables '' L ⊆ S := by
    rintro _ ⟨z, hz, rfl⟩
    change (z.1.1.1, (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm
      ((ContinuousLinearEquiv.finTwoArrow ℝ ℝ) z.1.1.2)) ∈ e.target
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact hKT hz.1.1
  obtain ⟨B, N, hB, hcB, _, hLN, _, hBN, hzero⟩ :=
    exists_compact_smooth_complex_extension H
      (hL.image (continuous_freezeLinearAmplitudeVariables d)) hS hLS
      (fun z hz => contDiffAt_unscaledInverseChartAmplitude e σ ha hΦ z (hi _ hz))
  refine ⟨B, hB, hcB, ?_, fun z hz => hzero z
    (unscaledInverseChartAmplitude_eq_zero_of_window e σ a Φ z hz)⟩
  intro q y hqy τ η hη α hα δ hδ
  by_cases hτ : τ ∈ Icc (-1 : ℝ) 1
  · apply hBN
    apply hLN
    refine ⟨(((q, y), (τ, η)), (α, δ)), ⟨⟨hqy, hτ, hη⟩, hα, hδ⟩, ?_⟩
    rfl
  · have hw : timePartitionWindow τ = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hmem => hτ (tsupport_timePartitionWindow_subset hmem))
    have hz : H (((y 0, y 1), (τ, η)), (q, (α, δ))) = 0 :=
      unscaledInverseChartAmplitude_eq_zero_of_window e σ a Φ _ hw
    change B (((y 0, y 1), (τ, η)), (q, (α, δ))) =
      H (((y 0, y 1), (τ, η)), (q, (α, δ)))
    rw [hzero _ hz, hz]

end PlanarNikodym
