import PlanarNikodym.Analysis.Fourier.UniformInverseChartConeL2

/-! Actual compact inverse-chart amplitudes and uniform Fourier/L²
constants require C∞ inverse charts alone. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem e3_contDiffAt_inverseChartTaylorAmplitude {d n : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux (n + 1))
      ((ℝ × Aux (d + 2)) × Aux (n + 1)))
    (σ : Fin (n + 1) ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (q : (CinematicAmplitudeVariables d n × (ℝ × ℝ)))
    (hi : ContDiffAt ℝ ∞ e.symm q.1.1) :
    ContDiffAt ℝ ∞ (inverseChartTaylorAmplitude e σ a Φ) q := by
  have hei : ContDiffAt ℝ ∞ (fun z :
      CinematicAmplitudeVariables d n × (ℝ × ℝ) => e.symm z.1.1) q :=
    hi.comp q contDiffAt_fst.fst
  have hp : ContDiffAt ℝ ∞ (fun z : CinematicAmplitudeVariables d n × (ℝ × ℝ) =>
      parameterFrame d (z.1.1.1.2 + coordinateInsertion σ (e.symm z.1.1).2)) q := (parameterFrame d).contDiff.contDiffAt.comp q
    (contDiffAt_fst.fst.fst.snd.add ((coordinateInsertion σ).contDiff.contDiffAt.comp q hei.snd))
  have harg : ContDiffAt ℝ ∞ (fun z : CinematicAmplitudeVariables d n × (ℝ × ℝ) =>
      (((parameterFrame d (z.1.1.1.2 + coordinateInsertion σ (e.symm z.1.1).2),
        z.1.1.1.1, z.1.2.1), z.1.2.2), z.2)) q := ((hp.prodMk (contDiffAt_fst.fst.fst.fst.prodMk contDiffAt_fst.snd.fst)).prodMk
    contDiffAt_fst.snd.snd).prodMk contDiffAt_snd
  exact (contDiff_rescaledTaylorAmplitude ha hΦ n).contDiffAt.comp q harg

theorem e3_contDiffAt_unscaledInverseChartAmplitude {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2)) (σ : Fin 2 ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    (z : (Plane × Plane) × LinearAmplitudeParameters d)
    (hi : ContDiffAt ℝ ∞ e.symm
      (z.2.1, (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm z.1.1)) :
    ContDiffAt ℝ ∞ (unscaledInverseChartAmplitude e σ a Φ) z := by
  have harg : ContDiff ℝ ∞ (fun z : (Plane × Plane) × LinearAmplitudeParameters d =>
      (((z.2.1, (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm z.1.1), z.1.2), z.2.2)) := by
    fun_prop
  exact (e3_contDiffAt_inverseChartTaylorAmplitude e σ ha hΦ _ hi).comp z harg.contDiffAt

theorem exists_e3_compact_unscaled_inverseChartAmplitude_extension {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) (σ : Fin 2 ↪ Fin (d + 2))
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
      (fun z hz => e3_contDiffAt_unscaledInverseChartAmplitude e σ ha hΦ z (hi _ hz))
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

theorem exists_e3_uniform_inverseChart_amplitude_cone_bound {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : ∀ x ∈ e.target, ContDiffAt ℝ ∞ e.symm x) (σ : Fin 2 ↪ Fin (d + 2))
    {a : Parameters 2 d × ℝ × ℝ → ℂ} (ha : ContDiff ℝ ∞ a)
    {Φ : Parameters 2 d × ℝ → ℝ} (hΦ : ContDiff ℝ ∞ Φ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} (hK : IsCompact K) (hKT : K ⊆ e.target)
    {J : Set ℝ} (hJ : IsCompact J) :
    ∃ (S : LinearAmplitudeParameters d → SchwartzMap (Plane × Plane) ℂ) (C : ℝ),
      0 ≤ C ∧
      (∀ q y, (q, y) ∈ K → ∀ τ : ℝ, ∀ η ∈ J, ∀ α ∈ Icc (0 : ℝ) 1,
        ∀ δ ∈ Icc (0 : ℝ) 1,
          S (q, (α, δ)) ((y 0, y 1), (τ, η)) =
            unscaledInverseChartAmplitude e σ a Φ (((y 0, y 1), (τ, η)), (q, (α, δ)))) ∧
      (∀ p w x, timePartitionWindow x.1 = 0 → S p (w, x) = 0) ∧
      (∀ p, (∫⁻ ζ : AmplitudeFourierSpace, ‖jointAmplitudeFourier (S p) ζ‖ₑ) ≤
        ENNReal.ofReal C) ∧
      ∀ p (h : Plane → ℂ), Measurable h → Integrable h → MemLp h 2 volume →
        ∀ κ r δ : ℝ, 0 < κ → 0 < r → 0 < δ →
        (∀ x : Plane, |x.2| < κ → h x = 0) →
        eLpNorm (dilatedAmplitudeConeExtension (fun w x => S p (w, x)) h r δ) 2 volume ≤
          ENNReal.ofReal C * ENNReal.ofReal δ⁻¹ ^ (1 / (2 : ℝ)) *
            ENNReal.ofReal (κ⁻¹ * r⁻¹ ^ (2 : ℕ)) ^ (1 / (2 : ℝ)) * eLpNorm h 2 volume := by
  obtain ⟨B, hB, hcB, hmatch, hzero⟩ :=
    exists_e3_compact_unscaled_inverseChartAmplitude_extension e hi σ ha hΦ hK hKT hJ
  let S := compactSmoothAmplitudeFamily B hB hcB
  obtain ⟨hSupp, hS, hjet⟩ := compactSmoothAmplitudeFamily_uniform_support_and_jets B hB hcB
  obtain ⟨C, hC, hcoef⟩ := exists_uniform_jointAmplitudeFourier_L1_bound S hSupp hS hjet
  refine ⟨S, C, hC, ?_, ?_, hcoef, ?_⟩
  · intro q y hqy τ η hη α hα δ hδ
    exact hmatch q y hqy τ η hη α hα δ hδ
  · intro p w x hx
    exact hzero ((w, x), p) hx
  · intro p h hh h1 h2 κ r δ hκ hr hδ hgap
    exact (eLpNorm_dilatedAmplitudeConeExtension_two_le (S p) h hh h1 h2 hκ hr hδ hgap).trans
      (by gcongr; exact hcoef p)

end PlanarNikodym
