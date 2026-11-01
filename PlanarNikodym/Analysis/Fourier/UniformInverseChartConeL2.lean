import PlanarNikodym.Analysis.Fourier.CompactInverseChartAmplitude
import PlanarNikodym.Analysis.Fourier.CompactSmoothAmplitudeFamily
import PlanarNikodym.Analysis.Fourier.DilatedAmplitudeConeL2

/-! A constructed uniform L² constant for the actual inverse-chart
Taylor amplitudes. The frequency-dependent output dilation stays in the
phase; the amplitude family has one fixed compact support. -/
noncomputable section
open Set MeasureTheory
open scoped ContDiff ENNReal
namespace PlanarNikodym

theorem exists_uniform_inverseChart_amplitude_cone_bound {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2))
    (hi : AnalyticOnNhd ℝ e.symm e.target) (σ : Fin 2 ↪ Fin (d + 2))
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
    exists_compact_unscaled_inverseChartAmplitude_extension e hi σ ha hΦ hK hKT hJ
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

/-- At the actual critical-scale parameter `α=rδ²`, the constructed
family agrees with the complete Taylor-corrected amplitude, not merely
with a phase polynomial or a derivative bound. -/
theorem uniformInverseChart_amplitude_eq_actual {d : ℕ}
    (e : OpenPartialHomeomorph ((ℝ × Aux (d + 2)) × Aux 2)
      ((ℝ × Aux (d + 2)) × Aux 2)) (σ : Fin 2 ↪ Fin (d + 2))
    (a : Parameters 2 d × ℝ × ℝ → ℂ) {Φ : Parameters 2 d × ℝ → ℝ}
    (hΦ : ContDiff ℝ ∞ Φ)
    (S : LinearAmplitudeParameters d → SchwartzMap (Plane × Plane) ℂ)
    {K : Set ((ℝ × Aux (d + 2)) × Aux 2)} {J : Set ℝ}
    (hmatch : ∀ q y, (q, y) ∈ K → ∀ τ : ℝ, ∀ η ∈ J, ∀ α ∈ Icc (0 : ℝ) 1,
      ∀ δ ∈ Icc (0 : ℝ) 1,
        S (q, (α, δ)) ((y 0, y 1), (τ, η)) =
          unscaledInverseChartAmplitude e σ a Φ (((y 0, y 1), (τ, η)), (q, (α, δ))))
    {q : ℝ × Aux (d + 2)} {y : Aux 2} (hqy : (q, y) ∈ K)
    (r δ τ : ℝ) {η : ℝ} (hη : η ∈ J)
    (hα : r * δ ^ (2 : ℕ) ∈ Icc (0 : ℝ) 1) (hδ : δ ∈ Icc (0 : ℝ) 1) :
    S (q, (r * δ ^ (2 : ℕ), δ)) ((y 0, y 1), (τ, η)) =
      actualTaylorAmplitude a Φ 1 r q.1 δ
        (parameterFrame d (q.2 + coordinateInsertion σ (e.symm (q, y)).2)) τ η := by
  rw [hmatch q y hqy τ η hη _ hα δ hδ,
    unscaledInverseChartAmplitude_eq_actualTaylorAmplitude e σ a hΦ]

end PlanarNikodym
